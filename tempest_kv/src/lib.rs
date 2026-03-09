use std::{path::PathBuf, sync::Arc, thread};

use crate::{
    base::{
        Comparer, DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum, StorageError,
        StorageResult,
    },
    batch::WriteBatch,
    config::StorageConfig,
    iterator::{DeduplicatingIterator, MergingIterator, MergingIteratorHeapEntry, SyncIterator},
    manifest::{ManifestRequest, StorageManifest},
    memtable::MemTable,
    sst::{SST_DIR, get_sst_path, reader::SstReader},
    wal::{Wal, WalStatus},
};

use bytes::Bytes;
use integer_encoding::VarInt;
use tempest_core::fio::FioFS;
use tokio::sync::{mpsc, oneshot};
use tracing::{Level, instrument};

#[macro_use]
extern crate derive_more;

#[macro_use]
extern crate tracing;

pub mod base;
pub mod batch;
pub mod config;
pub mod iterator;
pub mod manifest;
pub mod memtable;
pub mod sst;
pub mod wal;

mod compaction;
mod file_gc;
mod flush;
mod recovery;

#[cfg(test)]
mod tests;

#[derive(Debug)]
pub struct Storage<F: FioFS, C: Comparer = DefaultComparer> {
    /// The ID of this storage.
    id: u64,
    /// The root directory for this storage.
    root_dir: PathBuf,
    /// The file system that is backing this storage.
    fs: F,

    /// The manifest that manages state of this storage.
    manifest: StorageManifest<F>,

    /// The write-ahead log that ensure durability of writes to this storage.
    wal: Wal<F>,

    /// The currently active memtable.
    active: MemTable<C>,
    /// The immutable memtables.
    immutables: Vec<Arc<MemTable<C>>>,

    /// This is `true`, when [`shutdown`] has been called.
    ///
    /// [`shutdown`]: Self::shutdown
    is_shutdown: bool,

    config: StorageConfig,
}

fn read_varint(src: &[u8]) -> Option<(usize, usize)> {
    usize::decode_var(src)
}

impl<F: FioFS, C: Comparer> Storage<F, C> {
    #[instrument(skip(fs, root_dir), level = "info")]
    pub(crate) async fn init(
        id: u64,
        fs: F,
        root_dir: impl Into<PathBuf>,
        config: StorageConfig,
    ) -> StorageResult<Self> {
        info!(?config, "initializing storage");
        let root_dir = root_dir.into();
        fs.create_dir_all(&root_dir.join(SST_DIR)).await?;

        // initialize manifest
        let mut manifest =
            StorageManifest::init(fs.clone(), root_dir.clone(), config.manifest.clone()).await?;

        // allocate filenums for other components
        let filenum_range = manifest.get_filenums(1).await?;
        let wal_filenum = filenum_range.start;

        // initialize write-ahead log
        let (wal, recovery_reader) = Wal::init(
            fs.clone(),
            root_dir.clone(),
            wal_filenum,
            manifest.wal_filenums(),
            config.wal.clone(),
        )
        .await?;

        // NB: register wal into manifest *after* initializing, not before. the recovery reader
        // must not know about itself yet, before the new wal file is created.
        manifest
            .handle_request(ManifestRequest::new().with_wal_filenums_added([wal_filenum]))
            .await?;

        let smallest_wal_filenum = manifest.min_wal_filenum().unwrap_or(wal.filenum());

        // initialize memtables
        let active = MemTable::new(smallest_wal_filenum);
        let immutables = Vec::new();

        let mut storage = Self {
            id,
            root_dir,
            fs,

            // -- manager components --
            manifest,
            wal,

            active,
            immutables,

            is_shutdown: false,

            config,
        };

        storage.replay_wal(recovery_reader).await?;

        // do file gc on orphaned files that may be created during uncontrolled shutdowns
        let orphans = storage.collect_sst_orphans().await?;
        storage.spawn_file_gc(orphans);

        info!("finished initializing storage");
        Ok(storage)
    }

    async fn get_seqnum(&mut self) -> StorageResult<SeqNum> {
        let range = self.manifest.get_seqnums(1).await?;
        Ok(range.start)
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn write(&mut self, mut batch: WriteBatch) -> StorageResult<()> {
        trace!("writing batch: {:?}", batch);
        let seqnum = self.get_seqnum().await?;
        batch.commit(seqnum);
        trace!(?seqnum, "batch stamped with seqnum");
        let body = batch.take_buf().freeze();

        // -- persist in wal --
        trace!("persisting batch in wal");
        let flush_required = self.wal.append(body.clone()).await?;
        let wal_status = self.wal.flush(flush_required).await?;

        // -- commit to memtable --
        // TODO: unwrap here? check validity first? maybe this is fine
        self.apply_batch_to_memtable(body)?;

        // -- rotate wal if needed --
        match wal_status {
            WalStatus::Ok => {}
            WalStatus::NeedsRotation => {
                let filenum = self.manifest.get_filenums(1).await?.start;
                self.manifest
                    .handle_request(ManifestRequest::new().with_wal_filenums_added([filenum]))
                    .await?;
                self.wal.rotate(filenum).await?;
                let wal_orphans = self.collect_wal_orphans().await?;
                self.spawn_file_gc(wal_orphans);
            }
        }

        // -- freeze an flush memtables --
        self.maybe_freeze();
        self.maybe_flush().await?;

        Ok(())
    }

    #[instrument(skip(self), level = "debug")]
    pub(crate) async fn get(&self, key: &Bytes, snapshot: SeqNum) -> StorageResult<Option<Bytes>> {
        debug!("checking active memtable");
        if let Some(active_result) = self.active.get(&key, snapshot) {
            return Ok(Some(active_result));
        }
        debug!("not found in active memtable");

        debug!("checking immutable memtables");
        for imm in &self.immutables {
            if let Some(imm_result) = imm.get(&key, snapshot) {
                return Ok(Some(imm_result));
            }
        }
        debug!("not found in immutable memtables");

        debug!("checking ssts");
        let search_key = InternalKey::new(key.as_ref(), KeyTrailer::new(snapshot, KeyKind::MAX));
        for sst_meta in self.manifest.ssts() {
            let path = get_sst_path(&self.root_dir, sst_meta.filenum);
            let file = self.fs.opts().read(true).open(&path).await?;
            let reader = SstReader::<_, C>::open(file).await?;
            if let Some(value) = reader.get(&search_key).await? {
                return Ok(Some(value));
            }
        }
        debug!("not found");
        Ok(None)
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn scan(
        &self,
    ) -> StorageResult<DeduplicatingIterator<'_, MergingIterator<'_, C>, C>> {
        let mut sources = Vec::new();

        // -- pull from active memtable --
        sources.push(MergingIteratorHeapEntry::new(
            SyncIterator::new(self.active.iter()),
            u64::MAX,
        ));

        // -- pull from immutable memtables --
        for (idx, imm) in self.immutables.iter().enumerate() {
            sources.push(MergingIteratorHeapEntry::new(
                SyncIterator::new(imm.iter()),
                u64::MAX - (idx as u64 + 1),
            ));
        }

        // -- pull from ssts --
        for sst_meta in self.manifest.ssts() {
            let path = get_sst_path(&self.root_dir, sst_meta.filenum);
            let file = self.fs.opts().read(true).open(&path).await?;
            let reader = SstReader::<_, C>::open(file).await?;
            sources.push(MergingIteratorHeapEntry::new(
                reader.iter(),
                sst_meta.filenum,
            ));
        }

        Ok(DeduplicatingIterator::new(MergingIterator::new(sources)))
    }

    pub(crate) const fn highest_seqnum(&self) -> SeqNum {
        // SAFETY:`manifest.seqnum_current()` returns a value between SeqNum::START..=SEQNUM::MAX.
        // This means, that subtracting `1` will at most end up at SeqNum::MIN (START-1)
        unsafe { SeqNum::new_unchecked(self.manifest.seqnum_current().get() - 1) }
    }

    #[instrument(skip_all)]
    pub async fn shutdown(&mut self) -> StorageResult<()> {
        assert!(!self.is_shutdown);
        // NB: Set this to true, even if this function may return an error,
        // since we may shut down partially, which means we don't want to call shutdown again,
        // even though it did not complete the process
        self.is_shutdown = true;

        // shutdown manifest, to free unused seqnums
        self.manifest.shutdown().await?;
        info!("shut down manifest");

        Ok(())
    }
}

impl<F: FioFS, C: Comparer> Drop for Storage<F, C> {
    fn drop(&mut self) {
        if !self.is_shutdown {
            error!(id = self.id, "storage was not shut down correctly!");
        }
    }
}

pub struct StorageHandle {
    sender: mpsc::Sender<StorageCommand>,
}

impl StorageHandle {
    pub async fn write(&self, batch: WriteBatch) -> StorageResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(StorageCommand::Write {
                batch,
                respond_to: tx,
            })
            .await?;
        rx.await?
    }

    pub(crate) async fn shutdown(&self) -> StorageResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(StorageCommand::Shutdown { respond_to: tx })
            .await?;
        rx.await?
    }
}

#[derive(Debug)]
pub enum StorageCommand {
    Write {
        batch: WriteBatch,
        respond_to: oneshot::Sender<StorageResult<()>>,
    },
    Scan {},
    Shutdown {
        respond_to: oneshot::Sender<StorageResult<()>>,
    },
}

#[derive(Debug)]
pub enum CommandControlFlow {
    Continue,
    Shutdown {
        respond_to: oneshot::Sender<StorageResult<()>>,
    },
}

/// A background worker that can be controlled through channel commands and manages a [`Storage`].
pub struct StorageWorker<F: FioFS, C: Comparer> {
    storage: Storage<F, C>,
    receiver: mpsc::Receiver<StorageCommand>,
}

impl<F: FioFS, C: Comparer> StorageWorker<F, C> {
    /// Creates a storage worker that initializes and manages a [`Storage`] within the `root_dir`.
    pub fn spawn_worker(
        id: u64,
        fs: F,
        root_dir: impl Into<PathBuf>,
        config: StorageConfig,
    ) -> StorageHandle {
        let root_dir = root_dir.into();
        let storage_dir = root_dir.join(format!("storage-{}", id));
        let (sender, receiver) = mpsc::channel(1024);

        thread::spawn(move || {
            let _worker_entered = span!(Level::INFO, "storage-worker", id).entered();
            info!(id, ?root_dir, "spawning storage worker");
            // Specify core affinity for this worker
            core_affinity::set_for_current(core_affinity::CoreId { id: id as usize });

            let result = tokio_uring::start(async move {
                info!(id, "initialized tokio-uring runtime");
                let storage = Storage::<F, C>::init(id, fs, storage_dir, config).await?;
                let mut worker = StorageWorker { storage, receiver };
                worker.start().await;

                Ok::<_, StorageError>(())
            });
            if let Err(err) = result {
                error!("storage worker crashed: {}", err);
            }
        });

        StorageHandle { sender }
    }

    async fn start(&mut self) {
        info!("starting storage worker");
        let respond_to = loop {
            let control_flow = match self.receiver.recv().await {
                Some(cmd) => match self.handle_command(cmd).await {
                    Ok(cf) => cf,
                    Err(err) => {
                        error!("could not handle command: {}", err);
                        break None;
                    }
                },
                None => {
                    info!("channel closed. exiting");
                    break None;
                }
            };

            match control_flow {
                CommandControlFlow::Continue => continue,
                CommandControlFlow::Shutdown { respond_to } => {
                    info!("shutdown has been requested");
                    break Some(respond_to);
                }
            }
        };

        let result = self.storage.shutdown().await;
        if let Some(tx) = respond_to {
            if let Err(_) = tx.send(result) {
                error!("could not send shutdown confirmation: channel closed");
            }
        } else {
            match result {
                Ok(()) => info!("successfully shut down."),
                Err(err) => error!("could not shut down correctly: {}", err),
            }
        }
    }

    #[instrument(skip_all)]
    async fn handle_command(&mut self, cmd: StorageCommand) -> StorageResult<CommandControlFlow> {
        match cmd {
            StorageCommand::Write { batch, respond_to } => {
                let result = self.storage.write(batch).await;
                if let Err(e) = result.as_ref() {
                    error!("failed to execute write command: {}", e);
                }
                if let Err(_) = respond_to.send(result) {
                    error!("could not respond to write command: channel closed");
                }
                Ok(CommandControlFlow::Continue)
            }
            StorageCommand::Scan {} => todo!(),
            StorageCommand::Shutdown { respond_to } => {
                Ok(CommandControlFlow::Shutdown { respond_to })
            }
        }
    }
}
