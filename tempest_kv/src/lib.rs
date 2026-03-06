//! # Silo Module
//!
//! This module contains the code for our **storage silos**.
//!
//! ## What are silos
//!
//! Tempest is designed with the shared-nothing approach, where we try to avoid having any
//! resources requiring multi-thread synchronization primitives. This improves overall
//! **performance** and allows us to utilize certain Linux kernel features, such as **io_uring**,
//! which is bound to be used on one thread by implementation, i.e. most types are !Send.

use std::{path::PathBuf, sync::Arc, thread};

use crate::{
    base::{
        Comparer, DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum, StorageError,
        StorageResult,
    },
    batch::WriteBatch,
    config::SiloConfig,
    iterator::{DeduplicatingIterator, MergingIterator, MergingIteratorHeapEntry, SyncIterator},
    manifest::{ManifestRequest, StorageManifest, SstMetadata, get_sst_path},
    memtable::MemTable,
    sst::{reader::SstReader, writer::SstWriter},
    wal::SiloWal,
};

use bytes::{Buf, Bytes};
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

#[cfg(test)]
mod tests;

#[derive(Debug)]
pub struct Silo<F: FioFS, C: Comparer = DefaultComparer> {
    /// The ID of this silo.
    id: u64,
    /// The root directory for this silo.
    root_dir: PathBuf,
    /// The file system that is backing this silo.
    fs: F,

    /// The manifest that manages state of this silo.
    manifest: StorageManifest<F>,

    /// The write-ahead log that ensure durability of writes to this silo.
    wal: SiloWal<F>,

    /// The currently active memtable.
    active: MemTable<C>,
    /// The immutable memtables.
    immutables: Vec<Arc<MemTable<C>>>,

    /// This is `true`, when [`shutdown`] has been called.
    ///
    /// [`shutdown`]: Self::shutdown
    is_shutdown: bool,

    config: SiloConfig,
}

fn read_varint(src: &[u8]) -> Option<(usize, usize)> {
    usize::decode_var(src)
}

impl<F: FioFS, C: Comparer> Silo<F, C> {
    pub(crate) async fn init(
        id: u64,
        fs: F,
        root_dir: impl Into<PathBuf>,
        config: SiloConfig,
    ) -> StorageResult<Self> {
        info!(?config, "initializing silo");
        let root_dir = root_dir.into();

        // initialize manifest
        let mut manifest =
            StorageManifest::init(fs.clone(), root_dir.clone(), config.manifest.clone()).await?;

        // allocate filenums for other components
        let filenum_range = manifest.get_filenums(1).await?;
        let mut filenums = filenum_range.into_iter();

        // initialize wal
        let (wal, mut recovery_reader) = SiloWal::init(
            fs.clone(),
            root_dir.clone(),
            filenums.next().unwrap(),
            manifest.wal_filenums(),
            config.wal.clone(),
        )
        .await?;

        let smallest_wal_filenum = manifest
            .wal_filenums()
            .iter()
            .min()
            .copied()
            .unwrap_or_else(|| wal.current_filenum());

        // initialize memtables
        let active = MemTable::new(smallest_wal_filenum);
        let immutables = Vec::new();

        let mut silo = Self {
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

        while let Some(res) = recovery_reader.next().await {
            // skip over errors
            let data = match res {
                Ok(d) => d,
                Err(e) => {
                    warn!("could not recover record from wal: {}, skipping", e);
                    continue;
                }
            };

            let batch_seqnum = WriteBatch::seqnum(&data)?;
            if batch_seqnum <= silo.manifest.max_flushed_seqnum() {
                trace!(
                    ?batch_seqnum,
                    "skipping already flushed batch during recovery"
                );
                continue;
            }

            silo.apply_batch_to_memtable(data.freeze())?;
        }

        info!("finished initializing silo");
        Ok(silo)
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

        // TODO: Implement wal rotation
        //
        //match wal_status {
        //    WalStatus::Ok => {},
        //    WalStatus::NeedsRotation => self.wal.rotate(),
        //}

        self.maybe_freeze();
        self.maybe_flush().await?;

        Ok(())
    }

    fn apply_batch_to_memtable(&mut self, mut body: Bytes) -> StorageResult<()> {
        let header = body.split_to(12);

        let seqnum_raw = u64::from_le_bytes(header[0..8].try_into().unwrap());
        let seqnum = seqnum_raw.try_into()?;

        let count = u32::from_le_bytes(header[8..12].try_into().unwrap());

        // TODO: verify remaining length along the way, to prevent panics if batch is malformed
        let mut pairs: Vec<(KeyKind, Bytes, Bytes)> = Vec::new();
        for idx in 0..count {
            trace!(idx, "reading entry");

            // get kind
            let kind_byte = body.split_to(1)[0];
            let kind: KeyKind = kind_byte.try_into()?;

            // get key length varint
            let (key_len, varint_bytes_read) =
                read_varint(&body[..]).ok_or(StorageError::InvalidVarint)?;
            body.advance(varint_bytes_read);

            // get key
            let key = body.split_to(key_len);
            trace!(?kind, key_len, ?key, idx, "got key");

            match kind {
                KeyKind::Delete => {
                    pairs.push((kind, key, Bytes::new()));
                }
                KeyKind::Put => {
                    // get value length varint
                    let (value_len, varint_bytes_read) =
                        read_varint(&body[..]).ok_or(StorageError::InvalidVarint)?;
                    body.advance(varint_bytes_read);

                    // get value
                    let value = body.split_to(value_len);
                    trace!(value_len, ?value, idx, "got value");

                    pairs.push((kind, key, value));
                }
            }
        }

        for (kind, key, value) in pairs {
            let trailer = KeyTrailer::new(seqnum, kind);
            let key = InternalKey::new(key, trailer);
            self.active.insert(key, value);
        }

        Ok(())
    }

    fn maybe_freeze(&mut self) {
        if self.active.approximate_size() >= self.config.memtable.size_threshold {
            self.freeze_current_memtable();
        }
    }

    fn freeze_current_memtable(&mut self) {
        let frozen = std::mem::replace(&mut self.active, MemTable::new(self.wal.current_filenum()));
        self.immutables.insert(0, Arc::new(frozen));
    }

    async fn maybe_flush(&mut self) -> StorageResult<()> {
        while !self.immutables.is_empty() {
            self.flush_oldest_immutable().await?;
        }
        Ok(())
    }

    #[instrument(skip_all)]
    async fn flush_oldest_immutable(&mut self) -> StorageResult<()> {
        let imm = self.immutables.last().expect("checked by caller");

        let entry_count = imm.len();
        let min_key = imm.min_key().expect("non-empty immutable").key().clone();
        let max_key = imm.max_key().expect("non-empty immutable").key().clone();
        let min_seqnum = imm.min_seqnum().expect("non-empty immutable");
        let max_seqnum = imm.max_seqnum().expect("non-empty immutable");
        debug!(
            entry_count,
            ?min_key,
            ?max_key,
            ?min_seqnum,
            ?max_seqnum,
            "flushing oldest memtable to sst"
        );

        let filenum_range = self.manifest.get_filenums(1).await?;
        let filenum = filenum_range.start;
        let level = 0;

        let sst_path = get_sst_path(&self.root_dir, level, filenum);
        debug!(filenum, ?sst_path, "determined filenum");
        self.fs.create_dir_all(sst_path.parent().unwrap()).await?;
        let file = self
            .fs
            .opts()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&sst_path)
            .await?;

        let mut writer = SstWriter::<_, C>::new(file, entry_count, self.config.sst.clone());
        writer.extend_from_collection(imm.iter()).await?;
        let file_size = writer.finalize().await?;

        let metadata = SstMetadata {
            filenum,
            file_size,
            level,
            min_key,
            max_key,
            min_seqnum,
            max_seqnum,
        };

        self.immutables.pop();
        trace!(?metadata, "finished flushing memtable to sst");

        let min_remaining = self
            .immutables
            .iter()
            .map(|imm| imm.wal_filenum())
            .min()
            .unwrap_or(self.active.wal_filenum())
            // TODO: is active.wal_filenum() always greater than imm.wal_filenum()? -> omit this
            .min(self.active.wal_filenum());

        let filenums_to_remove: Vec<_> = self
            .manifest
            .wal_filenums()
            .iter()
            .copied()
            .filter(|&f| f < min_remaining)
            .collect();

        trace!(?filenums_to_remove, "removing unused wals from manifest");
        self.manifest
            .handle_request(
                ManifestRequest::new()
                    .with_ssts_added([metadata])
                    .with_wal_filenums_removed(filenums_to_remove),
            )
            .await?;

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
            let path = get_sst_path(&self.root_dir, sst_meta.level, sst_meta.filenum);
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
            let path = get_sst_path(&self.root_dir, sst_meta.level, sst_meta.filenum);
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

    /// Test only helper that forces the current active memtable to be frozen to the immutables.
    #[cfg(test)]
    fn test_force_freeze(&mut self) {
        debug!("force freezing current memtable");
        self.freeze_current_memtable();
    }
}

impl<F: FioFS, C: Comparer> Drop for Silo<F, C> {
    fn drop(&mut self) {
        if !self.is_shutdown {
            error!(id = self.id, "silo was not shut down correctly!");
        }
    }
}

pub struct SiloHandle {
    sender: mpsc::Sender<SiloCommand>,
}

impl SiloHandle {
    pub async fn write(&self, batch: WriteBatch) -> StorageResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(SiloCommand::Write {
                batch,
                respond_to: tx,
            })
            .await?;
        rx.await?
    }

    pub(crate) async fn shutdown(&self) -> StorageResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(SiloCommand::Shutdown { respond_to: tx })
            .await?;
        rx.await?
    }
}

#[derive(Debug)]
pub enum SiloCommand {
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

/// A background worker that can be controlled through channel commands and manages a [`Silo`].
pub struct SiloWorker<F: FioFS, C: Comparer> {
    silo: Silo<F, C>,
    receiver: mpsc::Receiver<SiloCommand>,
}

impl<F: FioFS, C: Comparer> SiloWorker<F, C> {
    /// Creates a silo worker that initializes and manages a [`Silo`] within the `root_dir`.
    pub fn spawn_worker(
        id: u64,
        fs: F,
        root_dir: impl Into<PathBuf>,
        config: SiloConfig,
    ) -> SiloHandle {
        let root_dir = root_dir.into();
        let silo_dir = root_dir.join(format!("silo-{}", id));
        let (sender, receiver) = mpsc::channel(1024);

        thread::spawn(move || {
            let _worker_entered = span!(Level::INFO, "silo-worker", id).entered();
            info!(id, ?root_dir, "spawning silo worker");
            // Specify core affinity for this worker
            core_affinity::set_for_current(core_affinity::CoreId { id: id as usize });

            let result = tokio_uring::start(async move {
                info!(id, "initialized tokio-uring runtime");
                let silo = Silo::<F, C>::init(id, fs, silo_dir, config).await?;
                let mut worker = SiloWorker { silo, receiver };
                worker.start().await;

                Ok::<_, StorageError>(())
            });
            if let Err(err) = result {
                error!("silo worker crashed: {}", err);
            }
        });

        SiloHandle { sender }
    }

    async fn start(&mut self) {
        info!("starting silo worker");
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

        let result = self.silo.shutdown().await;
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
    async fn handle_command(&mut self, cmd: SiloCommand) -> StorageResult<CommandControlFlow> {
        match cmd {
            SiloCommand::Write { batch, respond_to } => {
                let result = self.silo.write(batch).await;
                if let Err(e) = result.as_ref() {
                    error!("failed to execute write command: {}", e);
                }
                if let Err(_) = respond_to.send(result) {
                    error!("could not respond to write command: channel closed");
                }
                Ok(CommandControlFlow::Continue)
            }
            SiloCommand::Scan {} => todo!(),
            SiloCommand::Shutdown { respond_to } => Ok(CommandControlFlow::Shutdown { respond_to }),
        }
    }
}
