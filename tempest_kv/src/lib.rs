use std::{path::PathBuf, sync::Arc};

use crate::{
    base::{Comparer, DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum, StorageResult},
    batch::WriteBatch,
    config::StorageConfig,
    iterator::{
        DeduplicatingIterator, MergingIterator, MergingIteratorHeapEntry, SnapshotIterator,
        SyncIterator,
    },
    manifest::{ManifestRequest, StorageManifest},
    memtable::MemTable,
    sst::{SST_DIR, get_sst_path, reader::SstReader},
    wal::{Wal, WalStatus},
};

use bytes::Bytes;
use integer_encoding::VarInt;
use tempest_core::fio::FioFS;
use tracing::instrument;

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
pub mod worker;

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
    pub async fn init(
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
        snapshot: SeqNum,
    ) -> StorageResult<DeduplicatingIterator<'_, SnapshotIterator<'_, MergingIterator<'_, C>, C>, C>>
    {
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

        Ok(DeduplicatingIterator::new(SnapshotIterator::new(
            MergingIterator::new(sources),
            snapshot,
        )))
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
