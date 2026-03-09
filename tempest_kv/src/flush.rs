use std::sync::Arc;

use tempest_core::fio::FioFS;

use crate::{
    Storage,
    base::{Comparer, StorageResult},
    manifest::{ManifestRequest, SstMetadata},
    memtable::MemTable,
    sst::{get_sst_path, writer::SstWriter},
};

impl<F: FioFS, C: Comparer> Storage<F, C> {
    pub(crate) fn maybe_freeze(&mut self) {
        if self.active.approximate_size() >= self.config.memtable.size_threshold {
            self.freeze_current_memtable();
        }
    }

    fn freeze_current_memtable(&mut self) {
        let frozen = std::mem::replace(&mut self.active, MemTable::new(self.wal.filenum()));
        self.immutables.insert(0, Arc::new(frozen));
    }

    /// Flush all immutables to disk, if there are any, and also maybe compact the SSTs.
    pub(crate) async fn maybe_flush(&mut self) -> StorageResult<()> {
        while !self.immutables.is_empty() {
            self.flush_oldest_immutable().await?;
        }
        self.maybe_compact().await?;
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

        let filenum = self.manifest.get_filenums(1).await?.start;
        let level = 0;

        let sst_path = get_sst_path(&self.root_dir, filenum);
        debug!(filenum, ?sst_path, "determined filenum");
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
        let stats = writer.finalize().await?;

        let metadata = SstMetadata {
            filenum,
            level,
            stats,
        };

        // TODO: be more flexible here, and allow for the immutables to stay in memory for a while
        // to make reads of hot data more efficient.
        self.immutables.pop();
        trace!(?metadata, "finished flushing memtable to sst");

        let min_remaining = self
            .immutables
            .iter()
            .map(|imm| imm.wal_filenum())
            .min()
            // NB: `active.wal_filenum()` is always greater than `imm.wal_filenum()`.
            .unwrap_or(self.active.wal_filenum());

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

    /// Test only helper that forces the current active memtable to be frozen to the immutables.
    #[cfg(test)]
    pub(crate) fn test_force_freeze(&mut self) {
        debug!("force freezing current memtable");
        self.freeze_current_memtable();
    }
}
