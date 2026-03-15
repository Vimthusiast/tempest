use std::{
    collections::HashSet,
    path::PathBuf,
};

use serde::{Deserialize, Serialize};
use tempest_core::{
    fio::FioFS,
    journal::{Journal, Replayable},
};

use crate::{
    base::{SeqNum, StorageError, StorageResult},
    config::ManifestConfig,
    sst::writer::SstWriterStats,
};

#[cfg(test)]
mod tests;

/// # SST Metadata
///
/// Stores the metadata for one sorted string table within Tempest.
/// The path format is **`/{silo_root}/ssts/l-{level}/{filenum}.sst`**,
/// which can be obtained simply through the [`get_path`] method.
///
/// [`get_path`]: Self::get_path
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SstMetadata {
    pub(crate) filenum: u64,
    // TODO: leveled compaction strategy
    pub(crate) level: u8,
    pub(crate) stats: SstWriterStats,
}

#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct SstDeletion {
    pub(crate) filenum: u64,
}

impl SstDeletion {
    pub(crate) fn new(filenum: u64) -> Self {
        Self { filenum }
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
#[debug("ManifestEditV1(seqnum_limit={} filenum_limit={} ssts_added={} ssts_removed={})",
    seqnum_limit.map(|v| v.get()).unwrap_or(0),
    filenum_limit.unwrap_or(0),
    ssts_added.as_ref().map(|v| v.len()).unwrap_or(0),
    ssts_removed.as_ref().map(|v| v.len()).unwrap_or(0),
)]
pub(crate) struct ManifestEditV1 {
    pub(crate) seqnum_limit: Option<SeqNum>,
    pub(crate) filenum_limit: Option<u64>,

    /// A list of new [`SstMetadata`] objects that register SST files to the [`StorageManifest`].
    pub(crate) ssts_added: Option<Vec<SstMetadata>>,

    /// A list of removed [`SstMetadata`] objects, identified by their level and file ID,
    /// that register SST files to the [`StorageManifest`].
    pub(crate) ssts_removed: Option<Vec<SstDeletion>>,

    pub(crate) wal_filenums_added: Option<Vec<u64>>,
    pub(crate) wal_filenums_removed: Option<Vec<u64>>,
}

/// A versioned edit to the [`StorageManifest`].
#[repr(u16)]
#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum ManifestEdit {
    #[debug("{:?}", _0)]
    V1(ManifestEditV1) = 1,
}

impl ManifestEdit {
    pub(crate) fn into_latest(self) -> ManifestEditV1 {
        match self {
            Self::V1(edit) => edit,
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct ManifestRequest {
    pub ssts_added: Vec<SstMetadata>,
    pub ssts_removed: Vec<SstDeletion>,
    pub wal_filenums_added: Vec<u64>,
    pub wal_filenums_removed: Vec<u64>,
    pub seqnums_needed: u64,
    pub filenums_needed: u64,
}

impl ManifestRequest {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_ssts_added(mut self, ssts: impl IntoIterator<Item = SstMetadata>) -> Self {
        self.ssts_added.extend(ssts);
        self
    }

    pub fn with_ssts_removed(mut self, ssts: impl IntoIterator<Item = SstDeletion>) -> Self {
        self.ssts_removed.extend(ssts);
        self
    }

    pub fn with_wal_filenums_added(mut self, ssts: impl IntoIterator<Item = u64>) -> Self {
        self.wal_filenums_added.extend(ssts);
        self
    }

    pub fn with_wal_filenums_removed(mut self, ssts: impl IntoIterator<Item = u64>) -> Self {
        self.wal_filenums_removed.extend(ssts);
        self
    }

    pub fn with_seqnums_needed(mut self, n: u64) -> Self {
        self.seqnums_needed += n;
        self
    }

    pub fn with_filenums_needed(mut self, n: u64) -> Self {
        self.filenums_needed += n;
        self
    }
}

#[derive(Debug)]
#[debug(
    "ManifestResponse(seqnums=[{}..{}] filenums=[{}..{}])",
    seqnum_range.start.get(), seqnum_range.end.get(), filenum_range.start, filenum_range.end,
)]
pub(crate) struct ManifestResponse {
    pub seqnum_range: std::ops::Range<SeqNum>,
    pub filenum_range: std::ops::Range<u64>,
}

#[derive(Debug, Default)]
pub(crate) struct ManifestState {
    seqnum_limit: SeqNum,
    filenum_limit: u64,
    ssts: Vec<SstMetadata>,
    wal_filenums: Vec<u64>,
}

impl Replayable for ManifestState {
    type Edit = ManifestEdit;

    fn apply(&mut self, edit: Self::Edit) {
        let edit = edit.into_latest();
        if let Some(sl) = edit.seqnum_limit {
            self.seqnum_limit = sl;
        }

        if let Some(fl) = edit.filenum_limit {
            self.filenum_limit = fl;
        }

        if let Some(added) = edit.ssts_added {
            self.ssts.extend(added);
        }

        if let Some(removed) = edit.ssts_removed {
            let delset: HashSet<_> = removed.into_iter().map(|d| d.filenum).collect();
            self.ssts.retain(|m| !delset.contains(&m.filenum));
        }

        if let Some(added) = edit.wal_filenums_added {
            self.wal_filenums.extend(added);
        }

        if let Some(removed) = edit.wal_filenums_removed {
            let delset: HashSet<_> = removed.into_iter().collect();
            self.wal_filenums.retain(|n| !delset.contains(&n));
        }
    }

    fn snapshot(&self) -> Self::Edit {
        ManifestEdit::V1(ManifestEditV1 {
            seqnum_limit: Some(self.seqnum_limit),
            filenum_limit: Some(self.filenum_limit),
            ssts_added: Some(self.ssts.clone()),
            wal_filenums_added: Some(self.wal_filenums.clone()),
            ..Default::default()
        })
    }

    fn filename_prefix() -> &'static str {
        "manifest"
    }

    fn initial() -> Self {
        Default::default()
    }
}

/// Manages reads and writes to the manifest.
#[derive(Debug)]
pub(crate) struct StorageManifest<F: FioFS> {
    /// The root path of the storage this manifest belongs to.
    silo_root: PathBuf,

    /// Next sequence number that will be used for a range allocation.
    seqnum_current: SeqNum,
    /// Next file number that will be used for a range allocation.
    filenum_current: u64,

    journal: Journal<ManifestState, F>,

    /// This is `true`, when [`shutdown`] was called.
    ///
    /// [`shutdown`]: Self::shutdown
    is_shutdown: bool,

    config: ManifestConfig,
}

impl<F: FioFS> StorageManifest<F> {
    #[instrument(skip_all, level = "info")]
    pub(crate) async fn init(
        fs: F,
        silo_root: PathBuf,
        config: ManifestConfig,
    ) -> StorageResult<Self> {
        info!("initializing manifest at {:?}", silo_root);
        let manifest_dir = silo_root.join("manifest");
        fs.create_dir_all(&manifest_dir).await?;

        let journal =
            Journal::<ManifestState, _>::open(fs, manifest_dir, config.journal_config()).await?;

        info!(state=?journal.state(), "finished initializing manifest");
        Ok(Self {
            silo_root,
            seqnum_current: journal.seqnum_limit,
            filenum_current: journal.filenum_limit,
            journal,
            is_shutdown: false,
            config,
        })
    }

    pub(crate) async fn shutdown(&mut self) -> StorageResult<()> {
        assert!(!self.is_shutdown, "manifest has been shut down");

        // tighten down seqnum and filenum limit
        let final_edit = ManifestEdit::V1(ManifestEditV1 {
            seqnum_limit: Some(self.seqnum_current),
            filenum_limit: Some(self.filenum_current),
            ..Default::default()
        });

        // write the final edit
        self.journal.append(final_edit).await?;

        // mark instance as shut down
        self.is_shutdown = true;

        info!("manifest shut down cleanly");
        Ok(())
    }

    fn calculate_filenum_range(
        &self,
        size: u64,
    ) -> StorageResult<(std::ops::Range<u64>, Option<u64>)> {
        let start = self.filenum_current;

        let end = start
            .checked_add(size)
            .ok_or(StorageError::FileNumOverflow)?;

        let range = start..end;
        if end > self.journal.filenum_limit {
            let new_limit = end.saturating_add(self.config.filenum_limit_step);
            Ok((range, Some(new_limit)))
        } else {
            Ok((range, None))
        }
    }

    fn calculate_seqnum_range(
        &self,
        size: u64,
    ) -> StorageResult<(std::ops::Range<SeqNum>, Option<SeqNum>)> {
        let start = self.seqnum_current;

        let raw_end = start
            .get()
            .checked_add(size)
            .ok_or(StorageError::SeqNumOverflow(u64::MAX))?;

        let end = SeqNum::try_from(raw_end)?;

        let range = start..end;

        if end > self.journal.seqnum_limit {
            let raw_limit = end.get().saturating_add(self.config.seqnum_limit_step);
            let new_limit = SeqNum::try_from(std::cmp::min(raw_limit, SeqNum::MAX.get()))
                .expect("handled by cmp::min");
            Ok((range, Some(new_limit)))
        } else {
            Ok((range, None))
        }
    }

    #[instrument(skip(self), level = "debug")]
    pub(crate) async fn handle_request(
        &mut self,
        req: ManifestRequest,
    ) -> StorageResult<ManifestResponse> {
        let mut requires_write = false;
        let mut edit = ManifestEditV1::default();

        if !req.ssts_added.is_empty() {
            edit.ssts_added = Some(req.ssts_added);
            requires_write = true;
        }

        if !req.ssts_removed.is_empty() {
            edit.ssts_removed = Some(req.ssts_removed);
            requires_write = true;
        }

        if !req.wal_filenums_added.is_empty() {
            edit.wal_filenums_added = Some(req.wal_filenums_added);
            requires_write = true;
        }

        if !req.wal_filenums_removed.is_empty() {
            edit.wal_filenums_removed = Some(req.wal_filenums_removed);
            requires_write = true;
        }

        let (seqnum_range, new_seqnum_limit) = self.calculate_seqnum_range(req.seqnums_needed)?;
        edit.seqnum_limit = new_seqnum_limit;
        if edit.seqnum_limit.is_some() {
            requires_write = true;
        }

        let (filenum_range, new_filenum_limit) =
            self.calculate_filenum_range(req.filenums_needed)?;
        edit.filenum_limit = new_filenum_limit;
        if edit.filenum_limit.is_some() {
            requires_write = true;
        }

        if requires_write {
            debug!("requires write");
            // write edit to disk
            let edit = ManifestEdit::V1(edit);
            self.journal.append(edit).await?;
        }

        // update `current_*` on successful commit
        self.seqnum_current = seqnum_range.end;
        self.filenum_current = filenum_range.end;

        let response = ManifestResponse {
            seqnum_range,
            filenum_range,
        };

        debug!(?response, "finished handling manifest request");
        Ok(response)
    }

    pub(crate) async fn get_seqnums(&mut self, n: u64) -> StorageResult<std::ops::Range<SeqNum>> {
        let (range, new_limit) = self.calculate_seqnum_range(n)?;
        if new_limit.is_some() {
            // Slow path: we have to write a new limit to disk
            let resp = self
                .handle_request(ManifestRequest::new().with_seqnums_needed(n))
                .await?;
            Ok(resp.seqnum_range)
        } else {
            // Fast path: just bump the current pointer
            self.seqnum_current = range.end;
            Ok(range)
        }
    }

    pub(crate) async fn get_filenums(&mut self, n: u64) -> StorageResult<std::ops::Range<u64>> {
        let (range, new_limit) = self.calculate_filenum_range(n)?;
        if new_limit.is_some() {
            // Slow path: we have to write a new limit to disk
            let resp = self
                .handle_request(ManifestRequest::new().with_filenums_needed(n))
                .await?;
            Ok(resp.filenum_range)
        } else {
            // Fast path: just bump the current pointer
            self.filenum_current = range.end;
            Ok(range)
        }
    }

    /// Returns the next sequence number that will be used.
    pub(crate) const fn seqnum_current(&self) -> SeqNum {
        self.seqnum_current
    }

    pub(crate) const fn filenum_current(&self) -> u64 {
        self.filenum_current
    }

    pub(crate) fn ssts(&self) -> &[SstMetadata] {
        &self.journal.ssts
    }

    pub(crate) fn wal_filenums(&self) -> &[u64] {
        &self.journal.wal_filenums
    }

    pub(crate) fn min_wal_filenum(&self) -> Option<u64> {
        self.journal.wal_filenums.iter().min().copied()
    }

    pub(crate) fn max_flushed_seqnum(&self) -> SeqNum {
        // TODO: We should track the max flushed seqnum to prevent this calculation, but this is
        // easier and cheap enough for now. It's still O(N) though...
        self.journal
            .ssts
            .iter()
            .map(|s| s.stats.max_seqnum)
            .max()
            .unwrap_or(SeqNum::ZERO)
    }
}

impl<F: FioFS> Drop for StorageManifest<F> {
    fn drop(&mut self) {
        if !self.is_shutdown {
            error!("manifest was not shut down correctly");
        }
    }
}
