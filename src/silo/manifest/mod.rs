use std::{
    collections::HashSet,
    io,
    path::{Path, PathBuf},
};

use bincode::Options as BincodeOptions;
use bytes::{BufMut, BytesMut};
use futures::{FutureExt, StreamExt, TryStreamExt};
use tokio_uring::buf::BoundedBuf;

use crate::{
    base::{ByteSize, HexU64, SeqNum, TempestError, TempestResult, bincode_options},
    fio::{FioFS, FioFile},
    silo::{
        config::ManifestConfig,
    },
};


mod format;
#[cfg(test)]
mod tests;

pub(crate) use format::*;

pub(super) fn get_sst_path(silo_root: impl AsRef<Path>, level: u8, filenum: u64) -> PathBuf {
    silo_root
        .as_ref()
        .join("ssts")
        .join(format!("l-{}", level))
        .join(format!("{}.sst", filenum))
}

#[derive(Debug, Default)]
pub(super) struct ManifestRequest {
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

pub(super) struct ManifestResponse {
    pub seqnum_range: std::ops::Range<SeqNum>,
    pub filenum_range: std::ops::Range<u64>,
}

/// Manages reads and writes to the manifest of a silo.
#[derive(Debug)]
pub(super) struct SiloManifest<F: FioFS> {
    /// The root path of the silo this manifest belongs to.
    silo_root: PathBuf,
    /// The path to the directory, where manifest files are in.
    manifest_dir: PathBuf,

    /// The file system this silo manifest uses.
    fs: F,

    /// A scratch buffer that is used for encoding and passed to FS writes.
    #[debug("{}", scratch.as_ref()
        .map(|b| format!("Some(BytesMut(len={},cap={}))", b.len(), b.capacity()))
        .unwrap_or_else(|| format!("None")))]
    scratch: Option<BytesMut>,

    /// File handle to the current manifest file.
    current_file: <F as FioFS>::File,
    /// Write offset in the current manifest file.
    filepos: u64,
    /// The initial file size of the current manifest file.
    initial_file_size: u64,

    /// Next sequence number that will be used for a range allocation.
    seqnum_current: SeqNum,
    /// Current max available sequence number.
    seqnum_limit: SeqNum,

    /// Next file number that will be used for a range allocation.
    filenum_current: u64,
    /// Current max available file number.
    filenum_limit: u64,

    /// List of sorted string tables in this silo.
    ssts: Vec<SstMetadata>,
    /// List of write-ahead logs in this silo
    wal_filenums: Vec<u64>,

    /// This is `true`, when [`shutdown`] was called.
    ///
    /// [`shutdown`]: Self::shutdown
    is_shutdown: bool,

    config: ManifestConfig,
}

impl<F: FioFS> SiloManifest<F> {
    #[instrument(skip_all, level = "info")]
    pub(super) async fn init(
        fs: F,
        silo_root: PathBuf,
        config: ManifestConfig,
    ) -> TempestResult<Self> {
        info!("initializing silo manifest at {:?}", silo_root);
        let manifest_dir = silo_root.join("manifest");
        fs.create_dir_all(&manifest_dir).await?;

        info!("checking manifest directory for old manifests");
        let entries: Vec<_> = fs
            .read_dir(&manifest_dir)
            .await?
            .try_filter(|e| futures::future::ready(!e.is_dir()))
            .try_collect()
            .await?;

        if !entries.is_empty() {
            info!(
                "found {} manifest files, attempting to get the latest one",
                entries.len()
            );
            let mut manifest_details: Vec<_> = futures::stream::iter(entries)
                .map(|entry| {
                    let fs = fs.clone();
                    async move {
                        let path = entry.path().to_path_buf();
                        let file = match fs.opts().read(true).write(true).open(&path).await {
                            Ok(f) => f,
                            Err(e) => {
                                warn!("could not open manifest file {:?}", path);
                                return Err(e.into());
                            }
                        };

                        let buf = BytesMut::zeroed(SILO_MANIFEST_HEADER_SIZE);
                        let (res, sliced_buf) = file.read_exact_at(buf.slice(..), 0).await;
                        let buf = sliced_buf.into_inner();
                        if let Err(e) = res {
                            warn!("could not read header for file {:?}", path);
                            return Err(e.into());
                        }

                        // decode header
                        let header = match SiloManifestHeader::decode(buf[..].try_into().unwrap()) {
                            Ok(h) => h,
                            Err(e) => {
                                warn!("could not decode header for file {:?}", path);
                                return Err(e.into());
                            }
                        };

                        Ok::<_, TempestError>((header.filenum, path, file))
                    }
                })
                // run 10 reads at once
                .buffer_unordered(10)
                .try_collect()
                .await?;

            manifest_details.sort_by_key(|(filenum, _, _)| *filenum);

            if let Some((highest_filenum, path, file)) = manifest_details.pop() {
                let size = file.size().await?;
                let mut filepos = SILO_MANIFEST_HEADER_SIZE as u64;
                let mut scratch = BytesMut::with_capacity(4096);

                let mut had_error = false;

                // -- editable params --
                let mut seqnum_limit = SeqNum::START;
                let mut filenum_limit = highest_filenum;
                let mut ssts: Vec<SstMetadata> = Vec::new();
                let mut wal_filenums: Vec<u64> = Vec::new();

                debug!(
                    highest_filenum, size=?ByteSize(size), ?path,
                    "found latest manifest file, starting read"
                );
                while filepos < size {
                    let res;
                    (res, scratch) = Self::read_framed_edit(scratch, &file, filepos).await;
                    let (edit, bytes_read) = match res {
                        Ok(v) => v,
                        Err(e) => {
                            warn!(
                                ?path, filepos=?HexU64(filepos), size=?ByteSize(size),
                                "could not read manifest edit: {}, reconstructing from remaining data", e
                            );
                            had_error = true;
                            break;
                        }
                    };
                    trace!("got edit from manifest: {:?}", edit);
                    filepos += bytes_read;
                    let edit = edit.into_latest();

                    if let Some(sl) = edit.seqnum_limit {
                        seqnum_limit = sl;
                    }

                    if let Some(fl) = edit.filenum_limit {
                        filenum_limit = fl;
                    }

                    if let Some(added) = edit.ssts_added {
                        ssts.extend(added);
                    }

                    if let Some(removed) = edit.ssts_removed {
                        let ids: HashSet<_> = removed.into_iter().map(|r| r.filenum).collect();
                        ssts.retain(|s| !ids.contains(&s.filenum));
                    }

                    if let Some(added) = edit.wal_filenums_added {
                        wal_filenums.extend(added);
                    }

                    if let Some(removed) = edit.wal_filenums_removed {
                        let ids: HashSet<_> = removed.into_iter().collect();
                        wal_filenums.retain(|n| !ids.contains(n));
                    }
                }
                info!(
                    seqnum_limit = seqnum_limit.get(),
                    filenum_limit,
                    ssts = ssts.len(),
                    wal_filenums = wal_filenums.len(),
                    "finished reading in manifest file",
                );

                let mut res = Self {
                    silo_root,
                    manifest_dir,

                    fs,

                    scratch: Some(scratch),

                    current_file: file,
                    filepos,
                    initial_file_size: filepos,

                    seqnum_current: seqnum_limit,
                    seqnum_limit,

                    filenum_current: filenum_limit,
                    filenum_limit,

                    ssts,
                    wal_filenums,

                    is_shutdown: false,

                    config,
                };

                if had_error {
                    info!(
                        "writing to a new manifest file, after encountering error when decoding manifest body"
                    );
                    res.write_to_new_file().await?;
                }

                info!("finished initializing manifest");
                return Ok(res);
            }
        }

        info!("no manifest file found, creating new file");
        // this is the initial manifest file number
        let filenum = 0;

        // open the initial file
        let filepath = manifest_dir.join(SiloManifestHeader::new(filenum).get_filename());
        let file = fs
            .opts()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(filepath)
            .await?;

        // initialize the scratch buffer
        let scratch = BytesMut::with_capacity(4096);

        // create initial edit
        let filenum_limit = filenum + config.filenum_limit_step;
        let initial_edit = ManifestEdit::V1(ManifestEditV1 {
            filenum_limit: Some(filenum_limit),
            ..Default::default()
        });
        let (res, scratch) = Self::write_to_file(&file, scratch, filenum, &initial_edit).await;
        let filepos = res?;

        // sync file for durability
        file.sync_all().await?;

        info!("finished initializing manifest");
        let initial_file_size = filepos;
        let filenum_current = filenum + 1;
        Ok(Self {
            fs,
            silo_root,
            manifest_dir,

            scratch: Some(scratch),

            current_file: file,
            filepos: filepos as u64,
            initial_file_size,

            seqnum_limit: SeqNum::START,
            seqnum_current: SeqNum::START,

            filenum_current,
            filenum_limit,

            ssts: Vec::new(),
            wal_filenums: Vec::new(),

            is_shutdown: false,

            config,
        })
    }

    pub(super) async fn shutdown(&mut self) -> TempestResult<()> {
        assert!(!self.is_shutdown, "silo has been shut down");

        // tighten down seqnum and filenum limit
        let final_edit = ManifestEdit::V1(ManifestEditV1 {
            seqnum_limit: Some(self.seqnum_current),
            filenum_limit: Some(self.filenum_current),
            ..Default::default()
        });

        // write the final edit
        self.append_framed_edit(&final_edit).await?;

        // sync file for durability
        self.current_file.sync_all().await?;

        // mark instance as shut down
        self.is_shutdown = true;

        // NB: Technically, we don't have to set these, since the instance was shut down,
        // but for debugging purposes and to prevent potential issues, we still do
        self.seqnum_limit = self.seqnum_current;
        self.filenum_limit = self.filenum_current;

        info!("silo manifest shut down cleanly");
        Ok(())
    }

    async fn write_to_new_file(&mut self) -> TempestResult<()> {
        assert!(!self.is_shutdown, "silo has been shut down");
        let (filenum_range, filenum_limit) = self.calculate_filenum_range(1)?;
        let filenum = filenum_range.start;

        let header = SiloManifestHeader::new(filenum);

        let filepath = self.manifest_dir.join(header.get_filename());
        let file = self
            .fs
            .opts()
            .read(true)
            .write(true)
            // NB: We set create and truncate instead of create_new here,
            // which may be 'less safe' in a way, but recovers better in practice
            .create(true)
            .truncate(true)
            .open(&filepath)
            .await?;

        let scratch = self.scratch.take().expect("scatch buffer exists");

        let initial_edit = ManifestEdit::V1(ManifestEditV1 {
            seqnum_limit: Some(self.seqnum_limit),
            filenum_limit: Some(filenum_limit.unwrap_or(self.filenum_limit)),
            // PERF: manifest edits with lifetime, to borrow instead of clone here
            // -> Cow for owned manifest edits? -> zero-copy?
            ssts_added: Some(self.ssts.clone()),
            wal_filenums_added: Some(self.wal_filenums.clone()),
            ..Default::default()
        });

        let (res, scratch) = Self::write_to_file(&file, scratch, filenum, &initial_edit).await;
        self.scratch = Some(scratch);

        let bytes_written = res?;
        self.filepos = bytes_written;
        self.initial_file_size = bytes_written;

        file.sync_all().await?;

        trace!(
            seqnum_limit=?self.seqnum_limit, filenum_limit=self.filenum_limit,
            ?filepath, filenum, bytes_written,
            "wrote manifest to new file",
        );
        Ok(())
    }

    /// Creates a new manifest file with the ID `filenum` and writes all current state to it.
    /// Note that, while we do write to the file, we don't `fsync` in any way, so the caller is
    /// responsible. Returns the number of bytes written and the used scratch buffer.
    async fn write_to_file(
        file: &<F as FioFS>::File,
        mut scratch: BytesMut,
        filenum: u64,
        initial_edit: &ManifestEdit,
    ) -> (TempestResult<u64>, BytesMut) {
        debug!(filenum, "writing manifest to new file");
        // clear scratch buffer
        scratch.clear();

        // create the header for the new manifest file
        let header = SiloManifestHeader::new(filenum);

        // encode manifest header into buffer
        scratch.put_slice(&header.encode());
        let (res, scratch) = file.write_all_at(scratch, 0).await;
        if let Err(e) = res {
            return (Err(e.into()), scratch);
        }

        // write edit into buffer and to file, returning the bytes written result and buffer
        Self::write_framed_edit(
            initial_edit,
            scratch,
            file,
            SILO_MANIFEST_HEADER_SIZE as u64,
        )
        .map(|(res, buf)| (res.map(|v| v + SILO_MANIFEST_HEADER_SIZE as u64), buf))
        .await
    }

    /// Writes a new framed edit into a file. Returns the number of bytes written.
    #[instrument(skip(edit, scratch, file), level = "trace")]
    async fn write_framed_edit(
        edit: &ManifestEdit,
        mut scratch: BytesMut,
        file: &<F as FioFS>::File,
        filepos: u64,
    ) -> (TempestResult<u64>, BytesMut) {
        // clear the scratch buffer
        scratch.clear();

        // reserve space for the record prefix
        scratch.put_bytes(0, SILO_MANIFEST_RECORD_PREFIX_SIZE);

        // write the edit into the buffer
        if let Err(e) = bincode_options().serialize_into((&mut scratch).writer(), edit) {
            return (Err(e.into()), scratch);
        }

        // create and store the record prefix
        let record_prefix =
            SiloManifestRecordPrefix::new(&scratch[SILO_MANIFEST_RECORD_PREFIX_SIZE..]);
        scratch[0..SILO_MANIFEST_RECORD_PREFIX_SIZE].copy_from_slice(&record_prefix.encode());

        // the created record prefix for data should validate the data successfully
        debug_assert!(record_prefix.is_valid_record(&scratch[SILO_MANIFEST_RECORD_PREFIX_SIZE..]));

        // write the scratch buffer to disk
        let (res, buf) = file.write_all_at(scratch, filepos).await;
        if let Err(e) = res {
            return (Err(e.into()), buf);
        }

        (Ok(buf.len() as u64), buf)
    }

    async fn append_framed_edit(&mut self, edit: &ManifestEdit) -> TempestResult<()> {
        let mut scratch = self.scratch.take().expect("scatch buffer exists");
        scratch.clear();

        let (res, scratch) =
            Self::write_framed_edit(edit, scratch, &self.current_file, self.filepos).await;

        self.scratch = Some(scratch);

        let bytes_written = res?;
        self.filepos += bytes_written;

        Ok(())
    }

    #[instrument(skip(scratch, file), level = "trace")]
    async fn read_framed_edit(
        mut scratch: BytesMut,
        file: &<F as FioFS>::File,
        filepos: u64,
    ) -> (TempestResult<(ManifestEdit, u64)>, BytesMut) {
        let mut current_filepos = filepos;

        // clear the scratch buffer
        scratch.clear();

        // make space for the manifest record to read
        scratch.resize(SILO_MANIFEST_RECORD_PREFIX_SIZE, 0);
        trace!(
            buf_len = scratch.len(),
            buf_cap = scratch.capacity(),
            "trying to read manifest record prefix into scratch buffer"
        );
        let (res, slice) = file
            .read_exact_at(scratch.slice(0..12), current_filepos)
            .await;
        if let Err(e) = res {
            return (Err(e.into()), slice.into_inner());
        }
        assert_eq!(slice.len(), SILO_MANIFEST_RECORD_PREFIX_SIZE);
        current_filepos += SILO_MANIFEST_RECORD_PREFIX_SIZE as u64;

        // decode the record prefix
        let prefix = SiloManifestRecordPrefix::decode(slice.as_ref().try_into().unwrap());
        trace!(
            data_len = prefix.data_len,
            checksum = ?HexU64(prefix.checksum),
            "read and decoded manifest record prefix"
        );

        // reconstruct the inner buffer from the sliced view
        let mut scratch = slice.into_inner();

        // read the record body
        scratch.clear();
        scratch.put_bytes(0, prefix.data_len as usize);
        let (res, slice) = file
            .read_exact_at(scratch.slice(0..prefix.data_len as usize), current_filepos)
            .await;
        if let Err(e) = res {
            return (Err(e.into()), slice.into_inner());
        }
        current_filepos += prefix.data_len as u64;

        // validate with checksum
        if !prefix.is_valid_record(slice.as_ref()) {
            return (
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "manifest record prefix checksum mismatch: potential corruption",
                )
                .into()),
                slice.into_inner(),
            );
        }

        // parse manifest edit from the body
        let edit: ManifestEdit = match bincode_options().deserialize(&slice) {
            Ok(e) => e,
            Err(e) => return (Err(e.into()), slice.into_inner()),
        };

        let bytes_read = current_filepos - filepos;

        (Ok((edit, bytes_read)), slice.into_inner())
    }

    fn calculate_filenum_range(
        &self,
        size: u64,
    ) -> TempestResult<(std::ops::Range<u64>, Option<u64>)> {
        let start = self.filenum_current;

        let end = start
            .checked_add(size)
            .ok_or(TempestError::FileNumOverflow)?;

        let range = start..end;
        if end > self.filenum_limit {
            let new_limit = end + self.config.filenum_limit_step;
            Ok((range, Some(new_limit)))
        } else {
            Ok((range, None))
        }
    }

    fn calculate_seqnum_range(
        &self,
        size: u64,
    ) -> TempestResult<(std::ops::Range<SeqNum>, Option<SeqNum>)> {
        let start = self.seqnum_current;

        let raw_end = start
            .get()
            .checked_add(size)
            .ok_or(TempestError::SeqNumOverflow(u64::MAX))?;

        let end = SeqNum::try_from(raw_end)?;

        let range = start..end;

        if end > self.seqnum_limit {
            let raw_limit = end.get() + self.config.seqnum_limit_step;
            let new_limit = SeqNum::try_from(std::cmp::min(raw_limit, SeqNum::MAX.get()))
                .expect("handled by cmp::min");
            Ok((range, Some(new_limit)))
        } else {
            Ok((range, None))
        }
    }

    pub(super) fn apply_edit(&mut self, edit: ManifestEdit) {
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
            let ids: HashSet<_> = removed.into_iter().map(|r| r.filenum).collect();
            self.ssts.retain(|s| !ids.contains(&s.filenum));
        }

        if let Some(added) = edit.wal_filenums_added {
            self.wal_filenums.extend(added);
        }

        if let Some(removed) = edit.wal_filenums_removed {
            let ids: HashSet<_> = removed.into_iter().collect();
            self.wal_filenums.retain(|n| !ids.contains(n));
        }
    }

    async fn maybe_rotate(&mut self) -> TempestResult<()> {
        let threshold = std::cmp::max(
            self.initial_file_size * self.config.growth_factor,
            self.config.growth_baseline,
        );

        if self.filepos > threshold {
            trace!(current = self.filepos, threshold, "rotating manifest file");
            self.write_to_new_file().await?;
        }

        Ok(())
    }

    #[instrument(skip(self))]
    pub(super) async fn handle_request(
        &mut self,
        req: ManifestRequest,
    ) -> TempestResult<ManifestResponse> {
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
            // write edit to disk
            let edit = ManifestEdit::V1(edit);
            self.append_framed_edit(&edit).await?;
            self.current_file.sync_all().await?;

            // rotate file when surpassing threshold
            self.maybe_rotate().await?;

            // apply the manifest state edit to memory
            self.apply_edit(edit);
        }

        // update `current_*` on successful commit
        self.seqnum_current = seqnum_range.end;
        self.filenum_current = filenum_range.end;

        Ok(ManifestResponse {
            seqnum_range,
            filenum_range,
        })
    }

    pub(super) async fn get_seqnums(&mut self, n: u64) -> TempestResult<std::ops::Range<SeqNum>> {
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

    pub(super) async fn get_filenums(&mut self, n: u64) -> TempestResult<std::ops::Range<u64>> {
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
    pub(super) const fn seqnum_current(&self) -> SeqNum {
        self.seqnum_current
    }

    pub(super) fn ssts(&self) -> &[SstMetadata] {
        &self.ssts
    }

    pub(super) fn wal_filenums(&self) -> &[u64] {
        &self.wal_filenums
    }
}

impl<F: FioFS> Drop for SiloManifest<F> {
    fn drop(&mut self) {
        if !self.is_shutdown {
            error!("silo manifest was not shut down correctly");
        }
    }
}
