use std::{
    collections::HashSet,
    io,
    path::{Path, PathBuf},
};

use bincode::Options as BincodeOptions;
use bytes::{BufMut, BytesMut};
use crc64::crc64;
use futures::{FutureExt, StreamExt, TryStreamExt};
use serde::{Deserialize, Serialize};
use tokio_uring::buf::BoundedBuf;

use crate::{
    base::{SILO_MANIFEST_MAGICNUM, SeqNum, TempestError, TempestResult},
    fio::{FioFS, FioFile},
};

const SEQNUM_LIMIT_STEP: u64 = 1000;
const FILENUM_LIMIT_STEP: u64 = 100;

fn get_sst_path(silo_root: impl AsRef<Path>, level: u8, file_number: u64) -> PathBuf {
    silo_root
        .as_ref()
        .join(format!("l-{}", level))
        .join(format!("{}.sst", file_number))
}

fn bincode_options() -> impl BincodeOptions {
    bincode::options()
        .with_fixint_encoding() // Important: no variable length ints
        .with_little_endian() // Ensure consistency across platforms
        .allow_trailing_bytes()
}

/// # SST Metadata
///
/// Stores the metadata for one sorted string table within Tempest.
/// The path format is **`/{silo_root}/ssts/l-{level}/{filenum}.sst`**,
/// which can be obtained simply through the [`get_path`] method.
///
/// [`get_path`]: Self::get_path
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct SstMetadata {
    pub(super) filenum: u64,
    pub(super) file_size: u64,

    pub(super) level: u8,

    pub(super) min_key: Vec<u8>,
    pub(super) max_key: Vec<u8>,

    pub(super) min_seqnum: SeqNum,
    pub(super) max_seqnum: SeqNum,
}

impl SstMetadata {
    /// Returns the file system path for the SST this Metadata references.
    /// The path is returned as within the `ssts` subdirectory of `data`.
    /// To get the whole path, join these two together.
    pub fn get_path(&self, silo_root: impl AsRef<Path>) -> PathBuf {
        get_sst_path(silo_root, self.level, self.filenum)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub(super) struct SstDeletion {
    pub(super) filenum: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ManifestEditV1 {
    seqnum_limit: Option<SeqNum>,
    filenum_limit: Option<u64>,

    /// A list of new [`SstMetadata`] objects that register SST files to the [`SiloManifest`].
    ssts_added: Option<Vec<SstMetadata>>,

    /// A list of removed [`SstMetadata`] objects, identified by their level and file ID,
    /// that register SST files to the [`SiloManifest`].
    ssts_removed: Option<Vec<SstDeletion>>,
}

/// A versioned list of edits to the [`SiloManifest`].
#[repr(u16)]
#[derive(Debug, Serialize, Deserialize)]
pub enum ManifestEdit {
    V1(ManifestEditV1) = 1,
}

impl ManifestEdit {
    fn into_latest(self) -> ManifestEditV1 {
        match self {
            ManifestEdit::V1(edit) => edit,
        }
    }
}

/// Total size of a [`SiloManifestHeader`] after encoding.
const SILO_MANIFEST_HEADER_SIZE: usize = 24;

struct SiloManifestHeader {
    filenum: u64,
    filename: PathBuf,
}

impl SiloManifestHeader {
    pub fn new(filenum: u64) -> Self {
        // allocate filename once, to safe on future allocations using `get_filename`
        let filename = PathBuf::from(format!("MANIFEST-{}", filenum));
        Self { filenum, filename }
    }

    #[inline]
    pub const fn filenum(&self) -> u64 {
        self.filenum
    }

    #[inline]
    pub fn get_filename(&self) -> &Path {
        &self.filename
    }

    pub fn encode(&self) -> [u8; SILO_MANIFEST_HEADER_SIZE] {
        let mut buf = [0u8; SILO_MANIFEST_HEADER_SIZE];
        // 1. Magic bytes
        buf[0..8].copy_from_slice(SILO_MANIFEST_MAGICNUM);

        // 2. Manifest ID / file number (little-endian)
        buf[8..16].copy_from_slice(&self.filenum.to_le_bytes());

        // 3. Calculate and store CRC64 checksum
        let bytes_to_hash = &buf[0..16];
        let checksum = crc64(0, bytes_to_hash);
        buf[16..24].copy_from_slice(&checksum.to_le_bytes());
        buf
    }

    pub fn decode(buf: &[u8; SILO_MANIFEST_HEADER_SIZE]) -> io::Result<Self> {
        let magic_bytes = &buf[0..8];
        if magic_bytes != SILO_MANIFEST_MAGICNUM {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "invalid magic number: not a manifest file. expected {:?} but got {:?}.",
                    SILO_MANIFEST_MAGICNUM, magic_bytes
                ),
            ));
        }

        let checksum_bytes = buf[16..24].try_into().expect("16..24 is 8 long");
        let checksum = u64::from_le_bytes(checksum_bytes);
        let computed_checksum = crc64(0, &buf[0..16]);
        if computed_checksum != checksum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "manifest header checksum mismatch: potential corruption",
            ));
        }

        let file_number_bytes = buf[8..16].try_into().expect("8..16 is 8 long");
        let file_number = u64::from_le_bytes(file_number_bytes);
        Ok(Self::new(file_number))
    }
}

/// Total size of a record prefix in a silo manifest.
const SILO_MANIFEST_RECORD_PREFIX_SIZE: usize = 12;

struct SiloManifestRecordPrefix {
    data_len: u32,
    checksum: u64,
}

impl SiloManifestRecordPrefix {
    /// Creates a new record prefix for some data, providing a frame with a checksum.
    fn new(data: &[u8]) -> Self {
        assert!(
            data.len() <= u32::MAX as usize,
            "manifest record size may not exceed 2^32 bytes."
        );
        let data_len = data.len() as u32;
        let checksum = crc64(0, data);
        Self { data_len, checksum }
    }

    /// Calculates the checksum of `data` and compares it with the stored checksum.
    /// The length of `data` must equal the stored `data_len`.
    #[inline]
    fn is_valid_data(&self, data: &[u8]) -> bool {
        assert!(data.len() == self.data_len as usize);
        let computed_checksum = crc64(0, data);
        self.checksum == computed_checksum
    }

    /// Encodes this record prefix into bytes.
    fn encode(&self) -> [u8; SILO_MANIFEST_RECORD_PREFIX_SIZE] {
        let mut buf = [0u8; SILO_MANIFEST_RECORD_PREFIX_SIZE];

        buf[0..4].copy_from_slice(&self.data_len.to_le_bytes());
        buf[4..12].copy_from_slice(&self.checksum.to_le_bytes());

        buf
    }

    /// Decodes this record prefix from a byte slice.
    fn decode(buf: &[u8; SILO_MANIFEST_RECORD_PREFIX_SIZE]) -> Self {
        let data_len = u32::from_le_bytes(buf[0..4].try_into().unwrap());
        let checksum = u64::from_le_bytes(buf[4..12].try_into().unwrap());
        Self { data_len, checksum }
    }
}

#[derive(Debug, Default)]
pub(super) struct ManifestRequest {
    pub ssts_added: Vec<SstMetadata>,
    pub ssts_removed: Vec<SstDeletion>,
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

/// The ratio between the current file size and the baseline snapshot size
/// that triggers a rotation of the manifest file.
const SILO_MANIFEST_GROWTH_FACTOR: u64 = 2;

/// The minimum file size required before growth.
/// The growth factor does not matter when below this baseline.
const SILO_MANIFEST_GROWTH_BASELINE: u64 = 8 * 1024 * 1024; // 8 MiB

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
    current_filepos: u64,
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

    /// This is `true`, when [`shutdown`] was called.
    ///
    /// [`shutdown`]: Self::shutdown
    is_shutdown: bool,
}

impl<F: FioFS> SiloManifest<F> {
    #[instrument(skip_all, level = "info")]
    pub(super) async fn init(fs: F, silo_root: PathBuf) -> TempestResult<Self> {
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
                                warn!("could not open manifest file {:?}, skipping", path);
                                return Err(e.into());
                            }
                        };

                        let buf = BytesMut::zeroed(SILO_MANIFEST_HEADER_SIZE);
                        let (res, buf) = file.read_exact_at(buf, 0).await;
                        if let Err(e) = res {
                            warn!("could not read header for file {:?}", path);
                            return Err(e.into());
                        }

                        // decode header
                        let header =
                            match SiloManifestHeader::decode(buf.as_ref().try_into().unwrap()) {
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
                let file_size = file.size().await?;
                let mut current_filepos = SILO_MANIFEST_HEADER_SIZE as u64;
                let mut scratch = BytesMut::with_capacity(4096);

                let mut had_error = false;

                // -- editable params --
                let mut seqnum_limit = SeqNum::START;
                let mut filenum_limit = highest_filenum;
                let mut ssts: Vec<SstMetadata> = Vec::new();

                debug!(
                    highest_filenum,
                    file_size,
                    ?path,
                    "found latest manifest file, starting read"
                );
                while current_filepos < file_size {
                    let res;
                    (res, scratch) = Self::read_framed_edit(scratch, &file, current_filepos).await;
                    let (edit, bytes_read) = match res {
                        Ok(v) => v,
                        Err(e) => {
                            warn!(
                                ?path,
                                ?current_filepos,
                                ?file_size,
                                "could not read manifest edit: {}, reconstructing from remaining data",
                                e
                            );
                            had_error = true;
                            break;
                        }
                    };
                    trace!("got edit from manifest: {:?}", edit);
                    current_filepos += bytes_read;
                    let edit = edit.into_latest();

                    if let Some(sl) = edit.seqnum_limit {
                        seqnum_limit = sl;
                    }

                    if let Some(fl) = edit.filenum_limit {
                        filenum_limit = fl;
                    }

                    if let Some(removed) = edit.ssts_removed {
                        let ids: HashSet<_> = removed.into_iter().map(|r| r.filenum).collect();
                        ssts.retain(|s| !ids.contains(&s.filenum));
                    }

                    if let Some(added) = edit.ssts_added {
                        ssts.extend(added);
                    }
                }
                info!(
                    seqnum_limit = seqnum_limit.get(),
                    filenum_limit,
                    ssts = ssts.len(),
                    "finished reading in manifest file",
                );

                let mut res = Self {
                    silo_root,
                    manifest_dir,

                    fs,

                    scratch: Some(scratch),

                    current_file: file,
                    current_filepos,
                    initial_file_size: current_filepos,

                    seqnum_current: seqnum_limit,
                    seqnum_limit,

                    filenum_current: filenum_limit,
                    filenum_limit,

                    ssts,

                    is_shutdown: false,
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
        let filenum_limit = filenum + FILENUM_LIMIT_STEP;
        let initial_edit = ManifestEdit::V1(ManifestEditV1 {
            filenum_limit: Some(filenum_limit),
            seqnum_limit: None,
            ssts_added: None,
            ssts_removed: None,
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
            current_filepos: filepos as u64,
            initial_file_size,

            seqnum_limit: SeqNum::START,
            seqnum_current: SeqNum::START,

            filenum_current,
            filenum_limit,

            ssts: Vec::new(),

            is_shutdown: false,
        })
    }

    pub(super) async fn shutdown(&mut self) -> TempestResult<()> {
        assert!(!self.is_shutdown, "silo has been shut down");

        // tighten down seqnum and filenum limit
        let final_edit = ManifestEdit::V1(ManifestEditV1 {
            seqnum_limit: Some(self.seqnum_current),
            filenum_limit: Some(self.filenum_current),
            ssts_added: None,
            ssts_removed: None,
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

        let scratch = self.scratch.take().expect("scatch buffer not taken yet");

        let initial_edit = ManifestEdit::V1(ManifestEditV1 {
            seqnum_limit: Some(self.seqnum_limit),
            filenum_limit: Some(filenum_limit.unwrap_or(self.filenum_limit)),
            // PERF: manifest edits with lifetime, to borrow instead of clone here
            // -> Cow for owned manifest edits? -> zero-copy?
            ssts_added: Some(self.ssts.clone()),
            ssts_removed: None,
        });

        let (res, scratch) = Self::write_to_file(&file, scratch, filenum, &initial_edit).await;
        self.scratch = Some(scratch);

        let bytes_written = res?;
        self.current_filepos = bytes_written;
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
        debug_assert!(record_prefix.is_valid_data(&scratch[SILO_MANIFEST_RECORD_PREFIX_SIZE..]));

        // write the scratch buffer to disk
        let (res, buf) = file.write_all_at(scratch, filepos).await;
        if let Err(e) = res {
            return (Err(e.into()), buf);
        }

        (Ok(buf.len() as u64), buf)
    }

    async fn append_framed_edit(&mut self, edit: &ManifestEdit) -> TempestResult<()> {
        let mut scratch = self.scratch.take().expect("scatch buffer not taken yet");
        scratch.clear();

        let (res, scratch) =
            Self::write_framed_edit(edit, scratch, &self.current_file, self.current_filepos).await;

        self.scratch = Some(scratch);

        let bytes_written = res?;
        self.current_filepos += bytes_written;

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
            checksum = prefix.checksum,
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
        let is_valid = prefix.is_valid_data(slice.as_ref());
        if !is_valid {
            return (
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "manifest record prefix body was corrupted.",
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
            let new_limit = end + FILENUM_LIMIT_STEP;
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
            let raw_limit = end.get() + SEQNUM_LIMIT_STEP;
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

        if let Some(removed) = edit.ssts_removed {
            let ids: HashSet<_> = removed.into_iter().map(|r| r.filenum).collect();
            self.ssts.retain(|s| !ids.contains(&s.filenum));
        }

        if let Some(added) = edit.ssts_added {
            self.ssts.extend(added);
        }
    }

    async fn maybe_rotate(&mut self) -> TempestResult<()> {
        let threshold = std::cmp::max(
            self.initial_file_size * SILO_MANIFEST_GROWTH_FACTOR,
            SILO_MANIFEST_GROWTH_BASELINE,
        );

        if self.current_filepos > threshold {
            trace!(
                current = self.current_filepos,
                threshold, "rotating manifest file"
            );
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
        let mut edit = ManifestEditV1 {
            seqnum_limit: None,
            filenum_limit: None,
            ssts_added: None,
            ssts_removed: None,
        };

        if !req.ssts_added.is_empty() {
            edit.ssts_added = Some(req.ssts_added);
            requires_write = true;
        }

        if !req.ssts_removed.is_empty() {
            edit.ssts_removed = Some(req.ssts_removed);
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

    /// Returns the next sequence number that will be used.
    pub(super) const fn seqnum_current(&self) -> SeqNum {
        self.seqnum_current
    }
}

#[cfg(test)]
mod tests {
    use tracing::Level;

    use crate::{fio::VirtualFileSystem, tests::setup_tracing};

    use super::*;

    #[test]
    fn test_header_encode_decode() {
        let filenum = 42;
        let header = SiloManifestHeader::new(filenum);
        let encoded = header.encode();
        assert_eq!(encoded.len(), SILO_MANIFEST_HEADER_SIZE);
        let decoded = SiloManifestHeader::decode(&encoded).unwrap();
        assert_eq!(decoded.filenum, filenum);
    }

    #[test]
    fn test_record_prefix_encode_decode() {
        let data = b"some-garbage-data".as_ref();
        let record = SiloManifestRecordPrefix::new(data);
        let encoded = record.encode();
        assert_eq!(encoded.len(), SILO_MANIFEST_RECORD_PREFIX_SIZE);
        let decoded = SiloManifestRecordPrefix::decode(&encoded);
        assert!(decoded.is_valid_data(data));
    }

    #[test]
    fn test_manifest() {
        setup_tracing();
        tokio_uring::start(async {
            let silo_span = span!(Level::INFO, "silo", id = 0);
            let _enter = silo_span.enter();

            let fs = VirtualFileSystem::new();
            let silo_root = PathBuf::from("silo-0");

            let first_seqnum_range;
            let second_seqnum_range;

            {
                let mut manifest = SiloManifest::init(fs.clone(), silo_root.clone()).await?;
                let seqnums_needed = 10;
                let response = manifest
                    .handle_request(ManifestRequest::default().with_seqnums_needed(seqnums_needed))
                    .await?;
                first_seqnum_range = response.seqnum_range;
                manifest.shutdown().await?;
                info!("first manifest final state: {:#?}", manifest);
                let range_size = first_seqnum_range.end.get() - first_seqnum_range.start.get();
                assert_eq!(
                    range_size, seqnums_needed,
                    "requested {} seqnums, but got {}",
                    seqnums_needed, range_size,
                );
            }

            {
                let mut manifest = SiloManifest::init(fs.clone(), silo_root.clone()).await?;
                // simulate big seqnum request
                let seqnums_needed = SEQNUM_LIMIT_STEP * 3 / 2 + 10;
                let resp = manifest
                    .handle_request(ManifestRequest::default().with_seqnums_needed(seqnums_needed))
                    .await?;
                second_seqnum_range = resp.seqnum_range;
                manifest.shutdown().await?;
                info!("second manifest final state: {:#?}", manifest);
                let range_size = second_seqnum_range.end.get() - second_seqnum_range.start.get();
                assert_eq!(
                    range_size, seqnums_needed,
                    "requested {} seqnums, but got {}",
                    seqnums_needed, range_size,
                );
            }

            assert_eq!(
                first_seqnum_range.end, second_seqnum_range.start,
                "seqnum ranges should be continuous, got {:?} and {:?}",
                first_seqnum_range, second_seqnum_range,
            );

            Ok::<(), TempestError>(())
        })
        .unwrap();
    }
}
