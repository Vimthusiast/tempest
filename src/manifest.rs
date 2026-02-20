use std::{
    any::type_name,
    collections::HashSet,
    io,
    path::{Path, PathBuf},
    pin::Pin,
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
    },
};

use arc_swap::ArcSwap;
use bytes::{BufMut, Bytes, BytesMut};
use crc64::crc64;
use futures::StreamExt;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{
    core::{MANIFEST_MAGICNUM, SeqNum},
    fio::{FioFS, FioFile},
};

fn get_sst_path(level: u8, file_number: u64) -> PathBuf {
    PathBuf::new()
        .join("ssts")
        .join(format!("l-{}", level))
        .join(format!("{}.sst", file_number))
}

/// # SST Metadata
///
/// Stores the metadata for one sorted string table within Tempest.
/// The path format is **`./ssts/l-{level}/{file_number}.sst`** which
/// can be obtained simply through the [`get_path`] method.
///
/// [`get_path`]: Self::get_path
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SstMetadata {
    filenum: u64,
    file_size: u64,
    level: u8,
    smallest_key: Vec<u8>,
    largest_key: Vec<u8>,
}

impl SstMetadata {
    /// Returns the file system path for the SST this Metadata references.
    /// The path is returned as within the `ssts` subdirectory of `data`.
    /// To get the whole path, join these two together.
    pub fn get_path(&self) -> PathBuf {
        get_sst_path(self.level, self.filenum)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SstDeletion {
    filenum: u64,
    level: u8,
}

impl SstDeletion {
    pub fn get_path(&self) -> PathBuf {
        get_sst_path(self.level, self.filenum)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VersionEditV1 {
    seqnum_limit: Option<SeqNum>,
    filenum_limit: Option<u64>,
    /// A list of new [`SstMetadata`] objects that register SST files to the [`ManifestManager`].
    ssts_added: Option<Arc<[SstMetadata]>>,
    /// A list of removed [`SstMetadata`] objects, identified by their level and file ID,
    /// that register SST files to the [`ManifestManager`].
    ssts_removed: Option<Arc<[SstDeletion]>>,
}

/// A versioned list of all different version edits to the [`ManifestManager`].
#[repr(u16)]
#[derive(Debug, Serialize, Deserialize)]
pub enum VersionEdit {
    V1(VersionEditV1) = 1,
}

impl VersionEdit {
    fn into_latest(self) -> VersionEditV1 {
        match self {
            VersionEdit::V1(edit) => edit,
        }
    }
}

/// An **immutable** version of the [`ManifestManager`]s internal state.
#[derive(Debug, Clone)]
pub struct ManifestVersion {
    seqnum_limit: SeqNum,
    filenum_limit: u64,
    /// List of active SSTs on disk.
    ssts: Arc<[SstMetadata]>,
    filepath: Arc<Path>,
}

/// As the [`ManifestManager`] creates log files on disk, this header comes first at the start.
/// It encodes a static magic number, file ID, and checksum for those other bytes, so 24 bytes.
#[derive(Debug)]
pub struct ManifestHeader {
    file_number: u64,
    filename: PathBuf,
}

impl ManifestHeader {
    pub const MAGIC: &[u8; 8] = MANIFEST_MAGICNUM;

    /// Total size of the [`ManifestHeader`] after encoding.
    pub const SIZE: usize = 24;

    pub fn new(file_number: u64) -> Self {
        let filename = format!("MANIFEST-{}", file_number).into();
        Self {
            file_number,
            filename,
        }
    }

    #[inline]
    pub const fn file_number(&self) -> u64 {
        self.file_number
    }

    #[inline]
    pub fn get_filename(&self) -> &Path {
        &self.filename
    }

    pub fn encode(&self, buf: &mut [u8; Self::SIZE]) {
        // 1. Magic bytes
        buf[0..8].copy_from_slice(MANIFEST_MAGICNUM);

        // 2. Manifest ID / file number (little-endian)
        buf[8..16].copy_from_slice(&self.file_number.to_le_bytes());

        // 3. Calculate and store CRC64 checksum
        let bytes_to_hash = &buf[0..16];
        let checksum = crc64(0, bytes_to_hash);
        buf[16..24].copy_from_slice(&checksum.to_le_bytes());
    }

    pub fn decode(buf: &[u8; 24]) -> io::Result<Self> {
        let magic_bytes = &buf[0..8];
        if magic_bytes != MANIFEST_MAGICNUM {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Invalid magic number: not a manifest file. Expected {:?} but got {:?}.",
                    MANIFEST_MAGICNUM, magic_bytes
                ),
            ));
        }

        let checksum_bytes = buf[16..24].try_into().expect("16..24 is 8 long");
        let checksum = u64::from_le_bytes(checksum_bytes);
        let computed_checksum = crc64(0, &buf[0..16]);
        if computed_checksum != checksum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Manifest header checksum mismatch: potential corruption",
            ));
        }

        let file_number_bytes = buf[8..16].try_into().expect("8..16 is 8 long");
        let file_number = u64::from_le_bytes(file_number_bytes);
        Ok(Self::new(file_number))
    }
}

const MANIFEST_RECORD_PREFIX_SIZE: usize = 12;

#[derive(Debug)]
struct ManifestWriter<F: FioFS> {
    /// The file we are writing to.
    #[debug("{}",type_name::<<F as FioFS>::File>())]
    file: Pin<Box<<F as FioFS>::File>>,
    /// The current position in the file.
    pos: u64,
}

const FILENUM_LIMIT_STEP: u64 = 100;
const SEQNUM_LIMIT_STEP: u64 = 1000;

#[derive(Debug)]
pub struct ManifestManager<F: FioFS> {
    #[debug("{}", type_name::<F>())]
    fs: F,
    root_dir: PathBuf,
    manifest_dir: PathBuf,

    current_version: ArcSwap<ManifestVersion>,
    writer: tokio::sync::Mutex<Option<ManifestWriter<F>>>,

    filenum_current: AtomicU64,
    filenum_limit: AtomicU64,

    seqnum_current: AtomicU64,
    seqnum_limit: AtomicU64,

    is_shutdown: AtomicBool,
}

macro_rules! assert_manifest_writer_guard {
    ($self:ident, $writer_guard:expr) => {{
        debug_assert!(
            std::ptr::eq(tokio::sync::MutexGuard::mutex($writer_guard), &$self.writer),
            "The provied MutexGuard does not belong to the right instance"
        );
    }};
}

impl<F: FioFS> ManifestManager<F> {
    /// Initializes this Manifest Manager instance on the root directory `root_dir`, which is the
    /// root of this [`Tempest`] instance.
    ///
    /// [`Tempest`]: crate::Tempest
    pub(crate) async fn init(fs: F, root_dir: impl Into<PathBuf>) -> io::Result<Self> {
        let root_dir = root_dir.into();
        let manifest_dir = root_dir.join("manifests");
        fs.create_dir_all(&manifest_dir).await?;

        let res = Self {
            root_dir,
            manifest_dir,
            fs,

            current_version: ArcSwap::new(Arc::new(ManifestVersion {
                seqnum_limit: SeqNum::START,
                filenum_limit: 0,
                ssts: Arc::new([]),
                filepath: Arc::from(PathBuf::from("")),
            })),
            writer: Default::default(),

            filenum_current: 0.into(),
            filenum_limit: 0.into(),

            seqnum_current: SeqNum::START.get().into(),
            seqnum_limit: SeqNum::START.get().into(),

            is_shutdown: false.into(),
        };

        // list and aggregate all files in manifest directory, skipping subdirectories
        let mut entries = Vec::new();
        let mut entry_stream = res.fs.read_dir(&res.manifest_dir).await?;
        while let Some(entry) = entry_stream.next().await {
            let entry = entry?;
            if entry.is_dir() {
                eprintln!(
                    "found sub-directory '{:?}' in manifest directory, skipping",
                    entry.path()
                );
                continue;
            }
            entries.push(entry);
        }

        // read in old files
        if entries.len() > 0 {
            println!("Looking through {} old manifest files", entries.len());
            // aggregate all manifest file headers
            let mut files_with_header = Vec::new();
            for entry in entries {
                println!("Reading manifest header for {:?}", entry.path());
                let file = res.fs.open(entry.path()).await?;
                let file = Box::pin(file);
                // read the header
                let header_buf = BytesMut::zeroed(ManifestHeader::SIZE);
                let (res, header_buf) = file.read_exact_at(header_buf, 0).await;
                if let Err(err) = res {
                    eprintln!(
                        "could not read manifest header for {:?}: {}",
                        entry.path(),
                        err
                    );
                    return Err(err);
                }
                let header = ManifestHeader::decode(header_buf.as_ref().try_into().unwrap())?;
                files_with_header.push((header, file));
            }

            // get newest manifest file, ordered by file number in header
            let (header, file) = files_with_header
                .into_iter()
                .sorted_by_key(|(h, _f)| h.file_number)
                .last()
                .expect("we should have at least one file here");

            // set the new file name
            let mut writer_guard = res.writer.try_lock().expect("should not be locked yet");
            res.swap_current_filename(
                res.manifest_dir.join(header.get_filename()).into(),
                &writer_guard,
            );

            // start decoding after header (already parsed above)
            let pos = ManifestHeader::SIZE as u64;
            let writer = writer_guard.insert(ManifestWriter { file, pos });

            // reapply commit log in manifest file
            println!("Reapplying manifest file {:?}", header.get_filename());
            res.decode_manifest_file_body(writer).await?;
            println!("Finished loading old data from {:?}", header.get_filename());

            // update the initial offsets to the limit
            let current_arc = res.current_version.load();
            res.filenum_current
                .store(current_arc.filenum_limit, Ordering::Release);
            res.seqnum_current
                .store(current_arc.seqnum_limit.get(), Ordering::Release);
        } else {
            // when there is no file, create one
            let filenum = 0;
            let filenum_limit = filenum + FILENUM_LIMIT_STEP;
            res.filenum_current.store(filenum + 1, Ordering::Release);
            res.filenum_limit.store(filenum_limit, Ordering::Release);

            // lock the file writer
            let mut writer_guard = res.writer.try_lock().expect("should not be locked yet");

            // create the new file header
            let header = ManifestHeader::new(filenum);
            res.swap_current_filename(
                res.manifest_dir.join(header.get_filename()).into(),
                &writer_guard,
            );
            let current_version = res.current_version.load();

            // open file
            let file = res.fs.create(&current_version.filepath).await?;
            let file = Box::pin(file);

            // write header
            let mut header_buf = BytesMut::zeroed(ManifestHeader::SIZE);
            header.encode(header_buf.as_mut().try_into().unwrap());
            file.write_all_at(Bytes::from(header_buf), 0).await.0?;

            let writer = writer_guard.insert(ManifestWriter {
                file,
                // continue writing after header
                pos: ManifestHeader::SIZE as u64,
            });

            let edit = VersionEditV1 {
                seqnum_limit: Some(SeqNum::START),
                filenum_limit: Some(filenum + FILENUM_LIMIT_STEP),
                ssts_added: None,
                ssts_removed: None,
            };

            // write the first setup version edit
            res.write_framed_edit(writer, &VersionEdit::V1(edit))
                .await?;

            // sync all file metadata
            writer.file.sync_all().await?;
        }

        Ok(res)
    }

    pub(crate) async fn shutdown(&self) -> io::Result<()> {
        let mut writer_guard = self.writer.lock().await;
        if self
            .is_shutdown
            .compare_exchange(false, true, Ordering::Release, Ordering::Relaxed)
            .is_err()
        {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "Manifest manager has already been shut down",
            ));
        }

        // get the exact current allocation limits
        let final_seq = self
            .seqnum_current
            .load(Ordering::Acquire)
            .try_into()
            .expect("checked in range");
        let final_filenum = self.filenum_current.load(Ordering::Acquire);

        // create a final version edit, that tightens down the seqnum and filenum limits
        let edit = VersionEdit::V1(VersionEditV1 {
            seqnum_limit: Some(final_seq),
            filenum_limit: Some(final_filenum),
            ssts_added: None,
            ssts_removed: None,
        });

        // write the final version edit
        self.write_version_edit(edit, &mut writer_guard).await?;
        Ok(())
    }

    fn swap_current_filename(
        &self,
        filename: Arc<Path>,
        writer_guard: &tokio::sync::MutexGuard<'_, Option<ManifestWriter<F>>>,
    ) {
        assert_manifest_writer_guard!(self, writer_guard);
        let current_arc = self.current_version.load();

        let mut new_version = (**current_arc).clone();
        new_version.filepath = filename;

        self.current_version.store(new_version.into());
    }

    pub async fn flush_to_new_file(&self) -> io::Result<()> {
        // obtain a file number for the new manifest file
        // TODO: don't do this here, but after lock and wait with file writes for new file
        let file_number = self.next_file_number().await?;

        // lock all modifications
        let mut writer_guard = self.writer.lock().await;

        println!("Flushing to new file (#{})", file_number);

        // get a snapshot of the current version after locking
        let current_snapshot = self.current_version.load();

        // create the header
        let header = ManifestHeader::new(file_number);

        // there will only be one edit at first
        let edit = VersionEdit::V1(VersionEditV1 {
            seqnum_limit: Some(current_snapshot.seqnum_limit),
            filenum_limit: Some(current_snapshot.filenum_limit),
            ssts_added: Some(current_snapshot.ssts.clone()),
            ssts_removed: None,
        });

        // compute and update the new file path
        self.swap_current_filename(
            self.manifest_dir.join(header.get_filename()).into(),
            &writer_guard,
        );
        let current_arc = self.current_version.load();
        println!("Flushing manifest to new file {:?}", current_arc.filepath);

        // get writer guard inner value
        let writer = writer_guard.as_mut().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "Manifest writer not initialized")
        })?;

        // create the new file in fs and point the writer to it
        let file = self.fs.create(&current_arc.filepath).await?;
        let file = Box::pin(file);
        writer.file = file;

        // write the header
        let mut header_buf = BytesMut::zeroed(ManifestHeader::SIZE);
        header.encode(header_buf.as_mut().try_into().unwrap());
        writer.file.write_all_at(header_buf.freeze(), 0).await.0?;
        // advance writer past header
        writer.pos = ManifestHeader::SIZE as u64;

        // write the first large setup version edit
        self.write_framed_edit(writer, &edit).await?;

        // sync all file metadata
        writer.file.sync_all().await?;
        Ok(())
    }

    fn apply_to_mem_and_swap(&self, edit: VersionEdit) {
        let edit = edit.into_latest();
        println!("Applying edit: {:?}", edit);
        let current_arc = self.current_version.load();

        let mut new_ssts = current_arc.ssts.to_vec();
        if let Some(added_ssts) = edit.ssts_added {
            new_ssts.extend(added_ssts.iter().cloned());
        }

        if let Some(removed_ssts) = edit.ssts_removed
            && !removed_ssts.is_empty()
        {
            let removed_ids: HashSet<u64> = removed_ssts.iter().map(|d| d.filenum).collect();
            new_ssts.retain(|sst| !removed_ids.contains(&sst.filenum));
        }

        if let Some(next_seqnum) = edit.seqnum_limit {
            self.seqnum_limit
                .store(next_seqnum.get(), Ordering::Release);
        }

        if let Some(next_filenum) = edit.filenum_limit {
            self.filenum_limit.store(next_filenum, Ordering::Release);
        }

        let new_version = ManifestVersion {
            seqnum_limit: edit
                .seqnum_limit
                .unwrap_or_else(|| current_arc.seqnum_limit),
            filenum_limit: edit
                .filenum_limit
                .unwrap_or_else(|| current_arc.filenum_limit),
            ssts: new_ssts.into(),
            filepath: current_arc.filepath.clone(),
        };

        self.current_version.store(Arc::new(new_version));
    }

    async fn write_framed_edit(
        &self,
        writer: &mut ManifestWriter<F>,
        edit: &VersionEdit,
    ) -> io::Result<()> {
        // create a buffer that will be written to disk
        let mut buf = BytesMut::with_capacity(512);

        // reserve space for the frame prefix
        buf.put_bytes(0, MANIFEST_RECORD_PREFIX_SIZE);

        // create synchronous writer into scratch buffer
        let sync_writer = (&mut buf).writer();

        // serialize into scratch buffer writer
        bincode::serialize_into(sync_writer, edit)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // calculate length and checksum and store in frame prefix
        let data_len = (buf.len() - MANIFEST_RECORD_PREFIX_SIZE) as u32;
        let checksum = crc64(0, &buf[MANIFEST_RECORD_PREFIX_SIZE..]);
        buf[0..4].copy_from_slice(&data_len.to_le_bytes());
        buf[4..12].copy_from_slice(&checksum.to_le_bytes());

        let final_len = buf.len() as u64;

        // write the whole scratch buffer to the async writer at once
        writer.file.write_all_at(buf.freeze(), writer.pos).await.0?;
        // advance writer position past this record
        writer.pos += final_len;

        Ok(())
    }

    async fn decode_manifest_file_body(&self, writer: &mut ManifestWriter<F>) -> io::Result<()> {
        // read and apply all edits in the manifest file body
        let file_size = writer.file.size().await?;
        while writer.pos < file_size {
            let edit = Self::read_framed_edit(writer).await?;
            self.apply_to_mem_and_swap(edit);
        }
        Ok(())
    }

    async fn read_framed_edit(writer: &mut ManifestWriter<F>) -> io::Result<VersionEdit> {
        let mut current_read_pos = writer.pos;
        // read the prefix
        let prefix_buf = BytesMut::zeroed(MANIFEST_RECORD_PREFIX_SIZE);
        let (res, prefix_buf) = writer
            .file
            .read_exact_at(prefix_buf, current_read_pos)
            .await;
        res?;
        current_read_pos += MANIFEST_RECORD_PREFIX_SIZE as u64;

        // parse the prefix data
        let body_len = u32::from_le_bytes(prefix_buf[0..4].try_into().unwrap());
        let stored_checksum = u64::from_le_bytes(prefix_buf[4..12].try_into().unwrap());

        // read the body
        let body_buf = BytesMut::zeroed(body_len as usize);
        let (res, body_buf) = writer.file.read_exact_at(body_buf, current_read_pos).await;
        res?;
        current_read_pos += body_len as u64;

        // validate data with crc64 checksum
        let body_buf = body_buf.freeze();
        let computed_checksum = crc64(0, &body_buf);
        if stored_checksum != computed_checksum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Manifest record checksum mismatch",
            ));
        }

        let edit: VersionEdit = bincode::deserialize(&body_buf)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // advance the writer only when reading was successfull
        writer.pos = current_read_pos;

        Ok(edit)
    }

    async fn write_version_edit(
        &self,
        edit: VersionEdit,
        writer_guard: &mut tokio::sync::MutexGuard<'_, Option<ManifestWriter<F>>>,
    ) -> io::Result<()> {
        assert_manifest_writer_guard!(self, writer_guard);
        println!("Writing version edit {:?} on {:?}", edit, self);
        println!("Writer guard: {:?}", writer_guard);
        let mut writer = writer_guard.as_mut().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "Manifest writer not initialized")
        })?;

        // write into file, backed by in-mem scratch buffer
        self.write_framed_edit(&mut writer, &edit).await?;
        self.apply_to_mem_and_swap(edit);

        // sync all file metadata
        writer.file.sync_all().await?;
        println!("Finished writing version edit");
        Ok(())
    }

    async fn persist_seqnum_limit(
        &self,
        limit: SeqNum,
        writer_guard: &mut tokio::sync::MutexGuard<'_, Option<ManifestWriter<F>>>,
    ) -> io::Result<()> {
        assert_manifest_writer_guard!(self, writer_guard);
        let edit = VersionEdit::V1(VersionEditV1 {
            seqnum_limit: Some(limit),
            filenum_limit: None,
            ssts_added: None,
            ssts_removed: None,
        });
        self.write_version_edit(edit, writer_guard).await?;
        Ok(())
    }

    async fn persist_filenum_limit(
        &self,
        limit: u64,
        writer_guard: &mut tokio::sync::MutexGuard<'_, Option<ManifestWriter<F>>>,
    ) -> io::Result<()> {
        assert_manifest_writer_guard!(self, writer_guard);
        let edit = VersionEdit::V1(VersionEditV1 {
            seqnum_limit: None,
            filenum_limit: Some(limit),
            ssts_added: None,
            ssts_removed: None,
        });
        self.write_version_edit(edit, writer_guard).await?;
        Ok(())
    }

    /// Allocate a new [`SeqNum`] range for outside usage, like KV-store inserts.
    pub(crate) async fn seqnum_range(&self, size: u64) -> io::Result<std::ops::Range<SeqNum>> {
        loop {
            // check for shutdown
            if self.is_shutdown.load(Ordering::Acquire) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Manifest manager has already been shut down",
                ));
            }
            let current = self.seqnum_current.load(Ordering::Relaxed);
            let limit = self.seqnum_limit.load(Ordering::Relaxed);

            let new_current = current + size;

            let current_seqnum = current.try_into().expect("checked in range");
            let new_seqnum = new_current.try_into()?;

            if new_current <= limit {
                if self
                    .seqnum_current
                    .compare_exchange(current, new_current, Ordering::Release, Ordering::Relaxed)
                    .is_ok()
                {
                    let range = current_seqnum..new_seqnum;
                    return Ok(range);
                }
                continue;
            }

            // acquire exclusive lock for increasing the limit
            let mut writer_guard = self.writer.lock().await;

            // check for shutdown
            if self.is_shutdown.load(Ordering::Acquire) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Manifest manager has already been shut down",
                ));
            }

            // another thread increased limit while acquiring lock
            if self.seqnum_current.load(Ordering::Relaxed) + size
                <= self.seqnum_limit.load(Ordering::Relaxed)
            {
                continue;
            }

            // calculate new limit, so it fits the new value
            let new_limit = std::cmp::max(
                limit + (SEQNUM_LIMIT_STEP * 2),
                new_current + SEQNUM_LIMIT_STEP,
            )
            .try_into()?;

            self.persist_seqnum_limit(new_limit, &mut writer_guard)
                .await?;
            self.seqnum_current
                .store(new_seqnum.get(), Ordering::Release);

            let range = current_seqnum..new_seqnum;
            return Ok(range);
        }
    }

    /// Get a new file number, which is used for unique file names and ordering by time.
    /// This is a monotonically increasing function.
    pub(crate) async fn next_file_number(&self) -> io::Result<u64> {
        loop {
            // check for shutdown
            if self.is_shutdown.load(Ordering::Acquire) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Manifest manager has already been shut down",
                ));
            }
            let current = self.filenum_current.load(Ordering::Relaxed);
            let limit = self.filenum_limit.load(Ordering::Relaxed);

            let new_current = current + 1;

            if new_current <= limit {
                if self
                    .filenum_current
                    .compare_exchange(current, new_current, Ordering::Release, Ordering::Relaxed)
                    .is_ok()
                {
                    return Ok(current);
                }
                continue;
            }

            let mut writer_guard = self.writer.lock().await;
            // check for shutdown
            if self.is_shutdown.load(Ordering::Acquire) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Manifest manager has already been shut down",
                ));
            }

            // another thread increased limit while acquiring lock
            if self.filenum_current.load(Ordering::Relaxed) + 1
                <= self.filenum_limit.load(Ordering::Relaxed)
            {
                continue;
            }

            let new_limit = limit + FILENUM_LIMIT_STEP;
            self.persist_filenum_limit(new_limit, &mut writer_guard)
                .await?;
            self.filenum_current.store(new_current, Ordering::Release);

            return Ok(current);
        }
    }

    pub(crate) fn all_live_files(&self) -> HashSet<Arc<Path>> {
        let current_arc = self.current_version.load();

        let mut live = HashSet::new();
        live.insert(current_arc.filepath.clone());
        for sst in current_arc.ssts.iter() {
            live.insert(self.root_dir.join(sst.get_path()).into());
        }

        live
    }
}

#[cfg(test)]
mod tests {
    use crate::fio::VirtualFileSystem;

    use super::*;

    #[test]
    fn test_sst_get_path() {
        let cases = [
            (
                SstMetadata {
                    filenum: 242,
                    file_size: (2 << 10) + 0xDEADBEEF,
                    level: 1,
                    smallest_key: "apples".into(),
                    largest_key: "bananas".into(),
                },
                "ssts/l-1/242.sst",
            ),
            (
                SstMetadata {
                    filenum: 4012,
                    file_size: (2 << 12) - 42,
                    level: 4,
                    smallest_key: "cherries".into(),
                    largest_key: "mangos".into(),
                },
                "ssts/l-4/4012.sst",
            ),
            (
                SstMetadata {
                    filenum: 10502,
                    file_size: (2u64 << 12) - 2222,
                    level: 5,
                    smallest_key: "oranges".into(),
                    largest_key: "tomatoes".into(),
                },
                "ssts/l-5/10502.sst",
            ),
        ]
        .map(|(sst, path_str)| {
            let file_number = sst.filenum;
            let level = sst.level;
            (
                sst,
                // deletion is determined by `file_number` and `level`
                SstDeletion {
                    filenum: file_number,
                    level,
                },
                PathBuf::from(path_str),
            )
        });

        for (sst, deletion, path) in cases {
            assert_eq!(sst.get_path(), path);
            assert_eq!(deletion.get_path(), path);
        }
    }

    #[test]
    fn test_manifest_header_encode_decode() {
        let header = ManifestHeader::new(0);
        let mut header_buf = [0u8; ManifestHeader::SIZE];
        header.encode(&mut header_buf);
        let decoded = ManifestHeader::decode(&header_buf).unwrap();
        assert_eq!(header.file_number, decoded.file_number);
    }

    #[tokio::test]
    async fn test_manifest_manager() {
        let fs = VirtualFileSystem::new();
        let root_dir = "data";

        let first_range;
        let second_range;

        println!("Creating first manifest manager");
        {
            let range_size = SEQNUM_LIMIT_STEP + 10;
            let manifest_manager = ManifestManager::init(fs.clone(), root_dir).await.unwrap();
            first_range = manifest_manager.seqnum_range(range_size).await.unwrap();
            println!(
                "First manifest manager final state: {:#?}",
                manifest_manager
            );
            assert_eq!(first_range.end.get() - first_range.start.get(), range_size);
            manifest_manager.shutdown().await.unwrap();
        }

        println!("Creating second manifest manager");
        {
            let range_size = 100;
            let manifest_manager = ManifestManager::init(fs.clone(), root_dir).await.unwrap();
            second_range = manifest_manager.seqnum_range(range_size).await.unwrap();
            println!(
                "Second manifest manager final state: {:#?}",
                manifest_manager
            );
            assert_eq!(
                second_range.end.get() - second_range.start.get(),
                range_size
            );
            manifest_manager.shutdown().await.unwrap();
        }

        println!("Creating third manifest manager");
        {
            let manifest_manager = ManifestManager::init(fs.clone(), root_dir).await.unwrap();
            manifest_manager.flush_to_new_file().await.unwrap();
            let first_file_num = manifest_manager.next_file_number().await.unwrap();
            let second_file_num = manifest_manager.next_file_number().await.unwrap();
            let third_file_num = manifest_manager.next_file_number().await.unwrap();
            println!(
                "Third manifest manager final state: {:#?}",
                manifest_manager
            );
            let live_files = manifest_manager.all_live_files();
            println!("-- Live Files --");
            for lf in &live_files {
                println!("{:?}", lf);
            }

            assert!(first_file_num + 1 == second_file_num);
            assert!(second_file_num + 1 == third_file_num);
            assert_eq!(live_files.len(), 1);
            manifest_manager.shutdown().await.unwrap();
        }

        assert!(
            first_range.end == second_range.start,
            "seqnum ranges {:?} and {:?} should be continuous with graceful shutdowns!",
            first_range,
            second_range
        );
    }
}
