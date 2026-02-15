use std::{
    any::type_name,
    collections::HashSet,
    io,
    path::{Path, PathBuf},
};

use bytes::{BufMut, BytesMut};
use crc64::crc64;
use futures::StreamExt;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncSeekExt, AsyncWrite, AsyncWriteExt},
    pin,
};

use crate::{
    core::SeqNum,
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
    file_number: u64,
    file_size: u64,
    level: u8,
    smallest_key: Vec<u8>,
    largest_key: Vec<u8>,
}

impl SstMetadata {
    /// Returns the file system path for the SST this Metadata references.
    pub fn get_path(&self) -> PathBuf {
        get_sst_path(self.level, self.file_number)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SstDeletion {
    file_number: u64,
    level: u8,
}

impl SstDeletion {
    pub fn get_path(&self) -> PathBuf {
        get_sst_path(self.level, self.file_number)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct VersionEditV1 {
    next_sequence_number: SeqNum,
    next_file_number: u64,
    /// A list of new [`SstMetadata`] objects that register SST files to the [`Manifest`].
    added_ssts: Vec<SstMetadata>,
    removed_ssts: Vec<SstDeletion>,
}

/// A versioned list of all different version edits to the [`Manifest`].
#[derive(Serialize, Deserialize)]
#[repr(u16)]
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

#[derive(Default)]
pub struct Manifest {}

/// This header comes first in a manifest file.
#[derive(Debug)]
pub struct ManifestHeader {
    pub file_number: u64,
    pub filename: PathBuf,
}

impl ManifestHeader {
    /// Magic number as a first check for file validation.
    pub const MAGIC: &[u8; 8] = b"TMPS_MAN";

    /// Total size of the [`ManifestHeader`] after encoding.
    pub const SIZE: usize = 24;

    pub fn new(file_number: u64) -> Self {
        let filename = format!("MANIFEST-{}", file_number).into();
        Self {
            file_number,
            filename,
        }
    }

    pub fn get_filename(&self) -> &Path {
        &self.filename
    }

    pub fn encode(&self, buf: &mut [u8; Self::SIZE]) {
        // 1. Magic bytes
        buf[0..8].copy_from_slice(Self::MAGIC);

        // 2. Manifest ID / file number (little-endian)
        buf[8..16].copy_from_slice(&self.file_number.to_le_bytes());

        // 3. Calculate and store CRC64 checksum
        let bytes_to_hash = &buf[0..16];
        let checksum = crc64(0, bytes_to_hash);
        buf[16..24].copy_from_slice(&checksum.to_le_bytes());
    }

    pub fn decode(buf: &[u8; 24]) -> io::Result<Self> {
        let magic_bytes = &buf[0..8];
        if magic_bytes != Self::MAGIC {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Invalid magic number: not a manifest file. Expected {:?} but got {:?}.",
                    Self::MAGIC,
                    magic_bytes
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
pub struct ManifestManager<F: FioFS> {
    // -- Manager Data --
    manifest_dir: PathBuf,
    current_file: PathBuf,
    #[debug("{}", type_name::<F>())]
    fs: F,

    // -- Manifest Data --
    next_sequence_number: SeqNum,
    next_file_number: u64,
    ssts: Vec<SstMetadata>,
}

impl<F: FioFS> ManifestManager<F> {
    pub(crate) async fn init(fs: F, manifest_dir: impl Into<PathBuf>) -> io::Result<Self> {
        let manifest_dir = manifest_dir.into();
        fs.create_dir_all(&manifest_dir).await?;

        let mut res = Self {
            manifest_dir,
            current_file: PathBuf::new(),
            fs,

            next_sequence_number: SeqNum::START,
            next_file_number: 0,
            ssts: Vec::new(),
        };

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
            let mut files_with_header = Vec::new();
            for entry in entries {
                println!("Reading manifest header for {:?}", entry.path());
                let file = res.fs.open(entry.path()).await?;
                let mut file = Box::pin(file);
                // read the header
                let mut header_buf = [0u8; ManifestHeader::SIZE];
                file.read_exact(&mut header_buf).await?;
                let header = ManifestHeader::decode(&header_buf)?;
                files_with_header.push((header, file));
            }

            let (header, file) = files_with_header
                .iter_mut()
                .sorted_by_key(|(h, _f)| h.file_number)
                .last()
                .expect("we should have at least one file here");
            println!("Reapplying manifest file {:?}", header.get_filename());
            res.current_file = res.manifest_dir.join(header.get_filename());
            res.decode_manifest_file_body(file).await?;
            println!("Finished loading old data from {:?}", header.get_filename());
        } else {
            res.flush_to_new_file().await?;
        }

        Ok(res)
    }

    pub async fn flush_to_new_file(&mut self) -> io::Result<()> {
        let file_number = self.next_file_number;
        self.next_file_number = file_number + 1;

        let header = ManifestHeader::new(file_number);

        // setup scratch buffer
        let mut scratch = BytesMut::with_capacity(4096);

        // there will only be one edit at first
        let edit = VersionEditV1 {
            next_sequence_number: self.next_sequence_number,
            next_file_number: self.next_file_number,
            added_ssts: self.ssts.clone(),
            removed_ssts: vec![],
        };

        // compute the new file path
        self.current_file = self.manifest_dir.join(header.get_filename());
        println!("Flushing manifest to new file {:?}", self.current_file);

        // create the new file in fs
        let file = self.fs.create(&self.current_file).await?;
        pin!(file);

        // write the header
        let mut header_buf = [0u8; ManifestHeader::SIZE];
        header.encode(&mut header_buf);
        file.write(&header_buf).await?;

        // write the first large setup version edit
        self.write_framed_edit(&mut file, &mut scratch, &VersionEdit::V1(edit))
            .await?;

        // flush remaining bytes to file
        file.flush().await?;
        file.sync_all().await?;
        Ok(())
    }

    async fn write_framed_edit<W: AsyncWrite + Unpin + ?Sized>(
        &self,
        writer: &mut W,
        scratch: &mut BytesMut,
        edit: &VersionEdit,
    ) -> io::Result<()> {
        // clear the scratch buffer
        scratch.clear();

        // reserve space for the frame prefix
        scratch.put_bytes(0, MANIFEST_RECORD_PREFIX_SIZE);

        // create synchronous writer into scratch buffer
        let mut sync_writer = scratch.writer();

        // serialize into scratch buffer writer
        bincode::serialize_into(&mut sync_writer, edit)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // calculate length and checksum and store in frame prefix
        let data_len = (scratch.len() - MANIFEST_RECORD_PREFIX_SIZE) as u32;
        let checksum = crc64(0, &scratch[MANIFEST_RECORD_PREFIX_SIZE..]);
        scratch[0..4].copy_from_slice(&data_len.to_le_bytes());
        scratch[4..12].copy_from_slice(&checksum.to_le_bytes());

        // write the whole scratch buffer to the async writer at once
        writer.write_all(&scratch).await?;
        Ok(())
    }

    pub async fn decode_manifest_file_body<R: AsyncRead + Unpin + ?Sized>(
        &mut self,
        reader: &mut R,
    ) -> io::Result<()> {
        // read and apply the edits
        let mut scratch = Vec::new();
        while let Some(e) = Self::read_framed_edit(reader, &mut scratch).await? {
            self.apply_edit(e);
        }
        Ok(())
    }

    fn apply_edit(&mut self, edit: VersionEditV1) {
        println!("Applying edit: {:?}", edit);
        self.next_sequence_number = edit.next_sequence_number;
        self.next_file_number = edit.next_file_number;
        self.ssts.extend(edit.added_ssts);
        let removed_ids: HashSet<u64> = edit.removed_ssts.iter().map(|d| d.file_number).collect();
        self.ssts
            .retain(|sst| !removed_ids.contains(&sst.file_number));
    }

    async fn read_framed_edit<R: AsyncRead + Unpin + ?Sized>(
        reader: &mut R,
        scratch: &mut Vec<u8>,
    ) -> io::Result<Option<VersionEditV1>> {
        let mut header_buf = [0u8; MANIFEST_RECORD_PREFIX_SIZE];

        // peek at the first byte, to see if we have a clean EOF
        let n = reader.read(&mut header_buf[..1]).await?;
        if n == 0 {
            // clean EOF, finished reading
            return Ok(None);
        }

        // try reading remaining header bytes
        reader.read_exact(&mut header_buf[1..]).await.map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "Manifest truncated in header")
        })?;

        // parse the header data
        let data_len = u32::from_le_bytes(header_buf[0..4].try_into().unwrap());
        let stored_checksum = u64::from_le_bytes(header_buf[4..12].try_into().unwrap());

        // clear the scratch buffer
        scratch.clear();
        scratch.resize(data_len as usize, 0);

        reader.read_exact(scratch).await.map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Manifest truncated in record body",
            )
        })?;

        // validate data with crc64 checksum
        let computed_checksum = crc64(0, &scratch);
        if stored_checksum != computed_checksum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Manifest record checksum mismatch",
            ));
        }

        let edit: VersionEdit = bincode::deserialize(&scratch)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        let edit = edit.into_latest();

        Ok(Some(edit))
    }

    async fn write_version_edit(&mut self, edit: VersionEditV1) -> io::Result<()> {
        println!("Writing version edit {:?}", edit);
        let mut scratch = BytesMut::with_capacity(4096);
        let file = self.fs.open(&self.current_file).await?;
        pin!(file);
        file.seek(io::SeekFrom::End(0)).await?;
        self.write_framed_edit(&mut file, &mut scratch, &VersionEdit::V1(edit))
            .await?;
        println!("Finished writing version edit");
        Ok(())
    }

    /// Allocate a new [`SeqNum`] range for outside usage, like KV-store inserts.
    pub(crate) async fn seqnum_range(&mut self, size: u64) -> io::Result<std::ops::Range<SeqNum>> {
        let next_seqnum = self.next_sequence_number;
        self.next_sequence_number = self
            .next_sequence_number
            .increment(size)
            // TODO: Create custom error type as TempestError variant
            .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "SeqNum overflow"))?;

        let range = next_seqnum..self.next_sequence_number;
        self.write_version_edit(VersionEditV1 {
            next_sequence_number: self.next_sequence_number,
            next_file_number: self.next_file_number,
            added_ssts: Vec::new(),
            removed_ssts: Vec::new(),
        })
        .await?;

        Ok(range)
    }

    /// Get a new file number, which is used for unique file names and ordering by time.
    /// This is a monotonically increasing function.
    pub(crate) async fn next_file_number(&mut self) -> io::Result<u64> {
        let next_file_number = self.next_file_number;
        self.next_file_number += 1;

        self.write_version_edit(VersionEditV1 {
            next_sequence_number: self.next_sequence_number,
            next_file_number: self.next_file_number,
            added_ssts: Vec::new(),
            removed_ssts: Vec::new(),
        })
        .await?;

        Ok(next_file_number)
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
                    file_number: 242,
                    file_size: (2 << 10) + 0xDEADBEEF,
                    level: 1,
                    smallest_key: "apples".into(),
                    largest_key: "bananas".into(),
                },
                "ssts/l-1/242.sst",
            ),
            (
                SstMetadata {
                    file_number: 4012,
                    file_size: (2 << 12) - 42,
                    level: 4,
                    smallest_key: "cherries".into(),
                    largest_key: "mangos".into(),
                },
                "ssts/l-4/4012.sst",
            ),
            (
                SstMetadata {
                    file_number: 10502,
                    file_size: (2u64 << 12) - 2222,
                    level: 5,
                    smallest_key: "oranges".into(),
                    largest_key: "tomatoes".into(),
                },
                "ssts/l-5/10502.sst",
            ),
        ]
        .map(|(sst, path_str)| {
            let file_number = sst.file_number;
            let level = sst.level;
            (
                sst,
                // deletion is determined by `file_number` and `level`
                SstDeletion { file_number, level },
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
        let manifest_dir = "data/manifest";

        let first_range;
        let second_range;

        println!("Creating first manifest manager");
        {
            let mut manifest_manager = ManifestManager::init(fs.clone(), manifest_dir)
                .await
                .unwrap();
            first_range = manifest_manager.seqnum_range(24).await.unwrap();
            println!(
                "First manifest manager final state: {:#?}",
                manifest_manager
            );
            assert_eq!(first_range.end.get() - first_range.start.get(), 24);
        }

        println!("Creating second manifest manager");
        {
            let mut manifest_manager = ManifestManager::init(fs.clone(), manifest_dir)
                .await
                .unwrap();
            second_range = manifest_manager.seqnum_range(24).await.unwrap();
            println!(
                "Second manifest manager final state: {:#?}",
                manifest_manager
            );
            assert_eq!(second_range.end.get() - second_range.start.get(), 24);
        }

        println!("Creating third manifest manager");
        {
            let mut manifest_manager = ManifestManager::init(fs.clone(), manifest_dir)
                .await
                .unwrap();
            manifest_manager.flush_to_new_file().await.unwrap();
            let first_file_num = manifest_manager.next_file_number().await.unwrap();
            let second_file_num = manifest_manager.next_file_number().await.unwrap();
            let third_file_num = manifest_manager.next_file_number().await.unwrap();
            println!(
                "Third manifest manager final state: {:#?}",
                manifest_manager
            );
            assert_eq!(first_file_num + 1, second_file_num);
            assert_eq!(second_file_num + 1, third_file_num);
        }

        assert_eq!(
            first_range.end, second_range.start,
            "Ranges should be continuous"
        );
    }
}
