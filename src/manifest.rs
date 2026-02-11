use std::{
    ops::Range,
    path::{Path, PathBuf},
    sync::Arc,
};

use async_trait::async_trait;
use tokio::{
    fs,
    io::{self, AsyncWriteExt},
    sync::RwLock,
};

use crate::{
    core::{DecodeError, SliceReader, TempestError, TempestReader, TempestWriter},
    kv::SeqNum,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    next_seqnum: SeqNum,
}

impl Manifest {
    pub(crate) fn encode<W: TempestWriter>(&self, writer: &mut W) {
        writer.write_u64(self.next_seqnum.get());
    }

    pub(crate) fn decode<'a, R: TempestReader<'a>>(reader: &mut R) -> Result<Self, TempestError> {
        let seqnum = reader.read_u64()?;
        let seqnum = SeqNum::new(seqnum).ok_or_else(|| TempestError::InvalidSeqNum(seqnum))?;

        if !reader.is_eof() {
            return Err(TempestError::DecodeError(DecodeError::RemainingBytes(
                reader.bytes_left(),
                "Manifest reader",
            )));
        }

        Ok(Self {
            next_seqnum: seqnum,
        })
    }
}

impl Default for Manifest {
    fn default() -> Self {
        Self {
            next_seqnum: SeqNum::START,
        }
    }
}

#[async_trait]
pub trait ManifestManager {
    /// Allocate a range of `count` [`SeqNum`]s for use. Returns the range that was reserved.
    /// The implementation must ensure, that this range is never returned again from other calls.
    /// Usually bumps a counter by `count` and returns the range from `old_count..new_count`.
    async fn allocate_seqnum_range(&self, count: u64) -> Result<Range<SeqNum>, TempestError>;
}

#[derive(Default)]
pub struct InMemoryManifestManager {
    current_manifest: Arc<RwLock<Manifest>>,
}

impl InMemoryManifestManager {
    pub fn new() -> Self {
        Default::default()
    }
}

#[async_trait]
impl ManifestManager for InMemoryManifestManager {
    async fn allocate_seqnum_range(&self, count: u64) -> Result<Range<SeqNum>, TempestError> {
        let mut manifest_guard = self.current_manifest.write().await;

        let start = manifest_guard.next_seqnum;
        let end = start.get() + count;
        let end = SeqNum::new(end).ok_or_else(|| TempestError::InvalidSeqNum(end))?;
        manifest_guard.next_seqnum = end;

        Ok(start..end)
    }
}

pub const MANIFEST_FILE_NAME: &'static str = "MANIFEST";

pub struct FileSystemManifestManager {
    current_manifest: Arc<RwLock<Manifest>>,
    manifest_path: PathBuf,
    tmp_manifest_path: PathBuf,
}

impl FileSystemManifestManager {
    /// Opens up the file-system based [`ManifestManager`] implementation.
    /// The [`Manifest`]-file is stored as [`MANIFEST_FILE_NAME`] within the `data_dir` directory.
    pub async fn open(data_dir: impl AsRef<Path>) -> Result<Self, TempestError> {
        let manifest_path = data_dir.as_ref().join(MANIFEST_FILE_NAME);
        let tmp_manifest_path = manifest_path.join(".tmp");

        println!("Reading Manifest file: {:?}.", &manifest_path);
        let manifest = match fs::read(&manifest_path).await {
            Ok(file) => {
                println!("Found Manifest file; begin decoding.");
                let mut reader = SliceReader::new(&file);
                Manifest::decode(&mut reader)?
            }
            Err(err) => {
                if matches!(err.kind(), std::io::ErrorKind::NotFound) {
                    println!("Manifest file not found; creating {:?}.", &manifest_path);
                    // file does not exist, create manifest
                    Manifest::default()
                } else {
                    return Err(err.into());
                }
            }
        };

        let mut manifest_bytes = Vec::new();
        manifest.encode(&mut manifest_bytes);

        // write back the manifest file
        fs::write(&manifest_path, manifest_bytes).await?;

        let current_manifest = RwLock::new(manifest).into();

        Ok(Self {
            current_manifest,
            manifest_path,
            tmp_manifest_path,
        })
    }

    async fn write_manifest(&self, manifest: &Manifest) -> io::Result<()> {
        // encode the manifest into the buffer
        let mut manifest_bytes = Vec::new();
        manifest.encode(&mut manifest_bytes);

        // write out the buffer to a temporary file
        let mut tmp_file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(&self.tmp_manifest_path)
            .await?;
        tmp_file.write_all(&manifest_bytes).await?;
        tmp_file.sync_all().await?;
        drop(tmp_file);

        // rename file at once to prevent partial writes
        fs::rename(&self.tmp_manifest_path, &self.manifest_path).await?;

        Ok(())
    }
}

#[async_trait]
impl ManifestManager for FileSystemManifestManager {
    async fn allocate_seqnum_range(&self, count: u64) -> Result<Range<SeqNum>, TempestError> {
        let mut manifest_guard = self.current_manifest.write().await;

        let start = manifest_guard.next_seqnum;
        let end = start.get() + count;
        let end = SeqNum::new(end).ok_or_else(|| TempestError::InvalidSeqNum(end))?;

        // create modified manifest
        let mut new_manifest = manifest_guard.clone();
        new_manifest.next_seqnum = end;

        // try to persist manifest to fs
        self.write_manifest(&new_manifest).await?;

        // on success, swap out the old manifest with the new one
        *manifest_guard = new_manifest;

        // return the allocated range
        Ok(start..end)
    }
}

#[cfg(test)]
mod tests {
    use crate::core::SliceReader;

    use super::*;
    #[test]
    fn test_manifest_encode_decode() {
        let manifest = Manifest::default();
        let mut buf = Vec::new();
        manifest.encode(&mut buf);
        let mut reader = SliceReader::new(&buf);
        let decoded = Manifest::decode(&mut reader).unwrap();
        assert_eq!(decoded, manifest);
    }

    #[tokio::test]
    async fn test_in_memory_manifest_manager() {
        let manifest_manager = InMemoryManifestManager::new();
        let range1 = manifest_manager.allocate_seqnum_range(16).await.unwrap();
        assert_eq!(range1.end.get(), range1.start.get() + 16);
        // test continuity
        let range2 = manifest_manager.allocate_seqnum_range(4).await.unwrap();
        assert_eq!(range2.start, range1.end);

        // this will fail
        let range3_result = manifest_manager
            .allocate_seqnum_range(SeqNum::MAX.get())
            .await;
        assert!(
            range3_result.is_err(),
            "this should fail, as it would exceed the valid seqnum range"
        );

        // this will succeed again, because range3 did not bump the pointer
        let _range4 = manifest_manager.allocate_seqnum_range(4).await.unwrap();
    }
}
