use std::{
    collections::BTreeMap,
    io,
    path::{Path, PathBuf},
    sync::Arc,
};

use async_trait::async_trait;
use futures::{StreamExt, stream::BoxStream};
use itertools::Itertools;
use tokio::sync::RwLock;

use crate::fio::{FioDirEntry, FioFS, FioFile};

pub struct VirtualFile {
    data: Arc<RwLock<Vec<u8>>>,
    pos: usize,
}

impl VirtualFile {
    fn new(data: Arc<RwLock<Vec<u8>>>) -> Self {
        Self { data, pos: 0 }
    }
}

#[async_trait]
impl FioFile for VirtualFile {
    async fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let mut data = self.data.write().await;
        let end_pos = self.pos + buf.len();
        if end_pos > data.len() {
            data.resize(end_pos, 0);
        }
        data[self.pos..end_pos].copy_from_slice(buf);
        self.pos = end_pos;
        Ok(buf.len())
    }

    async fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.write(buf).await?;
        Ok(())
    }

    async fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        let data = self.data.read().await;
        let start = self.pos;
        if start >= data.len() {
            Ok(0)
        } else {
            self.pos = data.len();
            buf.extend_from_slice(&data[start..]);
            Ok(self.pos - start)
        }
    }

    async fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let data = self.data.read().await;
        let start = self.pos;
        let remaining = data.len() - start;
        if remaining < buf.len() {
            Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "Unexpected end of file",
            ))
        } else {
            self.pos += buf.len();
            buf.copy_from_slice(&data[start..self.pos]);
            Ok(buf.len())
        }
    }

    async fn sync_all(&mut self) -> io::Result<()> {
        // No-op, virtual file-system is always synced, there is no buffering or syscall
        Ok(())
    }

    async fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        let Some(new_pos) = (match pos {
            io::SeekFrom::Start(offset) => {
                self.pos = offset as usize;
                return Ok(self.pos as u64);
            }
            io::SeekFrom::End(offset) => self
                .data
                .read()
                .await
                .len()
                .checked_add_signed(offset as isize),
            io::SeekFrom::Current(offset) => self.pos.checked_add_signed(offset as isize),
        }) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Invalid seek input: Underflow",
            ));
        };
        self.pos = new_pos;
        Ok(self.pos as u64)
    }

    async fn size(&self) -> io::Result<u64> {
        let data = self.data.read().await;
        Ok(data.len() as u64)
    }
}

#[derive(Debug, Clone, Default)]
pub struct VirtualFileSystem {
    files: Arc<RwLock<BTreeMap<PathBuf, Arc<RwLock<Vec<u8>>>>>>,
}

impl VirtualFileSystem {
    fn normalize(path: impl AsRef<Path>) -> PathBuf {
        let mut components = Vec::new();

        for comp in path.as_ref().components() {
            match comp {
                std::path::Component::Prefix(_) => panic!(
                    "Path prefix in VFS is not supported! Got path {:?}.",
                    path.as_ref()
                ),
                std::path::Component::RootDir => {} // Ignore, we add it at the end
                std::path::Component::Normal(c) => components.push(c),
                std::path::Component::ParentDir => {
                    // Navigate back
                    let old = components.pop();
                    debug_assert!(
                        matches!(old, Some(_)),
                        "Parent directory navigation at root!"
                    );
                }
                std::path::Component::CurDir => {} // Skip "."
            }
        }

        let mut result = PathBuf::from("/");
        result.extend(components);
        result
    }
}

#[async_trait]
impl FioFS for VirtualFileSystem {
    type File = VirtualFile;

    async fn open(&self, path: &Path) -> io::Result<Self::File> {
        let path = Self::normalize(path);
        let files = self.files.read().await;
        let data = files
            .get(&path)
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "File not found"))?;

        Ok(VirtualFile::new(data.clone()))
    }

    async fn create(&self, path: &Path) -> io::Result<Self::File> {
        let path = Self::normalize(path);
        let mut files = self.files.write().await;
        let data = Arc::new(RwLock::new(Vec::new()));
        files.insert(path, data.clone());

        Ok(VirtualFile::new(data))
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        let from = Self::normalize(from);
        let to = Self::normalize(to);
        let mut files = self.files.write().await;
        let data = files
            .remove(&from)
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "Source file not found"))?;

        files.insert(to, data);
        Ok(())
    }

    async fn read_dir(
        &self,
        path: &Path,
    ) -> io::Result<BoxStream<'static, io::Result<FioDirEntry>>> {
        let search_path = Self::normalize(path);
        let mut prefix = search_path.to_string_lossy().into_owned();
        if !prefix.ends_with('/') {
            prefix.push('/');
        }

        let files = self.files.read().await;
        let mut entries = BTreeMap::new();

        for file_path in files.keys() {
            let file_str = file_path.to_string_lossy();

            if file_str.starts_with(&prefix) && *file_path != search_path {
                let relative = &file_str[prefix.len()..];

                let (name, is_dir) = if let Some(idx) = relative.find('/') {
                    (&relative[..idx], true)
                } else {
                    (relative, false)
                };

                let mut entry_path = PathBuf::from(&prefix);
                entry_path.push(name);

                if !entries.contains_key(&entry_path) {
                    entries.insert(
                        entry_path.clone(),
                        FioDirEntry {
                            path: entry_path,
                            is_dir,
                        },
                    );
                }
            }
        }

        Ok(futures::stream::iter(entries.into_values().map(Ok)).boxed())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fio::{FioFS, FioFile};
    use io::SeekFrom;

    #[tokio::test]
    async fn test_normalization_and_basic_io() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("test.txt");

        // Create and write
        let mut file = vfs.create(path).await.unwrap();
        file.write_all(b"hello world").await.unwrap();

        // Open via different but equivalent path
        let mut file_rel = vfs.open(Path::new("./test.txt")).await.unwrap();
        let mut buf = Vec::new();
        file_rel.read_to_end(&mut buf).await.unwrap();

        assert_eq!(buf, b"hello world");
    }

    #[tokio::test]
    async fn test_independent_cursors() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("shared.db");

        vfs.create(path)
            .await
            .unwrap()
            .write_all(b"0123456789")
            .await
            .unwrap();

        let mut h1 = vfs.open(path).await.unwrap();
        let mut h2 = vfs.open(path).await.unwrap();

        // Move h1 cursor
        h1.seek(SeekFrom::Start(5)).await.unwrap();
        let mut buf1 = vec![0; 1];
        h1.read_exact(&mut buf1).await.unwrap();

        // h2 should still be at 0
        let mut buf2 = vec![0; 1];
        h2.read_exact(&mut buf2).await.unwrap();

        assert_eq!(buf1, b"5");
        assert_eq!(buf2, b"0");
    }

    #[tokio::test]
    async fn test_rename_behavior() {
        let vfs = VirtualFileSystem::default();
        let old_path = Path::new("old.log");
        let new_path = Path::new("new.log");

        vfs.create(old_path)
            .await
            .unwrap()
            .write_all(b"log data")
            .await
            .unwrap();

        // Rename
        vfs.rename(old_path, new_path).await.unwrap();

        // Old should be gone
        assert!(vfs.open(old_path).await.is_err());

        // New should have data
        let mut file = vfs.open(new_path).await.unwrap();
        let mut buf = Vec::new();
        file.read_to_end(&mut buf).await.unwrap();
        assert_eq!(buf, b"log data");
    }

    #[tokio::test]
    async fn test_seek_and_overwrite() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("sparse.bin");
        let mut file = vfs.create(path).await.unwrap();

        // Write "AAA" at offset 5
        file.seek(SeekFrom::Start(5)).await.unwrap();
        file.write_all(b"AAA").await.unwrap();

        let mut read_file = vfs.open(path).await.unwrap();
        let mut buf = Vec::new();
        read_file.read_to_end(&mut buf).await.unwrap();

        // Should be [0,0,0,0,0, 'A','A','A']
        assert_eq!(buf.len(), 8);
        assert_eq!(&buf[0..5], &[0, 0, 0, 0, 0]);
        assert_eq!(&buf[5..8], b"AAA");
    }

    #[tokio::test]
    async fn test_seek_underflow_error() {
        let vfs = VirtualFileSystem::default();
        let mut file = vfs.create(Path::new("test")).await.unwrap();

        // Seek to -1 from Start
        let result = file.seek(SeekFrom::Current(-1)).await;
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().kind(), io::ErrorKind::InvalidInput);
    }

    #[tokio::test]
    async fn test_complex_path_resolution() {
        let vfs = VirtualFileSystem::default();
        // Path: /a/b/../c/./d.txt  => should be /a/c/d.txt
        let complex = Path::new("a/b/../c/./d.txt");
        vfs.create(complex)
            .await
            .unwrap()
            .write_all(b"nested")
            .await
            .unwrap();

        let simple = Path::new("/a/c/d.txt");
        assert!(vfs.open(simple).await.is_ok());
    }

    #[tokio::test]
    async fn test_file_size_reporting() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("size_test.db");

        // 1. New file should be size 0
        let mut file = vfs.create(path).await.unwrap();
        assert_eq!(file.size().await.unwrap(), 0);

        // 2. Write data and check size
        file.write_all(b"tempest").await.unwrap();
        assert_eq!(file.size().await.unwrap(), 7);

        // 3. Seek past end and write (creating a "hole")
        file.seek(io::SeekFrom::Start(10)).await.unwrap();
        file.write_all(b"db").await.unwrap();

        // Total size should be 10 (offset) + 2 (length of "db") = 12
        assert_eq!(file.size().await.unwrap(), 12);

        // 4. Verify new handles see the same size
        let file_readonly = vfs.open(path).await.unwrap();
        assert_eq!(file_readonly.size().await.unwrap(), 12);
    }

    #[tokio::test]
    async fn test_read_dir_vfs() {
        let vfs = VirtualFileSystem::default();

        // Set up a hierarchy:
        let files = [
            "/data/manifest.log",
            "/data/sst/001.sst",
            "/data/sst/002.sst",
            "/data/tmp/old/trash.bin",
        ]
        .map(PathBuf::from);
        for path in files {
            vfs.create(&path)
                .await
                .unwrap()
                .write("some-test-data".as_bytes())
                .await
                .unwrap();
        }

        // 1. Read /data/
        let mut stream = vfs.read_dir(Path::new("/data")).await.unwrap();
        let mut entries = Vec::new();
        while let Some(res) = stream.next().await {
            entries.push(res.unwrap());
        }

        // Should find: manifest.log (file), sst (dir), tmp (dir)
        assert_eq!(entries.len(), 3);

        let manifest = entries
            .iter()
            .find(|e| e.path.to_str().unwrap().contains("manifest.log"))
            .unwrap();
        assert!(!manifest.is_dir);

        let sst = entries
            .iter()
            .find(|e| e.path.to_str().unwrap().contains("sst"))
            .unwrap();
        assert!(sst.is_dir);
        // Ensure the path is exactly "/data/sst"
        assert_eq!(sst.path.to_str().unwrap(), "/data/sst");

        // 2. Read /data/sst/
        let mut stream = vfs.read_dir(Path::new("/data/sst")).await.unwrap();
        let mut sst_entries = Vec::new();
        while let Some(res) = stream.next().await {
            sst_entries.push(res.unwrap());
        }

        // Should find 001.sst and 002.sst
        assert_eq!(sst_entries.len(), 2);
        assert!(sst_entries.iter().all(|e| !e.is_dir));

        // 3. Test non-existent or empty dir
        let mut stream = vfs.read_dir(Path::new("/empty")).await.unwrap();
        assert!(stream.next().await.is_none());
    }
}
