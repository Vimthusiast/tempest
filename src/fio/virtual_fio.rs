use std::{
    collections::BTreeMap,
    io,
    path::{Path, PathBuf},
    sync::Arc,
};

use async_trait::async_trait;
use futures::{StreamExt, stream::BoxStream};
use tokio::io::{AsyncRead, AsyncSeek, AsyncWrite};

use crate::fio::{FioDirEntry, FioFS, FioFile};

pub struct VirtualFile {
    data: Arc<std::sync::RwLock<Vec<u8>>>,
    pos: u64,
}

impl VirtualFile {
    fn new(data: Arc<std::sync::RwLock<Vec<u8>>>) -> Self {
        Self { data, pos: 0 }
    }
}

impl AsyncRead for VirtualFile {
    fn poll_read(
        mut self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
        buf: &mut tokio::io::ReadBuf<'_>,
    ) -> std::task::Poll<io::Result<()>> {
        let data = self
            .data
            .read()
            .map_err(|_| io::Error::new(io::ErrorKind::Other, "Poisoned lock"))?;
        let start = self.pos as usize;
        let end = std::cmp::min(start + buf.remaining(), data.len());
        // only read if there is something left to read
        if start < end {
            let slice = &data[start..end];
            buf.put_slice(slice);
            drop(data);
            self.pos = end as u64;
        }
        std::task::Poll::Ready(Ok(()))
    }
}

impl AsyncWrite for VirtualFile {
    fn poll_write(
        mut self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
        buf: &[u8],
    ) -> std::task::Poll<io::Result<usize>> {
        let mut data = self
            .data
            .write()
            .map_err(|_| io::Error::new(io::ErrorKind::Other, "Poisoned lock"))?;
        let end_pos = self.pos + buf.len() as u64;
        if end_pos > data.len() as u64 {
            data.resize(end_pos as usize, 0);
        }
        data[(self.pos as usize)..(end_pos as usize)].copy_from_slice(buf);
        drop(data);
        self.pos = end_pos;
        std::task::Poll::Ready(Ok(buf.len()))
    }

    fn poll_flush(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<io::Result<()>> {
        std::task::Poll::Ready(Ok(()))
    }

    fn poll_shutdown(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<io::Result<()>> {
        std::task::Poll::Ready(Ok(()))
    }
}

impl AsyncSeek for VirtualFile {
    fn start_seek(mut self: std::pin::Pin<&mut Self>, position: io::SeekFrom) -> io::Result<()> {
        let Some(new_pos) = (match position {
            io::SeekFrom::Start(offset) => {
                self.pos = offset;
                return Ok(());
            }
            io::SeekFrom::End(offset) => (self
                .data
                .read()
                .map_err(|_| io::Error::new(io::ErrorKind::Other, "Poisoned lock"))?
                .len() as u64)
                .checked_add_signed(offset),
            io::SeekFrom::Current(offset) => self.pos.checked_add_signed(offset),
        }) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Invalid seek input: Underflow",
            ));
        };
        self.pos = new_pos;
        Ok(())
    }

    fn poll_complete(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<io::Result<u64>> {
        std::task::Poll::Ready(Ok(self.pos))
    }
}

#[async_trait]
impl FioFile for VirtualFile {
    async fn sync_all(&mut self) -> io::Result<()> {
        // No-op, virtual file-system is always synced, there is no buffering or syscall
        Ok(())
    }

    async fn size(&self) -> io::Result<u64> {
        let data = self
            .data
            .read()
            .map_err(|_| io::Error::new(io::ErrorKind::Other, "Poisoned lock"))?;
        Ok(data.len() as u64)
    }
}

#[derive(Debug, Clone, Default)]
pub struct VirtualFileSystem {
    files: Arc<tokio::sync::RwLock<BTreeMap<PathBuf, Arc<std::sync::RwLock<Vec<u8>>>>>>,
}

impl VirtualFileSystem {
    pub fn new() -> Self {
        Default::default()
    }

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
        println!("Creating file {:?}", path);
        let mut files = self.files.write().await;
        let data = Arc::new(std::sync::RwLock::new(Vec::new()));
        files.insert(path, data.clone());

        Ok(VirtualFile::new(data))
    }

    async fn create_dir_all(&self, _path: &Path) -> io::Result<()> {
        // No-op, virtual file-system is has no hierarchy, so we don't manage any directory entries
        Ok(())
    }

    async fn sync_dir(&self, _path: &Path) -> io::Result<()> {
        Ok(())
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        let from = Self::normalize(from);
        let to = Self::normalize(to);
        println!("Renaming file {:?} to {:?}", from, to);
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
        println!("Reading directory {:?}", search_path);
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
    use tokio::io::{AsyncReadExt, AsyncSeekExt, AsyncWriteExt};

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

        // Create file
        vfs.create(old_path)
            .await
            .unwrap()
            .write_all(b"log data")
            .await
            .unwrap();

        // Rename file and sync parent directory
        vfs.rename(old_path, new_path).await.unwrap();
        vfs.sync_dir(&PathBuf::from("/")).await.unwrap();

        // Old file should be gone
        assert!(vfs.open(old_path).await.is_err());

        // New file should have data
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
