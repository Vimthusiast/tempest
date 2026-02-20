use std::{
    collections::BTreeMap,
    io::{self},
    path::{Path, PathBuf},
    sync::Arc,
};

use async_trait::async_trait;
use bytes::{Bytes, BytesMut};
use futures::{StreamExt, stream::BoxStream};
use tokio::sync::RwLock;

use crate::fio::{FioDirEntry, FioFS, FioFile};

pub struct VirtualFile(Arc<RwLock<Vec<u8>>>);

impl VirtualFile {
    fn new(data: Arc<RwLock<Vec<u8>>>) -> Self {
        Self(data)
    }
}

#[async_trait(?Send)]
impl FioFile for VirtualFile {
    async fn sync_all(&mut self) -> io::Result<()> {
        // No-op, virtual file-system is always synced, there is no buffering or syscall involved
        Ok(())
    }

    async fn size(&self) -> io::Result<u64> {
        let data = self.0.read().await;
        Ok(data.len() as u64)
    }

    async fn read_exact_at(&self, mut buf: BytesMut, pos: u64) -> (io::Result<()>, BytesMut) {
        let data = self.0.read().await;

        let start = pos as usize;
        let end = start + buf.len();

        if end > data.len() {
            return (
                Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "Unexpected end of file",
                )),
                buf,
            );
        }

        buf.copy_from_slice(&data[start..end]);

        (Ok(()), buf)
    }

    async fn write_all_at(&self, buf: Bytes, pos: u64) -> (io::Result<()>, Bytes) {
        if buf.len() == 0 {
            return (Ok(()), buf);
        }

        let mut data = self.0.write().await;

        let start = pos as usize;
        let end = start + buf.len();

        if data.len() < end {
            data.resize(end, 0);
        }

        data[start..end].copy_from_slice(&buf);

        (Ok(()), buf)
    }
}

#[derive(Debug, Clone, Default)]
pub struct VirtualFileSystem {
    files: Arc<RwLock<BTreeMap<PathBuf, Arc<RwLock<Vec<u8>>>>>>,
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

#[async_trait(?Send)]
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
        let data = Arc::new(RwLock::new(Vec::new()));
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

    #[tokio::test]
    async fn test_path_normalization_and_basic_io() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("test.txt");
        let path_rel = Path::new("./test.txt");

        let data: &[u8] = "hello world".as_ref();

        // Create and write
        let file = vfs.create(path).await.unwrap();
        file.write_all_at(Bytes::from(data), 0).await.0.unwrap();

        // Open via different but equivalent path
        let file_rel = vfs.open(path_rel).await.unwrap();
        let buf = BytesMut::zeroed(data.len());
        let (res, buf) = file_rel.read_exact_at(buf, 0).await;
        res.unwrap();

        assert_eq!(buf, data);
    }

    #[tokio::test]
    async fn test_rename_behavior() {
        let vfs = VirtualFileSystem::default();
        let old_path = Path::new("old.log");
        let new_path = Path::new("new.log");
        let data = b"log data".as_ref();

        // Create and write to file
        let file = vfs.create(old_path).await.unwrap();
        file.write_all_at(Bytes::from(data), 0).await.0.unwrap();

        // Rename file and sync parent directory
        vfs.rename(old_path, new_path).await.unwrap();
        vfs.sync_dir(&PathBuf::from("/")).await.unwrap();

        // Old file should be gone
        assert!(vfs.open(old_path).await.is_err());

        // New file should have data
        let file = vfs.open(new_path).await.unwrap();
        let buf = BytesMut::zeroed(data.len());
        let (res, buf) = file.read_exact_at(buf, 0).await;
        res.unwrap();
        assert_eq!(buf, data);
    }

    #[tokio::test]
    async fn test_positional_overwrite_and_holes() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("sparse.bin");
        let file = vfs.create(path).await.unwrap();
        let data = b"ABC".as_ref();

        // Write "AAA" at offset 5. This should automatically resize the VFS vec
        // and leave indices 0..5 as zeros (creating a "hole").
        file.write_all_at(Bytes::from(data), 5).await.0.unwrap();

        let read_file = vfs.open(path).await.unwrap();
        assert_eq!(read_file.size().await.unwrap(), 8);

        let buf = BytesMut::zeroed(8);
        let (res, buf) = read_file.read_exact_at(buf, 0).await;
        res.unwrap();

        assert_eq!(&buf[0..5], &[0, 0, 0, 0, 0]);
        assert_eq!(&buf[5..8], data);
    }

    #[tokio::test]
    async fn test_read_out_of_bounds() {
        let vfs = VirtualFileSystem::default();
        let file = vfs.create(Path::new("small.bin")).await.unwrap();

        // Write 2 bytes
        file.write_all_at(Bytes::from(b"hi".as_ref()), 0)
            .await
            .0
            .unwrap();

        // Try to read 5 bytes at offset 0 (too many)
        let buf = BytesMut::zeroed(5);
        let (res, _) = file.read_exact_at(buf, 0).await;

        assert!(res.is_err());
        assert_eq!(res.unwrap_err().kind(), io::ErrorKind::UnexpectedEof);
    }

    #[tokio::test]
    async fn test_complex_path_resolution() {
        let vfs = VirtualFileSystem::default();
        // Path: /a/b/../c/./d.txt  => should be /a/c/d.txt
        let complex = Path::new("a/b/../c/./d.txt");
        let file = vfs.create(complex).await.unwrap();
        file.write_all_at(Bytes::from(b"nested".as_ref()), 0)
            .await
            .0
            .unwrap();

        let simple = Path::new("/a/c/d.txt");
        let opened = vfs.open(simple).await.unwrap();
        assert_eq!(opened.size().await.unwrap(), 6);
    }

    #[tokio::test]
    async fn test_concurrent_read_write() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("shared.db");
        vfs.create(path).await.unwrap();

        let writer = vfs.open(path).await.unwrap();
        let reader = vfs.open(path).await.unwrap();

        // Write at offset 0
        writer
            .write_all_at(Bytes::from_static(b"data"), 0)
            .await
            .0
            .unwrap();

        // Reader should see it immediately because they share the same Arc<RwLock<Vec<u8>>>
        let buf = BytesMut::zeroed(4);
        let (res, buf) = reader.read_exact_at(buf, 0).await;
        res.unwrap();
        assert_eq!(&buf[..], b"data");
    }

    #[tokio::test]
    async fn test_read_dir_vfs() {
        let vfs = VirtualFileSystem::default();

        let files = [
            "/data/manifest.log",
            "/data/sst/001.sst",
            "/data/sst/002.sst",
            "/data/tmp/old/trash.bin",
        ]
        .map(PathBuf::from);

        for path in files {
            let file = vfs.create(&path).await.unwrap();
            file.write_all_at(Bytes::from_static(b"test"), 0)
                .await
                .0
                .unwrap();
        }

        let mut stream = vfs.read_dir(Path::new("/data")).await.unwrap();
        let mut entries = Vec::new();
        while let Some(res) = stream.next().await {
            entries.push(res.unwrap());
        }

        // manifest.log, sst (dir), tmp (dir)
        assert_eq!(entries.len(), 3);

        assert!(
            entries
                .iter()
                .any(|e| e.path.to_str().unwrap() == "/data/manifest.log" && !e.is_dir)
        );
        assert!(
            entries
                .iter()
                .any(|e| e.path.to_str().unwrap() == "/data/sst" && e.is_dir)
        );
        assert!(
            entries
                .iter()
                .any(|e| e.path.to_str().unwrap() == "/data/tmp" && e.is_dir)
        );
    }
}
