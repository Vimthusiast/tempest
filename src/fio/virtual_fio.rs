use std::{
    collections::BTreeMap,
    io::{self},
    path::{Path, PathBuf},
    sync::Arc,
};

use async_trait::async_trait;
use futures::{StreamExt, stream::BoxStream};
use tokio::sync::RwLock;
use tokio_uring::buf::{BoundedBuf, BoundedBufMut};

use crate::fio::{FioDirEntry, FioFS, FioFile, OpenOptions};

#[derive(Debug, Default)]
#[debug("VirtualFile({:p})", Arc::as_ptr(_0))]
pub struct VirtualFile(Arc<RwLock<Vec<u8>>>);

#[async_trait(?Send)]
impl FioFile for VirtualFile {
    async fn sync_all(&self) -> io::Result<()> {
        // No-op, virtual file-system is always synced, there is no buffering or syscall involved
        Ok(())
    }

    async fn size(&self) -> io::Result<u64> {
        let data = self.0.read().await;
        Ok(data.len() as u64)
    }

    async fn read_exact_at<T: BoundedBufMut>(&self, mut buf: T, pos: u64) -> (io::Result<()>, T) {
        let space = buf.bytes_init();

        // no bytes to read
        if space == 0 {
            return (Ok(()), buf);
        }

        let start = pos as usize;
        let end = start + space;

        let data = self.0.read().await;

        if end > data.len() {
            return (
                Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "unexpected end of file",
                )),
                buf,
            );
        }

        buf.put_slice(&data[start..end]);

        (Ok(()), buf)
    }

    async fn write_all_at<T: BoundedBuf>(&self, buf: T, pos: u64) -> (io::Result<()>, T) {
        let len = buf.bytes_init();
        if len == 0 {
            return (Ok(()), buf);
        }

        let mut data = self.0.write().await;

        let start = pos as usize;
        let end = match start.checked_add(len) {
            Some(e) => e,
            None => {
                return (
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "position overflow",
                    )),
                    buf,
                );
            }
        };

        if data.len() < end {
            data.resize(end, 0);
        }

        // SAFETY: We got the initialized `len` of `buf` above.
        let src_slice = unsafe { std::slice::from_raw_parts(buf.stable_ptr(), len) };

        data[start..end].copy_from_slice(&src_slice);

        (Ok(()), buf)
    }
}

#[derive(Debug, Clone, Default)]
pub struct VirtualFileSystem {
    #[debug("{:p}", Arc::as_ptr(files))]
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
                    "path prefix in VFS is not supported! Got path {:?}.",
                    path.as_ref()
                ),
                std::path::Component::RootDir => {} // Ignore, we add it at the end
                std::path::Component::Normal(c) => components.push(c),
                std::path::Component::ParentDir => {
                    // Navigate back
                    let old = components.pop();
                    debug_assert!(
                        matches!(old, Some(_)),
                        "parent directory navigation at root!"
                    );
                }
                std::path::Component::CurDir => {} // Skip "."
            }
        }

        let mut result = PathBuf::from("/");
        result.extend(components);
        result
    }

    /// Debug print this file systems contents if trace verbosity is [`Level::DEBUG`] or higher.
    ///
    /// # Panics
    ///
    /// Panics if any of the internal files are still accesses.
    ///
    /// [`Level::DEBUG`]: tracing::Level::DEBUG
    #[cfg(test)]
    pub fn debug(&self) {
        if !tracing::enabled!(tracing::Level::DEBUG) {
            return;
        }

        println!("-- Virtual File System {:p} --", Arc::as_ptr(&self.files));
        let files = self.files.try_read().expect("vfs not locked");
        if !files.is_empty() {
            println!();
            for (path, file) in files.iter() {
                use crate::base::PrettyBytes;

                let file = file.try_read().expect("file not locked");
                println!("-- {:?} --", path);
                println!("{:?}\n", PrettyBytes(&file));
            }

            for path in files.iter().map(|(p, _)| p) {
                println!("{:?}", path)
            }
        }
        println!("Number of files: {}", files.len())
    }
}

#[async_trait(?Send)]
impl FioFS for VirtualFileSystem {
    type File = VirtualFile;

    // NB: We could:
    // - keep opts within the file to check if accesses are valid
    // - allow for opening directories as files (like on unix)
    // - allow for retrieving the file path from the file handle?
    // But this is mainly just a mock for unit testing some components,
    // so we do not have to go that far, because it wont be useful in prod.
    async fn open(&self, path: &Path, opts: &OpenOptions) -> io::Result<Self::File> {
        let path = Self::normalize(path);
        trace!("opening file {:?}", path);
        let requires_mutable = opts.create_new || opts.create;
        if requires_mutable {
            let mut files = self.files.write().await;
            if let Some(file) = files.get(&path) {
                if opts.create_new {
                    Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        "file already exists",
                    ))
                } else {
                    if opts.truncate {
                        file.write().await.truncate(0);
                    }
                    Ok(VirtualFile(file.clone()))
                }
            } else {
                if opts.create_new || opts.create {
                    let file = Arc::new(RwLock::new(Vec::new()));
                    files.insert(path, file.clone());
                    Ok(VirtualFile(file))
                } else {
                    Err(io::Error::new(io::ErrorKind::NotFound, "file not found"))
                }
            }
        } else {
            let files = self.files.read().await;
            if let Some(file) = files.get(&path) {
                if opts.truncate {
                    file.write().await.truncate(0);
                }
                Ok(VirtualFile(file.clone()))
            } else {
                Err(io::Error::new(io::ErrorKind::NotFound, "file not found"))
            }
        }
    }

    async fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        // No-op, virtual file-system is has no hierarchy, so we don't manage any directory entries
        trace!("creating directory {:?}", path);
        Ok(())
    }

    async fn sync_dir(&self, path: &Path) -> io::Result<()> {
        trace!("syncing directory {:?}", path);
        Ok(())
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        let from = Self::normalize(from);
        let to = Self::normalize(to);
        trace!("renaming file {:?} to {:?}", from, to);
        let mut files = self.files.write().await;
        let data = files
            .remove(&from)
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "source file not found"))?;

        files.insert(to, data);
        Ok(())
    }

    async fn read_dir(
        &self,
        path: &Path,
    ) -> io::Result<BoxStream<'static, io::Result<FioDirEntry>>> {
        let search_path = Self::normalize(path);
        trace!("reading directory {:?}", search_path);
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
    use bytes::{Bytes, BytesMut};

    use super::*;
    use crate::fio::{FioFS, FioFile};

    #[tokio::test]
    async fn test_path_normalization_and_basic_io() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("test.txt");
        let path_rel = Path::new("./test.txt");

        let data: &[u8] = "hello world".as_ref();

        // Create and write
        let file = vfs.opts().create(true).open(path).await.unwrap();
        file.write_all_at(Bytes::from(data), 0).await.0.unwrap();

        // Open via different but equivalent path
        let file_rel = vfs.opts().read(true).open(path_rel).await.unwrap();
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
        let file = vfs
            .opts()
            .write(true)
            .create(true)
            .open(old_path)
            .await
            .unwrap();
        file.write_all_at(Bytes::from(data), 0).await.0.unwrap();

        // Rename file and sync parent directory
        vfs.rename(old_path, new_path).await.unwrap();
        vfs.sync_dir(&PathBuf::from("/")).await.unwrap();

        // Old file should be gone
        assert!(vfs.opts().open(old_path).await.is_err());

        // New file should have data
        let file = vfs.opts().read(true).open(new_path).await.unwrap();
        let buf = BytesMut::zeroed(data.len());
        let (res, buf) = file.read_exact_at(buf, 0).await;
        res.unwrap();
        assert_eq!(buf, data);
    }

    #[tokio::test]
    async fn test_positional_overwrite_and_holes() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("sparse.bin");
        let file = vfs
            .opts()
            .write(true)
            .create(true)
            .open(path)
            .await
            .unwrap();
        let data = b"ABC".as_ref();

        // Write "AAA" at offset 5. This should automatically resize the VFS vec
        // and leave indices 0..5 as zeros (creating a "hole").
        file.write_all_at(Bytes::from(data), 5).await.0.unwrap();

        let read_file = vfs.opts().read(true).open(path).await.unwrap();
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
        let file = vfs
            .opts()
            .read(true)
            .write(true)
            .create(true)
            .open("small.bin")
            .await
            .unwrap();

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
        let file = vfs
            .opts()
            .write(true)
            .create(true)
            .open(complex)
            .await
            .unwrap();
        file.write_all_at(Bytes::from(b"nested".as_ref()), 0)
            .await
            .0
            .unwrap();

        let simple = Path::new("/a/c/d.txt");
        let opened = vfs.opts().open(simple).await.unwrap();
        assert_eq!(opened.size().await.unwrap(), 6);
    }

    #[tokio::test]
    async fn test_concurrent_read_write() {
        let vfs = VirtualFileSystem::default();
        let path = Path::new("shared.db");
        vfs.opts().create(true).open(path).await.unwrap();

        let writer = vfs.opts().write(true).open(path).await.unwrap();
        let reader = vfs.opts().read(true).open(path).await.unwrap();

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
            let file = vfs
                .opts()
                .write(true)
                .create(true)
                .open(&path)
                .await
                .unwrap();
            file.write_all_at(b"test".as_ref(), 0).await.0.unwrap();
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
