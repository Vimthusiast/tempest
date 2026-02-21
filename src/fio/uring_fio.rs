use std::{io, path::Path};

use async_trait::async_trait;
use futures::{
    StreamExt,
    stream::{self, BoxStream},
};
use tokio_uring::buf::{BoundedBuf, BoundedBufMut};

use crate::fio::{FioDirEntry, FioFS, FioFile};

#[derive(Debug)]
pub struct UringFile(tokio_uring::fs::File);

#[async_trait(?Send)]
impl FioFile for UringFile {
    async fn sync_all(&self) -> io::Result<()> {
        self.0.sync_all().await
    }

    async fn size(&self) -> io::Result<u64> {
        let statx = self.0.statx_builder().statx().await?;
        Ok(statx.stx_size)
    }

    async fn read_exact_at<T: BoundedBufMut>(&self, buf: T, pos: u64) -> (io::Result<()>, T) {
        self.0.read_exact_at(buf, pos).await
    }

    async fn write_all_at<T: BoundedBuf>(&self, buf: T, pos: u64) -> (io::Result<()>, T) {
        self.0.write_all_at(buf, pos).await
    }
}

#[derive(Debug, Clone, Default)]
pub struct UringFileSystem;

impl UringFileSystem {
    pub fn new() -> Self {
        Default::default()
    }
}

#[async_trait(?Send)]
impl FioFS for UringFileSystem {
    type File = UringFile;

    async fn open(&self, path: impl AsRef<Path>) -> io::Result<Self::File> {
        let path = path.as_ref();
        let file = tokio_uring::fs::OpenOptions::new()
            .write(true)
            .open(path)
            .await?;
        Ok(UringFile(file))
    }

    async fn create(&self, path: impl AsRef<Path>) -> io::Result<Self::File> {
        let path = path.as_ref();
        let file = tokio_uring::fs::OpenOptions::new()
            .create_new(true)
            .open(path)
            .await?;
        Ok(UringFile(file))
    }

    async fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        tokio_uring::fs::create_dir_all(path).await
    }

    async fn sync_dir(&self, path: &Path) -> io::Result<()> {
        tokio_uring::fs::File::open(path).await?.sync_all().await
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        tokio_uring::fs::rename(from, to).await
    }

    async fn read_dir(
        &self,
        path: &Path,
    ) -> io::Result<BoxStream<'static, io::Result<FioDirEntry>>> {
        let read_dir = tokio::fs::read_dir(path).await?;

        // Unfold the read_dir stream, trying to retrieve every entry within
        let stream = stream::unfold(read_dir, |mut rd| async move {
            match rd.next_entry().await {
                Ok(Some(entry)) => {
                    let path = entry.path();
                    match entry.file_type().await {
                        Ok(ft) => {
                            let res = Ok(FioDirEntry {
                                path,
                                is_dir: ft.is_dir(),
                            });
                            Some((res, rd)) // Successfully retrieved dir entry
                        }
                        Err(e) => Some((Err(e), rd)), // Failed to get file type
                    }
                }
                Ok(None) => None,             // End of stream
                Err(e) => Some((Err(e), rd)), // Error during iteration
            }
        });

        Ok(stream.boxed())
    }
}
