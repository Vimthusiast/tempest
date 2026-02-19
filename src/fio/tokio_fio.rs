use std::{
    os::unix::fs::MetadataExt,
    path::Path,
    pin::Pin,
    task::{Context, Poll},
};

use futures::{
    StreamExt,
    stream::{self, BoxStream},
};
use tokio::io::{self, AsyncRead, AsyncSeek, AsyncWrite};

use async_trait::async_trait;

use crate::fio::{FioDirEntry, FioFS, FioFile};

pub struct TokioFile(tokio::fs::File);

impl AsyncRead for TokioFile {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut io::ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        Pin::new(&mut self.0).poll_read(cx, buf)
    }
}

impl AsyncWrite for TokioFile {
    fn poll_write(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        Pin::new(&mut self.0).poll_write(cx, buf)
    }

    fn poll_flush(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Pin::new(&mut self.0).poll_flush(cx)
    }

    fn poll_shutdown(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Pin::new(&mut self.0).poll_shutdown(cx)
    }
}

impl AsyncSeek for TokioFile {
    fn start_seek(mut self: Pin<&mut Self>, position: io::SeekFrom) -> io::Result<()> {
        Pin::new(&mut self.0).start_seek(position)
    }

    fn poll_complete(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<u64>> {
        Pin::new(&mut self.0).poll_complete(cx)
    }
}

#[async_trait]
impl FioFile for TokioFile {
    async fn sync_all(&mut self) -> io::Result<()> {
        self.0.sync_all().await
    }

    async fn size(&self) -> io::Result<u64> {
        let metadata = self.0.metadata().await?;
        Ok(metadata.size())
    }
}

#[derive(Clone)]
pub struct TokioFileSystem;

#[async_trait]
impl FioFS for TokioFileSystem {
    type File = TokioFile;

    async fn open(&self, path: &Path) -> io::Result<Self::File> {
        let file = tokio::fs::File::open(path).await?;
        Ok(TokioFile(file))
    }

    async fn create(&self, path: &Path) -> io::Result<Self::File> {
        let file = tokio::fs::File::create(path).await?;
        Ok(TokioFile(file))
    }

    async fn create_dir_all(&self, path: &Path) -> io::Result<()> {
        tokio::fs::create_dir_all(path).await
    }

    async fn sync_dir(&self, path: &Path) -> io::Result<()> {
        #[cfg(unix)]
        {
            let file = tokio::fs::File::open(path).await?;
            file.sync_all().await?;
        }
        Ok(())
    }

    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()> {
        tokio::fs::rename(from, to).await
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
