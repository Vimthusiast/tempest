use std::{os::unix::fs::MetadataExt, path::Path};

use futures::{
    StreamExt,
    stream::{self, BoxStream},
};
use tokio::io::{self, AsyncReadExt, AsyncSeekExt, AsyncWriteExt};

use async_trait::async_trait;

use crate::fio::{FioDirEntry, FioFS, FioFile};

pub struct TokioFile(tokio::fs::File);

#[async_trait]
impl FioFile for TokioFile {
    async fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf).await
    }

    async fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.0.write_all(buf).await
    }

    async fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read_exact(buf).await
    }

    async fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        self.0.read_to_end(buf).await
    }

    async fn sync_all(&mut self) -> io::Result<()> {
        self.0.sync_all().await
    }

    async fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        self.0.seek(pos).await
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
