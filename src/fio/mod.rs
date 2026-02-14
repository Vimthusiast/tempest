//! # File I/O
//!
//! This module contains asynchronous abstractions over the file system, to allow testing of
//! implementations that require file-system I/O.

use std::{
    io,
    path::{Path, PathBuf},
};

use async_trait::async_trait;

mod tokio_fio;
mod virtual_fio;

use futures::stream::BoxStream;
pub use tokio_fio::*;
pub use virtual_fio::*;

pub struct FioDirEntry {
    path: PathBuf,
    is_dir: bool,
}

#[async_trait]
pub trait FioFile: Send + Sync {
    /// Writes a buffer into this writer, returning how many bytes were written.
    ///
    /// This function will attempt to write the entire contents of `buf`, but
    /// the entire write might not succeed, or the write may also generate an
    /// error. Typically, a call to `write` represents one attempt to write to
    /// any wrapped object.
    async fn write(&mut self, buf: &[u8]) -> io::Result<usize>;

    /// Attempts to write an entire buffer into this writer.
    async fn write_all(&mut self, buf: &[u8]) -> io::Result<()>;

    /// Reads the exact number of bytes required to fill `buf`.
    async fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<usize>;

    /// Reads all bytes until EOF in this source, placing them into `buf`.
    async fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize>;

    async fn sync_all(&mut self) -> io::Result<()>;

    async fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64>;

    async fn seek_relative(&mut self, offset: i64) -> io::Result<()> {
        self.seek(io::SeekFrom::Current(offset)).await?;
        Ok(())
    }

    async fn size(&self) -> io::Result<u64>;
}

#[async_trait]
pub trait FioFS: Send + Sync {
    type File: FioFile;

    /// Retrieve a [`Self::File`], which is just a thin handle.
    async fn open(&self, path: &Path) -> io::Result<Self::File>;

    /// Create a new [`Self::File`], returning the handle.
    async fn create(&self, path: &Path) -> io::Result<Self::File>;

    /// Rename a file, essentially moving it to another location.
    /// The path `to` may point to an existing file, which is then deleted.
    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()>;

    /// Reads the contents of a directory as an asynchronous stream of directory entries.
    async fn read_dir(
        &self,
        path: &Path,
    ) -> io::Result<BoxStream<'static, io::Result<FioDirEntry>>>;
}
