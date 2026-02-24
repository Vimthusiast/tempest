//! # File I/O
//!
//! This module contains asynchronous abstractions over the file system, to allow testing of
//! implementations that require file-system I/O.

use std::{
    io,
    path::{Path, PathBuf},
};

use async_trait::async_trait;

mod uring_fio;
mod virtual_fio;

use futures::stream::BoxStream;
use tokio_uring::buf::{BoundedBuf, BoundedBufMut};
pub use uring_fio::*;
pub use virtual_fio::*;

pub struct FioDirEntry {
    path: PathBuf,
    is_dir: bool,
}

impl FioDirEntry {
    #[inline]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[inline]
    pub const fn is_dir(&self) -> bool {
        self.is_dir
    }

    pub const fn is_file(&self) -> bool {
        !self.is_dir
    }
}

/// # File I/O File Trait
///
/// A trait that abstracts asynchronous I/O from the file system.
#[async_trait(?Send)]
pub trait FioFile: Unpin {
    async fn sync_all(&self) -> io::Result<()>;
    async fn size(&self) -> io::Result<u64>;

    async fn read_exact_at<T: BoundedBufMut>(&self, buf: T, pos: u64) -> (io::Result<()>, T);
    async fn write_all_at<T: BoundedBuf>(&self, buf: T, pos: u64) -> (io::Result<()>, T);
}

#[async_trait(?Send)]
pub trait FioFS: Send + Sync + 'static + Clone {
    /// The representation of a single file in this file system.
    type File: FioFile;

    /// Retrieve a [`Self::File`], which is just a thin handle, i.e. a [file descriptor].
    ///
    /// [file descriptor]: https://en.wikipedia.org/wiki/File_descriptor
    async fn open(&self, path: impl AsRef<Path>) -> io::Result<Self::File>;

    /// Create a new [`Self::File`], returning the handle.
    async fn create(&self, path: impl AsRef<Path>) -> io::Result<Self::File>;

    /// Recursively creates a directory and all of its parent components if they are missing.
    async fn create_dir_all(&self, path: &Path) -> io::Result<()>;

    /// Sync a directory to disk to finalize any metadata changes inside, such as renames.
    async fn sync_dir(&self, path: &Path) -> io::Result<()>;

    /// Rename a file, essentially moving it to another location.
    /// The path `to` may point to an existing file, which is then deleted.
    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()>;

    /// Reads the contents of a directory as an asynchronous stream of directory entries.
    async fn read_dir(
        &self,
        path: &Path,
    ) -> io::Result<BoxStream<'static, io::Result<FioDirEntry>>>;
}
