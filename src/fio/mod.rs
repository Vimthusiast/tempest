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

#[derive(Debug, Default)]
pub struct OpenOptions {
    // TODO: We should consider using a bitmask here for efficiency
    pub read: bool,
    pub write: bool,
    pub create: bool,
    pub create_new: bool,
    pub truncate: bool,
}

pub struct OpenBuilder<F: FioFS> {
    fs: F,
    opts: OpenOptions,
}

impl<F: FioFS> OpenBuilder<F> {
    pub(crate) fn new(fs: F) -> Self {
        let opts = OpenOptions::default();
        Self { fs, opts }
    }

    pub const fn read(mut self, read: bool) -> Self {
        self.opts.read = read;
        self
    }

    pub const fn write(mut self, write: bool) -> Self {
        self.opts.write = write;
        self
    }

    pub const fn create(mut self, create: bool) -> Self {
        self.opts.create = create;
        self
    }

    pub const fn create_new(mut self, create_new: bool) -> Self {
        self.opts.create_new = create_new;
        self
    }

    pub const fn truncate(mut self, truncate: bool) -> Self {
        self.opts.truncate = truncate;
        self
    }

    pub async fn open(&self, path: impl AsRef<Path>) -> io::Result<F::File> {
        let path = path.as_ref();
        self.fs.open(path, &self.opts).await
    }
}

/// # File I/O File Trait
///
/// A trait that abstracts asynchronous I/O from the file system.
#[async_trait(?Send)]
pub trait FioFile: Unpin + 'static {
    async fn sync_all(&self) -> io::Result<()>;
    async fn size(&self) -> io::Result<u64>;

    async fn read_exact_at<T: BoundedBufMut>(&self, buf: T, pos: u64) -> (io::Result<()>, T);
    async fn write_all_at<T: BoundedBuf>(&self, buf: T, pos: u64) -> (io::Result<()>, T);
}

#[async_trait(?Send)]
pub trait FioFS: Send + Sync + 'static + Clone {
    /// The representation of a single file in this file system.
    type File: FioFile;

    fn opts(&self) -> OpenBuilder<Self> {
        OpenBuilder::new(self.clone())
    }

    /// Retrieve a [`Self::File`], which is just a thin handle, i.e. a [file descriptor].
    ///
    /// [file descriptor]: https://en.wikipedia.org/wiki/File_descriptor
    async fn open(&self, path: &Path, opts: &OpenOptions) -> io::Result<Self::File>;

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
