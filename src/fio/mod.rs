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
use tokio::io::{AsyncRead, AsyncSeek, AsyncWrite};
pub use tokio_fio::*;
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
#[async_trait]
pub trait FioFile: AsyncRead + AsyncWrite + AsyncSeek + Send + Sync {
    async fn sync_all(&mut self) -> io::Result<()>;
    async fn size(&self) -> io::Result<u64>;
}

#[async_trait]
pub trait FioFS: Send + Sync + Clone {
    type File: FioFile;

    /// Retrieve a [`Self::File`], which is just a thin handle.
    async fn open(&self, path: &Path) -> io::Result<Self::File>;

    /// Create a new [`Self::File`], returning the handle.
    async fn create(&self, path: &Path) -> io::Result<Self::File>;

    /// Recursively creates a directory and all of its parent components if they are missing.
    async fn create_dir_all(&self, path: &Path) -> io::Result<()>;

    /// Rename a file, essentially moving it to another location.
    /// The path `to` may point to an existing file, which is then deleted.
    async fn rename(&self, from: &Path, to: &Path) -> io::Result<()>;

    /// Reads the contents of a directory as an asynchronous stream of directory entries.
    async fn read_dir(
        &self,
        path: &Path,
    ) -> io::Result<BoxStream<'static, io::Result<FioDirEntry>>>;
}
