use std::{
    io,
    path::{Path, PathBuf},
};

use bytes::{BufMut, Bytes, BytesMut};
use tempest_core::{
    fio::{FioFS, FioFile},
    utils::{ByteSize, HexU64},
};
use tokio_uring::buf::BoundedBuf;

use crate::{
    base::{StorageError, StorageResult},
    config::WalConfig,
    wal::format::{
        SILO_WAL_HEADER_SIZE, SILO_WAL_RECORD_PREFIX_SIZE, WAL_DIR, WalHeader, WalRecordPrefix,
    },
};

pub(crate) mod format;

#[cfg(test)]
mod tests;

// NOTE: extend this to a flag set if we add more variants later and add getters
// => potentially bitmask this
#[derive(Debug)]
pub(crate) enum WalStatus {
    // Operation succeeded. No action required.
    Ok,
    // Operation succeeded, file needs to be rotated.
    NeedsRotation,
}

/// A loose value guard that ensures the WAL is flushed before proceeding with the inner data.
#[must_use = "WAL data must be flushed to disk"]
pub(crate) struct WalFlushRequired(pub WalStatus);

#[derive(Debug)]
struct WalFileReader<F: FioFile> {
    file: F,
    filepos: u64,
    endpos: u64,
    had_error: bool,
    scratch: Option<BytesMut>,
}

impl<F: FioFile> WalFileReader<F> {
    fn new(file: F, filepos: u64, endpos: u64) -> Self {
        Self {
            file,
            filepos,
            endpos,
            had_error: false,
            scratch: Some(BytesMut::with_capacity(16)),
        }
    }

    async fn next(&mut self) -> Option<StorageResult<BytesMut>> {
        if self.filepos >= self.endpos || self.had_error {
            return None;
        }
        // NB: We take here and expect it to always be put back, since we require ownership when
        // passing this buffer to the file system layer, i.e. io_uring
        let scratch = self.scratch.take().expect("scratch buffer exists");
        let (res, scratch) =
            Self::read_record(scratch, &self.file, self.filepos, self.endpos).await;
        self.scratch = Some(scratch);
        let (data, bytes_read) = match res {
            Ok(v) => v,
            Err(e) => {
                // this will be empty, on the first error
                self.had_error = true;
                return Some(Err(e.into()));
            }
        };
        self.filepos += bytes_read;
        Some(Ok(data))
    }

    /// Returns the record data and the number of bytes read on success,
    /// on an error if it failed. Always returns the scratch buffer back out.
    #[instrument(skip_all)]
    async fn read_record(
        mut scratch: BytesMut,
        file: &F,
        filepos: u64,
        endpos: u64,
    ) -> (StorageResult<(BytesMut, u64)>, BytesMut) {
        debug!(filepos=?HexU64(filepos), "reading from write-ahead log");

        let mut current_pos = filepos;

        // read the record prefix
        if current_pos + SILO_WAL_RECORD_PREFIX_SIZE as u64 > endpos {
            return (
                Err(io::Error::new(io::ErrorKind::UnexpectedEof, "unexpected end of file").into()),
                scratch,
            );
        }
        scratch.resize(SILO_WAL_RECORD_PREFIX_SIZE, 0);
        let sliced_scratch = scratch.slice(..);
        let (res, sliced_scratch) = file.read_exact_at(sliced_scratch, current_pos).await;
        let scratch = sliced_scratch.into_inner();
        if let Err(e) = res {
            return (Err(e.into()), scratch);
        }
        let record_prefix =
            WalRecordPrefix::decode(scratch[..SILO_WAL_RECORD_PREFIX_SIZE].try_into().unwrap());
        debug!(
            size = ?ByteSize(record_prefix.len as u64),
            checksum = ?HexU64(record_prefix.checksum),
            "got record prefix"
        );
        current_pos += SILO_WAL_RECORD_PREFIX_SIZE as u64;

        if current_pos + record_prefix.len as u64 > endpos {
            return (
                Err(io::Error::new(io::ErrorKind::UnexpectedEof, "unexpected end of file").into()),
                scratch,
            );
        }
        let filebuf = BytesMut::zeroed(record_prefix.len as usize);
        let sliced_filebuf = filebuf.slice(..record_prefix.len as usize);
        let (res, sliced_filebuf) = file.read_exact_at(sliced_filebuf, current_pos).await;
        let filebuf = sliced_filebuf.into_inner();
        if let Err(e) = res {
            return (Err(e.into()), scratch);
        }
        assert_eq!(filebuf.len(), record_prefix.len as usize);
        current_pos += record_prefix.len as u64;

        if !record_prefix.is_valid_record(&filebuf) {
            return (
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "write-ahead log record prefix checksum mismatch: potential corruption",
                )
                .into()),
                scratch,
            );
        }

        let bytes_read = current_pos - filepos;
        (Ok((filebuf, bytes_read)), scratch)
    }
}

pub struct WalRecoveryReader<F: FioFS> {
    sources: Vec<WalFileReader<<F as FioFS>::File>>,
    pos: usize,
}

impl<F: FioFS> WalRecoveryReader<F> {
    /// Reads in all the `files` in form of a stream, in the order the filenums were supplied.
    #[instrument(skip_all)]
    async fn recover(fs: F, dir: impl AsRef<Path>, files: &[u64]) -> StorageResult<Self> {
        let dir = dir.as_ref();
        info!(
            ?dir,
            num_files = files.len(),
            "creating wal recovery reader"
        );

        if files.is_empty() {
            return Ok(Self {
                sources: Vec::new(),
                pos: 0,
            });
        }

        // files is already ordered by the manifest, no sort needed
        let mut sources = Vec::with_capacity(files.len());
        for &filenum in files {
            let path = dir.join(format!("{}.log", filenum));
            let file = fs.opts().read(true).open(&path).await?;

            // verify header integrity before trusting this file
            let buf = BytesMut::zeroed(SILO_WAL_HEADER_SIZE);
            let (res, buf) = file.read_exact_at(buf.slice(..), 0).await;
            res?;

            let header = WalHeader::decode(buf.into_inner().as_ref().try_into().unwrap())?;

            if header.filenum != filenum {
                error!(
                    expected = filenum,
                    got = header.filenum,
                    "WAL header filenum mismatch"
                );
                return Err(StorageError::WalCorruption {
                    expected: filenum,
                    got: header.filenum,
                });
            }

            let filepos = SILO_WAL_HEADER_SIZE as u64;
            let size = file.size().await?;
            sources.push(WalFileReader::new(file, filepos, size));
        }

        Ok(Self { sources, pos: 0 })
    }

    pub async fn next(&mut self) -> Option<StorageResult<BytesMut>> {
        loop {
            // check if we reached end
            if self.pos >= self.sources.len() {
                return None;
            }
            // get next value from sources
            if let Some(result) = self.sources[self.pos].next().await {
                return Some(result);
            }
            // advance if source is exhausted
            self.pos += 1;
        }
    }
}

/// # Storage Write-Ahead Log
///
/// Ensures that writes are durable before being committed to the memtable of the LSM-Tree.
///
/// ## File Structure
///
/// The file is structured into a header, followed by a list of records with an arbitrary size.
/// The initial header of WAL files is used to distinguish them from other files.
/// It identifies the files based on their starting magic number and the silo-unique filenum.
/// The total encoded length of the header is equal to [`WAL_HEADER_SIZE`].
///
/// ```not_rust
/// +------------+--------------+-- ... --+
/// | Magic (8B) | Filenum (8B) | Records |
/// +------------+--------------+-- ... --+
/// ```
///
/// Every record in the WAL has a CRC64 checksum for data integrity checks and a length, which is
/// at most 4GiB. In the future, we should split up logical and physical WALs, so that a big record
/// may span multiple files.
///
/// ```not_rust
/// +---------------+----------+-- .. --+
/// | Checksum (8B) | Len (4B) |  Data  |
/// +---------------+----------+-- .. --+
/// ```
#[derive(Debug)]
pub struct Wal<F: FioFS> {
    storage_dir: PathBuf,
    root_dir: PathBuf,

    scratch: Option<BytesMut>,

    fs: F,
    current_file: <F as FioFS>::File,
    filenum: u64,
    filepos: u64,
    record_count: u32,

    config: WalConfig,
}

pub(crate) fn wal_file_path(dir: &Path, filenum: u64) -> PathBuf {
    dir.join(format!("{}.log", filenum))
}

impl<F: FioFS> Wal<F> {
    pub(crate) async fn init(
        fs: F,
        storage_dir: PathBuf,
        filenum: u64,
        files: &[u64],
        config: WalConfig,
    ) -> StorageResult<(Self, WalRecoveryReader<F>)> {
        let root_dir = storage_dir.join(WAL_DIR);
        info!("initializing write-ahead log at {:?}", root_dir);
        fs.create_dir_all(&root_dir).await?;

        let recovery_reader = WalRecoveryReader::recover(fs.clone(), &root_dir, files).await?;

        let current_file_path = wal_file_path(&root_dir, filenum);
        let current_file = fs
            .opts()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(current_file_path)
            .await?;

        let mut scratch = BytesMut::with_capacity(64);

        let header = WalHeader::new(filenum);
        scratch.put_slice(&header.encode());
        let sliced_scratch = scratch.slice(..);
        let (res, sliced_scratch) = current_file.write_all_at(sliced_scratch, 0).await;
        if let Err(e) = res {
            return Err(e.into());
        }
        let scratch = sliced_scratch.into_inner();

        let wal = Self {
            storage_dir,
            root_dir,

            scratch: Some(scratch),

            fs,
            current_file,
            filenum,
            filepos: SILO_WAL_HEADER_SIZE as u64,
            record_count: 0,

            config,
        };

        info!("finished initializing write-ahead log");
        Ok((wal, recovery_reader))
    }

    const fn get_status(&self) -> WalStatus {
        let needs_rotation = self.filepos > self.config.rotate_file_size_threshold
            || self.record_count > self.config.rotate_record_count_threshold;
        if needs_rotation {
            WalStatus::NeedsRotation
        } else {
            WalStatus::Ok
        }
    }

    /// Writes out the data into the current write-ahead log file.
    /// Note that, while we do write to the file, we don't `fsync` in any way, so the caller is
    /// responsible, allowing for multiple appends in a row, before flushing (batching).
    ///
    /// # Returns
    ///
    /// Returns the current status of this WAL, wrapped in a flush-guard.
    #[instrument(skip_all, level = "debug", fields(data_size = ?ByteSize(data.len() as u64), filesize=?HexU64(self.filepos)))]
    pub(crate) async fn append(&mut self, data: Bytes) -> StorageResult<WalFlushRequired> {
        let mut filepos = self.filepos;

        // encode record prefix into scratch buffer and write it out to the file
        debug!("writing record prefix");
        let mut scratch = self.scratch.take().expect("scratch buffer exists");
        scratch.clear();
        let prefix = WalRecordPrefix::new(&data);
        scratch.put_slice(&prefix.encode());
        let sliced_scratch = scratch.slice(..SILO_WAL_RECORD_PREFIX_SIZE);
        let (res, sliced_scratch) = self
            .current_file
            .write_all_at(sliced_scratch, filepos)
            .await;
        self.scratch = Some(sliced_scratch.into_inner());
        if let Err(e) = res {
            return Err(e.into());
        }
        // move past the written record prefix
        filepos += SILO_WAL_RECORD_PREFIX_SIZE as u64;

        // NB: slice up data explicitly for io_uring passing. uring interface does not respect
        // length of the buffer, but capacity otherwise.
        debug!("writing record body");
        let data_len = data.len();
        let (res, _data) = self.current_file.write_all_at(data, filepos).await;
        if let Err(e) = res {
            return Err(e.into());
        }
        // move past the written record body
        filepos += data_len as u64;

        let record_size = filepos - self.filepos;

        // update the file position
        self.filepos = filepos;
        self.record_count += 1;

        debug!(
            filepos = ?HexU64(filepos), record_count = self.record_count,
            record_size = ?ByteSize(record_size), "finished appending to wal"
        );

        // return the new status
        Ok(WalFlushRequired(self.get_status()))
    }

    pub(crate) async fn rotate(&mut self, filenum: u64) -> StorageResult<()> {
        let current_file_path = wal_file_path(&self.root_dir, filenum);
        let current_file = self
            .fs
            .opts()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&current_file_path)
            .await?;

        let mut scratch = self.scratch.take().expect("scratch buffer exists");
        scratch.clear();

        let header = WalHeader::new(filenum);
        scratch.put_slice(&header.encode());
        let sliced_scratch = scratch.slice(..);
        let (res, sliced_scratch) = current_file.write_all_at(sliced_scratch, 0).await;
        self.scratch = Some(sliced_scratch.into_inner());
        if let Err(e) = res {
            return Err(e.into());
        }

        self.current_file = current_file;
        self.filenum = filenum;
        self.filepos = SILO_WAL_HEADER_SIZE as u64;
        self.record_count = 0;

        Ok(())
    }

    /// Executes a flush of the WAL and returns the inner status from that flush.
    pub(crate) async fn flush(&mut self, flush: WalFlushRequired) -> StorageResult<WalStatus> {
        self.current_file.sync_all().await?;
        Ok(flush.0)
    }

    pub(crate) fn filenum(&self) -> u64 {
        self.filenum
    }
}
