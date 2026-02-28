use std::{
    io,
    path::{Path, PathBuf},
};

use bytes::{BufMut, Bytes, BytesMut};
use crc64::crc64;
use futures::{StreamExt, TryStreamExt};
use serde::{Deserialize, Serialize};
use tokio_uring::buf::BoundedBuf;
use tracing::{Instrument, Level};

use crate::{
    base::{ByteSize, HexU64, SILO_WAL_MAGICNUM, TempestError, TempestResult},
    fio::{FioFS, FioFile},
};

#[derive(Debug)]
pub struct WalHeader {
    filenum: u64,
}

impl WalHeader {
    #[inline]
    pub const fn new(filenum: u64) -> Self {
        Self { filenum }
    }

    #[inline]
    pub const fn filenum(&self) -> u64 {
        self.filenum
    }

    #[inline]
    fn encode(&self) -> [u8; SILO_WAL_HEADER_SIZE] {
        let mut buf = [0u8; SILO_WAL_HEADER_SIZE];
        buf[0..8].copy_from_slice(SILO_WAL_MAGICNUM);
        buf[8..16].copy_from_slice(&self.filenum.to_le_bytes());
        buf
    }

    fn decode(buf: [u8; SILO_WAL_HEADER_SIZE]) -> io::Result<Self> {
        let magic_bytes = &buf[0..8];
        if magic_bytes != SILO_WAL_MAGICNUM {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "invalid magic number: not a write-ahead log file. expected {:?} but got {:?}.",
                    SILO_WAL_MAGICNUM, magic_bytes
                ),
            ));
        }

        // copy filenum
        let filenum = u64::from_le_bytes(buf[8..16].try_into().unwrap());
        Ok(Self { filenum })
    }
}

/// This frames WAL records using a checksum of the data and the data length.
#[derive(Debug, Serialize, Deserialize)]
pub struct WalRecordPrefix {
    checksum: u64,
    len: u32,
}

impl WalRecordPrefix {
    /// Creates a new record prefix for the supplied bytes,
    /// by calculating the crc64 checksum and the length.
    fn new(record: &[u8]) -> Self {
        let checksum = crc64(0, record);
        let len = record.len() as u32;
        Self { checksum, len }
    }

    /// Calculates the checksum of `record` and compares it with the stored checksum.
    /// The length of `record` must equal the stored `len`.
    ///
    /// # Panics
    ///
    /// Panics if `record.len()` is different from `self.len`.
    #[inline]
    fn is_valid_record(&self, record: &[u8]) -> bool {
        assert_eq!(record.len(), self.len as usize);
        let computed_checksum = crc64(0, record);
        computed_checksum == self.checksum
    }

    /// Encodes this record prefix into bytes.
    #[inline]
    fn encode(&self) -> [u8; SILO_WAL_RECORD_PREFIX_SIZE] {
        let mut buf = [0u8; SILO_WAL_RECORD_PREFIX_SIZE];
        buf[0..8].copy_from_slice(&self.checksum.to_le_bytes());
        buf[8..12].copy_from_slice(&self.len.to_le_bytes());
        buf
    }

    /// Decodes this record prefix from a bytes slice.
    #[inline]
    fn decode(buf: [u8; SILO_WAL_RECORD_PREFIX_SIZE]) -> Self {
        let checksum = u64::from_le_bytes(buf[0..8].try_into().unwrap());
        let len = u32::from_le_bytes(buf[8..12].try_into().unwrap());
        Self { checksum, len }
    }
}

// NOTE: extend this to a flag set if we add more variants later and add getters
// => potentially bitmask this
#[derive(Debug)]
pub enum WalStatus {
    // Operation succeeded. No action required.
    Ok,
    // Operation succeeded, file needs to be rotated.
    NeedsRotation,
}

/// A loose value guard that ensures the WAL is flushed before proceeding with the inner data.
#[must_use = "WAL data must be flushed to disk"]
pub struct WalFlushRequired(pub WalStatus);

#[derive(Debug)]
pub struct WalFileReader<F: FioFile> {
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

    pub(crate) async fn next(&mut self) -> Option<TempestResult<BytesMut>> {
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
    ) -> (TempestResult<(BytesMut, u64)>, BytesMut) {
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
        let sliced_scratch = scratch.slice(..SILO_WAL_RECORD_PREFIX_SIZE);
        let (res, sliced_scratch) = file.read_exact_at(sliced_scratch, current_pos).await;
        let scratch = sliced_scratch.into_inner();
        if let Err(e) = res {
            return (Err(e.into()), scratch);
        }
        let record_prefix = WalRecordPrefix::decode(scratch[..].try_into().unwrap());
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
    // TODO: Take in list of filenums to recover from manifest
    #[instrument(skip_all)]
    async fn recover(fs: F, dir: impl AsRef<Path>) -> TempestResult<Self> {
        let dir = dir.as_ref();
        info!(?dir, "creating wal recovery reader");
        let entries: Vec<_> = fs
            .read_dir(dir)
            .await?
            .try_filter(|e| futures::future::ready(!e.is_dir()))
            .try_collect()
            .await?;

        if entries.len() > 0 {
            info!("found {} wal files for recovery", entries.len());
            let mut wal_details: Vec<_> = futures::stream::iter(entries)
                .map(|e| {
                    let fs = fs.clone();
                    let span = span!(Level::DEBUG, "get-file-details", path=?e.path());
                    async move {
                        let file = match fs.opts().read(true).open(e.path()).await {
                            Ok(f) => f,
                            Err(e) => {
                                error!("could not open wal file: {}", e);
                                return Err(e.into());
                            }
                        };
                        debug!("opened file");

                        let buf = BytesMut::zeroed(SILO_WAL_HEADER_SIZE);
                        let sliced_buf = buf.slice(..SILO_WAL_HEADER_SIZE);
                        let (res, sliced_buf) = file.read_exact_at(sliced_buf, 0).await;
                        if let Err(e) = res {
                            error!("could not reader header: {}", e);
                            return Err(e.into());
                        }
                        debug!("read header bytes");

                        let header = match WalHeader::decode(
                            sliced_buf.into_inner().as_ref().try_into().unwrap(),
                        ) {
                            Ok(h) => h,
                            Err(e) => {
                                error!("could not decode header: {}", e);
                                return Err(e.into());
                            }
                        };
                        debug!(filenum = header.filenum, "decoded header");

                        Ok::<_, TempestError>((header, file))
                    }
                    .instrument(span)
                })
                // run 10 reads at once
                .buffer_unordered(10)
                .try_collect()
                .await?;

            wal_details.sort_by_key(|(h, _f)| h.filenum);

            let mut sources = Vec::new();
            for (header, file) in wal_details {
                let filepos = SILO_WAL_HEADER_SIZE as u64;
                let size = file.size().await?;
                debug!(
                    filenum = header.filenum, size = ?ByteSize(size),
                    "sourcing wal file through reader"
                );
                let reader = WalFileReader::new(file, filepos, size);
                sources.push(reader)
            }
            Ok(Self { sources, pos: 0 })
        } else {
            let sources = Vec::new();
            Ok(Self { sources, pos: 0 })
        }
    }

    pub async fn next(&mut self) -> Option<TempestResult<BytesMut>> {
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

/// # Silo Write-Ahead Log
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
pub struct SiloWal<F: FioFS> {
    silo_dir: PathBuf,
    wal_dir: PathBuf,

    scratch: Option<BytesMut>,

    fs: F,
    current_file: <F as FioFS>::File,
    filepos: u64,
    record_count: u32,
}

// -- constants --
pub const SILO_WAL_DIR_NAME: &str = "wal";
pub const SILO_WAL_HEADER_SIZE: usize = 16;
pub const SILO_WAL_RECORD_PREFIX_SIZE: usize = 12;
pub const SILO_WAL_FILE_ROTATE_FILE_SIZE_THRESHOLD: u64 = 2 * 1024 * 1024 * 1024;
pub const SILO_WAL_FILE_ROTATE_RECORD_COUNT_THRESHOLD: u32 = 10_000;

impl<F: FioFS> SiloWal<F> {
    pub(crate) async fn init(
        fs: F,
        silo_dir: PathBuf,
        filenum: u64,
    ) -> TempestResult<(Self, WalRecoveryReader<F>)> {
        let wal_dir = silo_dir.join(SILO_WAL_DIR_NAME);
        info!("initializing silo write-ahead log at {:?}", wal_dir);
        fs.create_dir_all(&wal_dir).await?;

        let recovery_reader = WalRecoveryReader::recover(fs.clone(), &wal_dir).await?;

        let current_file_path = wal_dir.join(format!("{}.log", filenum));
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
        let sliced_scratch = scratch.slice(..SILO_WAL_HEADER_SIZE);
        let (res, sliced_scratch) = current_file.write_all_at(sliced_scratch, 0).await;
        if let Err(e) = res {
            return Err(e.into());
        }
        let scratch = sliced_scratch.into_inner();

        let wal = Self {
            silo_dir,
            wal_dir,

            scratch: Some(scratch),

            fs,
            current_file,
            filepos: SILO_WAL_HEADER_SIZE as u64,
            record_count: 0,
        };

        info!("finished initializing write-ahead log");
        Ok((wal, recovery_reader))
    }

    const fn get_status(&self) -> WalStatus {
        let needs_rotation = self.filepos > SILO_WAL_FILE_ROTATE_FILE_SIZE_THRESHOLD
            || self.record_count > SILO_WAL_FILE_ROTATE_RECORD_COUNT_THRESHOLD;
        if needs_rotation {
            WalStatus::NeedsRotation
        } else {
            WalStatus::Ok
        }
    }

    /// Writes out the data into the current write-ahead log file.
    /// Note that, while we do write to the file, we don't `fsync` in any way, so the caller is
    /// responsible. Returns the current status of this WAL.
    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn append(&mut self, data: Bytes) -> TempestResult<WalFlushRequired> {
        let mut filepos = self.filepos;
        debug!(
            data_size=?ByteSize(data.len() as u64), filepos=?HexU64(filepos),
            "appending to write-ahead log"
        );

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
        // TODO: Maybe we don't have to do this if `Bytes` is truncated, just for `BytesMut`.
        debug!("writing record body");
        let data_len = data.len();
        let data_slice = BoundedBuf::slice(data, ..data_len);
        let (res, _data_slice) = self.current_file.write_all_at(data_slice, filepos).await;
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

    /// Executes a flush of the WAL and returns the inner status from that flush.
    pub async fn flush(&mut self, flush: WalFlushRequired) -> TempestResult<WalStatus> {
        self.current_file.sync_all().await?;
        Ok(flush.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fio::VirtualFileSystem,
        tests::{filenum_gen, setup_tracing},
    };

    #[tokio::test]
    async fn test_silo_wal() -> Result<(), Box<dyn std::error::Error>> {
        setup_tracing();

        let fs = VirtualFileSystem::new();
        let silo_dir = PathBuf::from("data/silo0");
        let mut next_filenum = filenum_gen();
        let data = Bytes::from_static(b"some-test-data");

        {
            let (mut wal, mut recovery_reader) =
                SiloWal::init(fs.clone(), silo_dir.clone(), next_filenum()).await?;
            let _ = wal.append(data.clone()).await?;
            assert!(recovery_reader.next().await.is_none());
        }

        {
            let (_, mut recovery_reader) =
                SiloWal::init(fs.clone(), silo_dir.clone(), next_filenum()).await?;
            assert_eq!(recovery_reader.next().await.unwrap().unwrap(), data);
            assert!(recovery_reader.next().await.is_none());
        }

        Ok(())
    }
}
