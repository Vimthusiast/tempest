use std::{io, path::PathBuf};

use bytes::{BufMut, Bytes, BytesMut};
use crc64::crc64;
use serde::{Deserialize, Serialize};
use tokio_uring::buf::BoundedBuf;

use crate::{
    base::{SILO_WAL_MAGICNUM, TempestResult},
    fio::{FioFS, FioFile},
};

/// # Write-Ahead Log Header
///
/// The initial small header of WAL files, used to distinguish them from other files.
/// Identifies the files based on their starting magic number and the silo-unique filenum.
/// The total encoded length is equal to [`WAL_HEADER_SIZE`]:
///
/// ```not_rust
/// +------------+--------------+
/// | Magic (8B) | Filenum (8B) |
/// +------------+--------------+
/// ```
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

/// # Write-Ahead Log Record Prefix
///
/// This frames WAL records using a checksum of the data and the data length.
/// A single WAL record looks like this:
///
/// ```not_rust
/// +---------------+----------+-- .... --+
/// | Checksum (8B) | Len (4B) |  Record  |
/// +---------------+----------+-- .... --+
/// ```
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

#[derive(Debug)]
pub struct SiloWal<F: FioFS> {
    silo_dir: PathBuf,
    wal_dir: PathBuf,

    scratch: Option<BytesMut>,

    fs: F,
    current_file: <F as FioFS>::File,
    current_filepos: u64,
    current_record_count: u32,
}

// -- constants --
pub const SILO_WAL_DIR_NAME: &str = "wal";
pub const SILO_WAL_HEADER_SIZE: usize = 16;
pub const SILO_WAL_RECORD_PREFIX_SIZE: usize = 12;
pub const SILO_WAL_FILE_ROTATE_SIZE_THRESHOLD: u64 = 2 * 1024 * 1024 * 1024;
pub const SILO_WAL_FILE_ROTATE_RECORD_COUNT_THRESHOLD: u32 = 10_000;

impl<F: FioFS> SiloWal<F> {
    pub(crate) async fn init(fs: F, silo_dir: PathBuf, filenum: u64) -> TempestResult<Self> {
        let wal_dir = silo_dir.join(SILO_WAL_DIR_NAME);
        info!("initializing silo write-ahead log at {:?}", wal_dir);
        fs.create_dir_all(&wal_dir).await?;

        let current_file_path = wal_dir.join(format!("{}.log", filenum));
        let current_file = fs
            .opts()
            .read(true)
            .write(true)
            .create(true)
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

        info!("finished initializing write-ahead log");
        Ok(Self {
            silo_dir,
            wal_dir,

            scratch: Some(scratch),

            fs,
            current_file,
            current_filepos: SILO_WAL_HEADER_SIZE as u64,
            current_record_count: 0,
        })
    }

    const fn get_status(&self) -> WalStatus {
        let needs_rotation = self.current_filepos > SILO_WAL_FILE_ROTATE_SIZE_THRESHOLD
            || self.current_record_count > SILO_WAL_FILE_ROTATE_RECORD_COUNT_THRESHOLD;
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
    pub(crate) async fn append(&mut self, data: Bytes) -> TempestResult<WalStatus> {
        let mut current_pos = self.current_filepos;
        debug!(
            data_len = data.len(),
            current_pos, "appending to write-ahead log"
        );

        // encode record prefix into scratch buffer and write it out to the file
        debug!("writing record prefix");
        let mut scratch = self.scratch.take().expect("scratch buffer not taken yet");
        scratch.clear();
        let prefix = WalRecordPrefix::new(&data);
        scratch.put_slice(&prefix.encode());
        let sliced_scratch = scratch.slice(..SILO_WAL_RECORD_PREFIX_SIZE);
        let (res, sliced_scratch) = self
            .current_file
            .write_all_at(sliced_scratch, current_pos)
            .await;
        self.scratch = Some(sliced_scratch.into_inner());
        if let Err(e) = res {
            return Err(e.into());
        }
        // move past the written record prefix
        current_pos += SILO_WAL_RECORD_PREFIX_SIZE as u64;

        // NB: slice up data explicitly for io_uring passing. uring interface does not respect
        // length of the buffer, but capacity otherwise.
        // TODO: Maybe we don't have to do this if `Bytes` is truncated, just for `BytesMut`.
        debug!("writing record body");
        let data_len = data.len();
        let data_slice = BoundedBuf::slice(data, ..data_len);
        let (res, _data_slice) = self
            .current_file
            .write_all_at(data_slice, current_pos)
            .await;
        if let Err(e) = res {
            return Err(e.into());
        }
        // move past the written record body
        current_pos += data_len as u64;

        // update the file position
        self.current_filepos = current_pos;
        self.current_record_count += 1;

        debug!(
            current_pos,
            current_record_count = self.current_record_count,
            "finished appending to wal"
        );

        // return the new status
        Ok(self.get_status())
    }

    #[instrument(skip_all)]
    async fn read_record(file: &<F as FioFS>::File) -> TempestResult<()> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::tests::setup_tracing;

    #[tokio::test]
    async fn test_silo_wal() {
        setup_tracing();
    }
}
