use std::io;

use crc64::crc64;
use serde::{Deserialize, Serialize};

use crate::base::SILO_WAL_MAGICNUM;

// -- constants --
pub(super) const SILO_WAL_DIR_NAME: &str = "wal";
pub(super) const SILO_WAL_HEADER_SIZE: usize = 16;
pub(super) const SILO_WAL_RECORD_PREFIX_SIZE: usize = 12;

#[derive(Debug)]
pub(super) struct WalHeader {
    pub(super) filenum: u64,
}

impl WalHeader {
    #[inline]
    pub(super) const fn new(filenum: u64) -> Self {
        Self { filenum }
    }

    #[inline]
    pub(super) fn encode(&self) -> [u8; SILO_WAL_HEADER_SIZE] {
        let mut buf = [0u8; SILO_WAL_HEADER_SIZE];
        buf[0..8].copy_from_slice(SILO_WAL_MAGICNUM);
        buf[8..16].copy_from_slice(&self.filenum.to_le_bytes());
        buf
    }

    pub(super) fn decode(buf: [u8; SILO_WAL_HEADER_SIZE]) -> io::Result<Self> {
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
pub(super) struct WalRecordPrefix {
    pub(super) checksum: u64,
    pub(super) len: u32,
}

impl WalRecordPrefix {
    /// Creates a new record prefix for the supplied bytes,
    /// by calculating the crc64 checksum and the length.
    pub(super) fn new(record: &[u8]) -> Self {
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
    pub(super) fn is_valid_record(&self, record: &[u8]) -> bool {
        assert_eq!(record.len(), self.len as usize);
        let computed_checksum = crc64(0, record);
        computed_checksum == self.checksum
    }

    /// Encodes this record prefix into bytes.
    #[inline]
    pub(super) fn encode(&self) -> [u8; SILO_WAL_RECORD_PREFIX_SIZE] {
        let mut buf = [0u8; SILO_WAL_RECORD_PREFIX_SIZE];
        buf[0..8].copy_from_slice(&self.checksum.to_le_bytes());
        buf[8..12].copy_from_slice(&self.len.to_le_bytes());
        buf
    }

    /// Decodes this record prefix from a bytes slice.
    #[inline]
    pub(super) fn decode(buf: [u8; SILO_WAL_RECORD_PREFIX_SIZE]) -> Self {
        let checksum = u64::from_le_bytes(buf[0..8].try_into().unwrap());
        let len = u32::from_le_bytes(buf[8..12].try_into().unwrap());
        Self { checksum, len }
    }
}
