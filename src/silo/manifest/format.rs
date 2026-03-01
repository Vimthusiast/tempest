use std::{
    io,
    path::{Path, PathBuf},
};

use bytes::Bytes;
use crc64::crc64;
use serde::{Deserialize, Serialize};

use crate::base::{SILO_MANIFEST_MAGICNUM, SeqNum};

/// # SST Metadata
///
/// Stores the metadata for one sorted string table within Tempest.
/// The path format is **`/{silo_root}/ssts/l-{level}/{filenum}.sst`**,
/// which can be obtained simply through the [`get_path`] method.
///
/// [`get_path`]: Self::get_path
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SstMetadata {
    pub(crate) filenum: u64,
    pub(crate) file_size: u64,

    pub(crate) level: u8,

    pub(crate) min_key: Bytes,
    pub(crate) max_key: Bytes,

    pub(crate) min_seqnum: SeqNum,
    pub(crate) max_seqnum: SeqNum,
}

#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct SstDeletion {
    pub(crate) filenum: u64,
}

#[derive(Debug, Default, Serialize, Deserialize)]
#[debug("ManifestEditV1(seqnum_limit={} filenum_limit={} ssts_added={} ssts_removed={})",
    seqnum_limit.map(|v| v.get()).unwrap_or(0),
    filenum_limit.unwrap_or(0),
    ssts_added.as_ref().map(|v| v.len()).unwrap_or(0),
    ssts_removed.as_ref().map(|v| v.len()).unwrap_or(0),
)]
pub(crate) struct ManifestEditV1 {
    pub(super) seqnum_limit: Option<SeqNum>,
    pub(super) filenum_limit: Option<u64>,

    /// A list of new [`SstMetadata`] objects that register SST files to the [`SiloManifest`].
    pub(super) ssts_added: Option<Vec<SstMetadata>>,

    /// A list of removed [`SstMetadata`] objects, identified by their level and file ID,
    /// that register SST files to the [`SiloManifest`].
    pub(super) ssts_removed: Option<Vec<SstDeletion>>,

    pub(super) wal_filenums_added: Option<Vec<u64>>,
    pub(super) wal_filenums_removed: Option<Vec<u64>>,
}

/// A versioned list of edits to the [`SiloManifest`].
#[repr(u16)]
#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum ManifestEdit {
    #[debug("{:?}", _0)]
    V1(ManifestEditV1) = 1,
}

impl ManifestEdit {
    pub(super) fn into_latest(self) -> ManifestEditV1 {
        match self {
            ManifestEdit::V1(edit) => edit,
        }
    }
}

/// Total size of a [`SiloManifestHeader`] after encoding.
pub(super) const SILO_MANIFEST_HEADER_SIZE: usize = 24;

pub(super) struct SiloManifestHeader {
    pub(super) filenum: u64,
    pub(super) filename: PathBuf,
}

impl SiloManifestHeader {
    pub(super) fn new(filenum: u64) -> Self {
        // allocate filename once, to safe on future allocations using `get_filename`
        let filename = PathBuf::from(format!("MANIFEST-{}", filenum));
        Self { filenum, filename }
    }

    #[inline]
    pub(super) const fn filenum(&self) -> u64 {
        self.filenum
    }

    #[inline]
    pub(super) fn get_filename(&self) -> &Path {
        &self.filename
    }

    pub(super) fn encode(&self) -> [u8; SILO_MANIFEST_HEADER_SIZE] {
        let mut buf = [0u8; SILO_MANIFEST_HEADER_SIZE];
        // 1. Magic bytes
        buf[0..8].copy_from_slice(SILO_MANIFEST_MAGICNUM);

        // 2. Manifest ID / file number (little-endian)
        buf[8..16].copy_from_slice(&self.filenum.to_le_bytes());

        // 3. Calculate and store CRC64 checksum
        let bytes_to_hash = &buf[0..16];
        let checksum = crc64(0, bytes_to_hash);
        buf[16..24].copy_from_slice(&checksum.to_le_bytes());
        buf
    }

    pub(super) fn decode(buf: &[u8; SILO_MANIFEST_HEADER_SIZE]) -> io::Result<Self> {
        let magic_bytes = &buf[0..8];
        if magic_bytes != SILO_MANIFEST_MAGICNUM {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "invalid magic number: not a manifest file. expected {:?} but got {:?}.",
                    SILO_MANIFEST_MAGICNUM, magic_bytes
                ),
            ));
        }

        let checksum_bytes = buf[16..24].try_into().expect("16..24 is 8 long");
        let checksum = u64::from_le_bytes(checksum_bytes);
        let computed_checksum = crc64(0, &buf[0..16]);
        if computed_checksum != checksum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "manifest header checksum mismatch: potential corruption",
            ));
        }

        let file_number_bytes = buf[8..16].try_into().expect("8..16 is 8 long");
        let file_number = u64::from_le_bytes(file_number_bytes);
        Ok(Self::new(file_number))
    }
}

/// Total size of a record prefix in a silo manifest.
pub(super) const SILO_MANIFEST_RECORD_PREFIX_SIZE: usize = 12;

pub(super) struct SiloManifestRecordPrefix {
    pub(super) data_len: u32,
    pub(super) checksum: u64,
}

impl SiloManifestRecordPrefix {
    /// Creates a new record prefix for some data, providing a frame with a checksum.
    pub(super) fn new(data: &[u8]) -> Self {
        assert!(
            data.len() <= u32::MAX as usize,
            "manifest record size may not exceed 2^32 bytes."
        );
        let data_len = data.len() as u32;
        let checksum = crc64(0, data);
        Self { data_len, checksum }
    }

    /// Calculates the checksum of `data` and compares it with the stored checksum.
    /// The length of `data` must equal the stored `data_len`.
    ///
    /// # Panics
    ///
    /// Panics if `data.len()` is different from `self.data_len`.
    #[inline]
    pub(super) fn is_valid_record(&self, data: &[u8]) -> bool {
        assert_eq!(data.len(), self.data_len as usize);
        let computed_checksum = crc64(0, data);
        self.checksum == computed_checksum
    }

    /// Encodes this record prefix into bytes.
    #[inline]
    pub(super) fn encode(&self) -> [u8; SILO_MANIFEST_RECORD_PREFIX_SIZE] {
        let mut buf = [0u8; SILO_MANIFEST_RECORD_PREFIX_SIZE];
        buf[0..4].copy_from_slice(&self.data_len.to_le_bytes());
        buf[4..12].copy_from_slice(&self.checksum.to_le_bytes());
        buf
    }

    /// Decodes this record prefix from a byte slice.
    #[inline]
    pub(super) fn decode(buf: &[u8; SILO_MANIFEST_RECORD_PREFIX_SIZE]) -> Self {
        let data_len = u32::from_le_bytes(buf[0..4].try_into().unwrap());
        let checksum = u64::from_le_bytes(buf[4..12].try_into().unwrap());
        Self { data_len, checksum }
    }
}
