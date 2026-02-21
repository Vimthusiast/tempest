//! This module contains core types that are used across Tempest.
use std::io;

use nonmax::NonMaxU64;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use serde::{Deserialize, Serialize};

/// Magic number for the manifest files, as a first check for file validation.
/// Stored in the footer, at the end of an `*.sst` file.
pub const SST_MAGICNUM: &[u8; 8] = b"TMPS_SST";

/// Magic number for the silo manifest files, as a first check for file validation.
/// Stored in the header, at the start of a `MANIFEST-*` file.
pub const SILO_MANIFEST_MAGICNUM: &[u8; 8] = b"TMPS_MAN";

#[derive(
    Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
#[debug("SeqNum({_0})")]
pub struct SeqNum(NonMaxU64);

impl SeqNum {
    pub const ZERO: Self = unsafe { Self::new_unchecked(0) };
    /// The first sequence number used for keys.
    /// 1-15 are reserved for later use
    pub const START: Self = unsafe { Self::new_unchecked(16) };
    pub const MAX: Self = unsafe { Self::new_unchecked((1 << 56) - 1) };

    /// Creates a new `SeqNum` without verifying that it is within bounds.
    ///
    /// # Safety
    ///
    /// Caller has to ensure that `val` is at most [`SeqNum::MAX`].
    #[inline]
    pub(crate) const unsafe fn new_unchecked(val: u64) -> Self {
        // SAFETY: User has to ensure that `val <= Self::MAX`
        return Self(unsafe { NonMaxU64::new_unchecked(val) });
    }

    // Returns the value as a u64 primitive type.
    #[inline]
    pub(crate) const fn get(&self) -> u64 {
        return self.0.get();
    }
}

impl Default for SeqNum {
    fn default() -> Self {
        Self::START
    }
}

impl TryFrom<u64> for SeqNum {
    // TODO: Use TempestError here
    type Error = TempestError;

    fn try_from(val: u64) -> Result<Self, Self::Error> {
        if val > Self::MAX.get() {
            return Err(TempestError::SeqNumOverflow(val));
        }
        // SAFETY: Just checked `val` is in valid range
        Ok(unsafe { SeqNum::new_unchecked(val) })
    }
}

// These values are part of the file format and shall never be changed.
#[repr(u8)]
#[derive(
    Debug,
    Display,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    IntoPrimitive,
    TryFromPrimitive,
)]
pub enum KeyKind {
    Delete = 0,
    Set = 1,
}

impl KeyKind {
    /// Teh lowest byte value.
    pub const MIN: Self = Self::Delete;
    /// The highest byte value.
    pub const MAX: Self = Self::Set;
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyTrailer(u64);

impl KeyTrailer {
    pub fn new(seq: SeqNum, kind: KeyKind) -> Self {
        Self((seq.get() << 8) | (kind as u64))
    }

    pub fn seq(&self) -> SeqNum {
        // SAFETY: we right shift by 8, so it's less than or equal to SeqNum::MAX
        unsafe { SeqNum::new_unchecked(self.0 >> 8) }
    }

    pub fn kind(&self) -> KeyKind {
        KeyKind::try_from((self.0 & 0xFF) as u8)
            .expect("key trailer should always have a valid kind")
    }
}

#[derive(Debug, Display, Error, From)]
pub enum TempestError {
    #[from(skip)]
    #[display("Sequence number overflow: {_0} exceeds maximum allowed ({}).", SeqNum::MAX.get())]
    SeqNumOverflow(#[error(not(source))] u64),

    #[display("File number hard limit of 2^64 reached")]
    FileNumOverflow,

    #[display("I/O error: {}", _0)]
    IoError(std::io::Error),

    #[display("Failed to encode: {}", _0)]
    BincodeError(bincode::Error),

    #[display("Tempest error: {}", _0)]
    Other(#[error(not(source))] &'static str),
}

pub type TempestResult<T> = Result<T, TempestError>;
