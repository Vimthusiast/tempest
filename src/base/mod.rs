//! This module contains base types that are used across Tempest.
//!
//! - [`SeqNum`]: A sequence number new-type, since they are 56 bits, due to bit-packing.
//! - [`KeyKind`]: A one-byte key-kind that identifies different operations in our storage layer.
//! - [`KeyTrailer`]: This type packs the [`SeqNum`] in the higher 7 bytes, with [`KeyKind`] at the
//!   lowest byte. Ordering by it therefore prioritizes the sequence number over the kind.
//! - [`InternalKey`]: This is the key representation that our storage layer uses. It implements
//!   custom ordering through the [`Comparer`] trait, allowing for key suffixes that encode custom
//!   data. Tempest uses the suffix for [`HlcTimestamp`]s, to allow ordering of data across silos.
//!
//! [`HlcTimestamp`]: crate::ctrl::hlc::HlcTimestamp

use std::{cmp, marker::PhantomData};

use bincode::Options as BincodeOptions;
use bytes::Bytes;
use nonmax::NonMaxU64;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use serde::{Deserialize, Serialize};

pub mod comparer;
pub mod error;

pub use comparer::*;
pub use error::*;

/// Magic number for the manifest files, as a first check for file validation.
/// Stored in the footer, at the end of an `*.sst` file.
pub const SST_MAGICNUM: &[u8; 8] = b"TMPS_SST";

/// Magic number for the silo manifest files, as a first check for file validation.
/// Stored in the header, at the start of a `MANIFEST-*` file.
pub const SILO_MANIFEST_MAGICNUM: &[u8; 8] = b"TMPS_MAN";

/// Magic number for the silo write-ahead log files, as a first check for file validation.
/// Stored in the header, at the start of a `*.log` file.
pub const SILO_WAL_MAGICNUM: &[u8; 8] = b"TMPS_WAL";

/// The crate wide used [`bincode`] encoding options.
#[doc(hidden)]
pub fn bincode_options() -> impl BincodeOptions {
    bincode::options()
        .with_fixint_encoding() // Important: no variable length ints
        .with_little_endian() // Ensure consistency across platforms
        .allow_trailing_bytes()
}

#[derive(
    Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
#[debug("SeqNum({_0})")]
pub struct SeqNum(NonMaxU64);

impl SeqNum {
    pub const ZERO: Self = unsafe { Self::new_unchecked(0) };

    /// The sequence number one below the start.
    /// Sometimes exists when searching in a silo, that had no inserts yet.
    pub const MIN: Self = unsafe { Self::new_unchecked(15) };
    /// The first sequence number used for keys.
    /// 1-14 are reserved for later use
    pub const START: Self = unsafe { Self::new_unchecked(16) };
    /// The maximum sequence number available. Sequence numbers may only use 56 bits,
    /// since the [`KeyTrailer`] encodes the [`SeqNum`] in the upper 7 bytes, with the
    /// [`KeyKind`] in the lowest byte, to achieve the best bit packing.
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
    Put = 1,
}

impl KeyKind {
    /// The lowest value (byte-wise).
    pub const MIN: Self = Self::Delete;
    /// The highest value (byte-wise).
    pub const MAX: Self = Self::Put;
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[debug("KeyTrailer({}:seqnum={},kind={})", _0, self.seqnum(), self.kind())]
pub struct KeyTrailer(u64);

impl KeyTrailer {
    pub const fn new(seqnum: SeqNum, kind: KeyKind) -> Self {
        Self((seqnum.get() << 8) | (kind as u64))
    }

    pub const fn seqnum(&self) -> SeqNum {
        // SAFETY: we right shift by 8, so it's less than or equal to SeqNum::MAX
        unsafe { SeqNum::new_unchecked(self.0 >> 8) }
    }

    pub const fn kind(&self) -> KeyKind {
        // SAFETY: we mask by 0xFF to get the key kind bits,
        // which are always inserted by us and must thus be correct
        unsafe { std::mem::transmute((self.0 & 0xFF) as u8) }
    }

    /// Creates a key trailer for testing other parts of Tempest.
    /// This function will always return the exact same zeroed key trailer.
    #[cfg(test)]
    pub(crate) const fn test() -> Self {
        Self::new(SeqNum::ZERO, KeyKind::MIN)
    }
}

#[derive(Debug, Clone)]
pub struct InternalKey<C: Comparer = DefaultComparer> {
    key: Bytes,
    trailer: KeyTrailer,
    _marker: PhantomData<C>,
}

impl<C: Comparer> InternalKey<C> {
    pub(crate) fn new(key: Bytes, trailer: KeyTrailer) -> Self {
        Self {
            key,
            trailer,
            _marker: PhantomData,
        }
    }

    pub(crate) fn trailer(&self) -> KeyTrailer {
        self.trailer
    }

    pub(crate) fn key(&self) -> &Bytes {
        &self.key
    }

    /// Generate an internal key for testing other parts of Tempest.
    /// Test keys with a higher ID will be greater than ones with a lower ID.
    /// This is useful to test correctness of internal ordering.
    #[cfg(test)]
    pub(crate) fn test(id: u64) -> Self {
        let user_key = Bytes::from(id.to_be_bytes().to_vec());
        Self::new(user_key, KeyTrailer::test())
    }

    // Test helper that gets the key as an easily comparable `u64` value.
    #[cfg(test)]
    pub(crate) fn user_key_as_u64(&self) -> u64 {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(self.key.as_ref());
        u64::from_be_bytes(buf)
    }
}

impl<C: Comparer> cmp::PartialEq for InternalKey<C> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl<C: Comparer> cmp::Eq for InternalKey<C> {}

impl<C: Comparer> cmp::PartialOrd for InternalKey<C> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<C: Comparer> cmp::Ord for InternalKey<C> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let c = C::default();

        match c.compare_physical(self.key.as_ref(), other.key.as_ref()) {
            cmp::Ordering::Equal => other.trailer.cmp(&self.trailer),
            ord => ord,
        }
    }
}
