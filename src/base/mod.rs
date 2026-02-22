//! This module contains base types that are used across Tempest.
use std::{cmp, marker::PhantomData};

use nonmax::NonMaxU64;
use num_enum::{IntoPrimitive, TryFromPrimitive, TryFromPrimitiveError};
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
    pub fn new(seqnum: SeqNum, kind: KeyKind) -> Self {
        Self((seqnum.get() << 8) | (kind as u64))
    }

    pub fn seqnum(&self) -> SeqNum {
        // SAFETY: we right shift by 8, so it's less than or equal to SeqNum::MAX
        unsafe { SeqNum::new_unchecked(self.0 >> 8) }
    }

    pub fn kind(&self) -> KeyKind {
        // SAFETY: we mask by 0xFF to get the key kind bits,
        // which are always inserted by us and must thus be correct
        unsafe { std::mem::transmute((self.0 & 0xFF) as u8) }
    }
}

pub trait Comparer: Default + 'static {
    /// Returns the index where the version suffix starts.
    /// If there is no suffix, returns the length of the slice.
    fn split(&self, key: &[u8]) -> usize;

    /// Compares the prefix part of two keys.
    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

    /// Compares the suffix part of two keys.
    fn compare_suffix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

    /// This function is used to compare two different keys.
    /// It first compares them ascending by the prefix, and then ascending by the suffix.
    fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        let anon = self.split(a);
        let bnon = self.split(b);

        match self.compare_prefix(&a[..anon], &b[..bnon]) {
            cmp::Ordering::Equal => self.compare_suffix(&a[anon..], &b[bnon..]),
            ord => ord,
        }
    }
}

#[derive(Default)]
pub struct DefaultComparer;

impl Comparer for DefaultComparer {
    fn split(&self, key: &[u8]) -> usize {
        key.len()
    }

    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }

    fn compare_suffix(&self, _a: &[u8], _b: &[u8]) -> cmp::Ordering {
        cmp::Ordering::Equal
    }
}

#[derive(Default)]
pub struct AssertComparer<C: Comparer>(C);

impl<C: Comparer> Comparer for AssertComparer<C> {
    fn split(&self, key: &[u8]) -> usize {
        self.0.split(key)
    }

    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        self.0.compare_prefix(a, b)
    }

    fn compare_suffix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        self.0.compare_suffix(a, b)
    }

    fn compare(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        // compare the two keys completely (prefix and suffix)
        let res = self.0.compare(a, b);

        // check for anti-symmetry:
        // `a == b` implies `b == a`
        // `a > b` implies `b < a`
        // `a < b` implies `b > a`
        debug_assert_eq!(
            res,
            self.0.compare(b, a).reverse(),
            "Anti-symmetry violation: compare(a,b) != reverse(compare(b,a))"
        );

        // check for consistency with prefix:
        // if a < b, then prefix(a) must be <= prefix(b)
        let split_a = self.0.split(a);
        let split_b = self.0.split(b);
        let prefix_cmp = a[..split_a].cmp(&b[..split_b]);

        match prefix_cmp {
            cmp::Ordering::Less => {
                debug_assert_eq!(
                    res,
                    cmp::Ordering::Less,
                    "Consistency violation: prefix(a) < prefix(b) but a >= b"
                )
            }
            cmp::Ordering::Greater => {
                debug_assert_eq!(
                    res,
                    cmp::Ordering::Greater,
                    "Consistency violation: prefix(a) > prefix(b) but a <= b"
                )
            }
            cmp::Ordering::Equal => {
                // only suffix comparison matters here
            }
        }

        res
    }
}

#[derive(Debug)]
pub struct InternalKey<K: AsRef<[u8]>, C: Comparer = DefaultComparer> {
    key: K,
    trailer: KeyTrailer,
    _marker: PhantomData<C>,
}

impl<K: AsRef<[u8]>, C: Comparer> InternalKey<K, C> {
    pub(crate) fn new(key: K, trailer: KeyTrailer) -> Self {
        Self {
            key,
            trailer,
            _marker: PhantomData,
        }
    }

    pub(crate) fn trailer(&self) -> KeyTrailer {
        self.trailer
    }

    pub(crate) fn key(&self) -> &K {
        &self.key
    }
}

impl<K: AsRef<[u8]>, C: Comparer> cmp::PartialEq for InternalKey<K, C> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl<K: AsRef<[u8]>, C: Comparer> cmp::Eq for InternalKey<K, C> {}

impl<K: AsRef<[u8]>, C: Comparer> cmp::PartialOrd for InternalKey<K, C> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: AsRef<[u8]>, C: Comparer> cmp::Ord for InternalKey<K, C> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let c = C::default();

        match c.compare(self.key.as_ref(), other.key.as_ref()) {
            cmp::Ordering::Equal => other.trailer.cmp(&self.trailer),
            ord => ord,
        }
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

    #[display("Invalid key kind: {}", _0.number)]
    InvalidKeyKind(TryFromPrimitiveError<KeyKind>),

    #[display("Invalid Varint: Failed to decode.")]
    InvalidVarint,
}

pub type TempestResult<T> = Result<T, TempestError>;
