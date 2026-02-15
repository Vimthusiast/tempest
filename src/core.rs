use nonmax::NonMaxU64;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use serde::{Deserialize, Serialize};

#[derive(
    Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct SeqNum(NonMaxU64);

impl SeqNum {
    pub const ZERO: Self = unsafe { Self::new_unchecked(0) };
    /// The first sequence number used for keys.
    /// 1-15 are reserved for later use
    pub const START: Self = unsafe { Self::new_unchecked(16) };
    pub const MAX: Self = unsafe { Self::new_unchecked((1 << 56) - 1) };

    pub(crate) const fn new(val: u64) -> Option<Self> {
        if val > Self::MAX.get() {
            return None;
        }
        // SAFETY: Just checked that `val` is never greater than 2^56-1
        return Some(unsafe { Self::new_unchecked(val) });
    }

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

    pub(crate) const fn increment(&self, rhs: u64) -> Option<Self> {
        Self::new(self.get() + rhs)
    }
}

impl Default for SeqNum {
    fn default() -> Self {
        Self::START
    }
}

impl Into<u64> for SeqNum {
    fn into(self) -> u64 {
        self.get()
    }
}

// These values are part of the file format and shall never be changed.
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
#[repr(u8)]
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
