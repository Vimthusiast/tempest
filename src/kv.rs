use std::{cmp::Reverse, collections::BTreeMap, ops::Bound, sync::Arc};

use async_trait::async_trait;
use futures::{
    StreamExt,
    stream::{self, BoxStream},
};
use nonmax::NonMaxU64;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use tokio::sync::RwLock;

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SeqNum(NonMaxU64);

impl SeqNum {
    pub const ZERO: Self = unsafe { Self::new_unchecked(0) };
    pub const MAX: Self = unsafe { Self::new_unchecked((1 << 56) - 1) };

    pub(crate) fn new(val: u64) -> Option<Self> {
        if val > Self::MAX.get() {
            return None;
        }
        // SAFETY: Just checked that `val` is never greater than 2^56-1
        return Some(Self(unsafe { NonMaxU64::new_unchecked(val) }));
    }

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

#[async_trait]
pub trait KvStore: Send + Sync {
    async fn get(&self, key: &[u8], seq: SeqNum) -> Option<Vec<u8>>;
    async fn set(&self, key: Vec<u8>, value: Vec<u8>, seq: SeqNum, kind: KeyKind);
    fn scan<'a>(
        &self,
        start: Bound<&'a [u8]>,
        end: Bound<&'a [u8]>,
        seq: SeqNum,
    ) -> BoxStream<'a, (Vec<u8>, Vec<u8>)>;
}

#[derive(Default)]
pub struct InMemoryKvStore {
    inner: Arc<RwLock<BTreeMap<(Vec<u8>, Reverse<SeqNum>), (Vec<u8>, KeyKind)>>>,
}

impl InMemoryKvStore {
    pub fn new() -> Self {
        Default::default()
    }
}

#[async_trait]
impl KvStore for InMemoryKvStore {
    async fn get(&self, key: &[u8], seq: SeqNum) -> Option<Vec<u8>> {
        let inner = self.inner.read().await;

        let mut range = inner.range((key.to_vec(), Reverse(seq))..);

        if let Some(((found_key, Reverse(_found_seq)), (value, found_kind))) = range.next() {
            // skipped over key
            if found_key != key {
                return None;
            }

            match found_kind {
                KeyKind::Delete => return None,
                KeyKind::Set => return Some(value.clone()),
            }
        }
        None
    }

    async fn set(&self, key: Vec<u8>, value: Vec<u8>, seq: SeqNum, kind: KeyKind) {
        self.inner
            .write()
            .await
            .insert((key, Reverse(seq)), (value, kind));
    }

    fn scan<'a>(
        &self,
        start: Bound<&'a [u8]>,
        end: Bound<&'a [u8]>,
        seq: SeqNum,
    ) -> BoxStream<'a, (Vec<u8>, Vec<u8>)> {
        let inner_clone = self.inner.clone();

        stream::once(async move {
            let read_guard = inner_clone.read_owned().await;
            let mut results = Vec::new();
            let mut current_key: Option<(Vec<u8>, SeqNum)> = None;

            // Convert the start + seq to the complex bound, that ensures ordering of keys
            let range_start = match start {
                Bound::Included(k) => Bound::Included((k.to_vec(), Reverse(seq))),
                Bound::Excluded(k) => Bound::Excluded((k.to_vec(), Reverse(SeqNum::ZERO))),
                Bound::Unbounded => Bound::Unbounded,
            };

            for ((found_key, Reverse(found_seq)), (found_value, found_kind)) in
                read_guard.range((range_start, Bound::Unbounded))
            {
                // Respect the end bound
                match end {
                    Bound::Included(e) if found_key.as_slice() > e => break,
                    Bound::Excluded(e) if found_key.as_slice() >= e => break,
                    _ => {}
                }

                // Skip versions from the future
                if *found_seq > seq {
                    continue;
                }

                // If this is an older version, skip it
                if let Some((current_key, current_seq)) = current_key.as_ref() {
                    if current_key == found_key {
                        assert!(current_seq > found_seq);
                        continue;
                    }
                }
                current_key = Some((found_key.clone(), *found_seq));

                match found_kind {
                    KeyKind::Delete => {}
                    KeyKind::Set => results.push((found_key.clone(), found_value.clone())),
                    // others may come later
                }
            }

            results
        })
        .flat_map(stream::iter)
        .boxed()
    }
}
