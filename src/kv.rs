use std::{cmp::Reverse, collections::BTreeMap, ops::Bound, sync::Arc};

use async_trait::async_trait;
use futures::{
    StreamExt,
    stream::{self, BoxStream},
};
use itertools::Itertools;
use nonmax::NonMaxU64;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use tokio::sync::{OwnedRwLockReadGuard, RwLock};

use crate::core::TempestError;

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SeqNum(NonMaxU64);

impl SeqNum {
    pub const ZERO: Self = unsafe { Self::new_unchecked(0) };
    /// The first sequence number used for keys.
    /// 1-15 are reserved for later use
    pub const START: Self = unsafe { Self::new_unchecked(16) };
    pub const MAX: Self = unsafe { Self::new_unchecked((1 << 56) - 1) };

    pub(crate) fn new(val: u64) -> Option<Self> {
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
    fn cursor_at_prefix(&self, prefix: Vec<u8>, seq: SeqNum) -> Box<dyn KvCursor>;
}

#[async_trait]
pub trait KvCursor: Send {
    /// Seeks to a specific key (or the first key greater than it).
    async fn seek(&mut self, key: &[u8]) -> Result<(), TempestError>;

    /// Moves to the next key-value pair and returns it.
    async fn next(&mut self) -> Result<Option<(Vec<u8>, Vec<u8>)>, TempestError>;

    /// Returns the current Key and Value.
    /// Returns `None` if the cursor is out of bounds or at EOF.
    fn current(&self) -> Option<(&[u8], &[u8])>;

    /// Check if the cursor is still valid.
    fn is_valid(&self) -> bool;

    /// Consumes the cursor and returns a Stream of Key-Value pairs.
    fn into_stream(self: Box<Self>) -> BoxStream<'static, (Vec<u8>, Vec<u8>)>
    where
        Self: 'static,
    {
        stream::unfold(self, |mut cursor| async move {
            match cursor.next().await {
                Ok(Some(pair)) => Some((pair, cursor)),
                _ => None,
            }
        })
        .boxed()
    }
}

/// The internal state of our Cursor.
/// We store the owned guard so the BTreeMap isn't dropped or mutated under us.
pub struct VersionedKvCursor {
    /// The captured read lock.
    guard: OwnedRwLockReadGuard<BTreeMap<(Vec<u8>, Reverse<SeqNum>), (Vec<u8>, KeyKind)>>,
    /// The visible sequence number for this cursor.
    seq: SeqNum,
    /// The inclusive lower bound for the scan.
    prefix: Vec<u8>,
    /// The current position in the BTreeMap.
    /// We use a raw key here to re-establish the range iterator if needed,
    /// but for simplicity, we'll hold the iterator directly.
    current_key: Option<Vec<u8>>,
    current_value: Option<Vec<u8>>,
    /// Whether the cursor is finished.
    is_done: bool,
}

#[async_trait]
impl KvCursor for VersionedKvCursor {
    async fn seek(&mut self, key: &[u8]) -> Result<(), TempestError> {
        self.is_done = false;
        // Logic: Jump to the key, then call next() to handle versioning
        self.current_key = Some(key.to_vec());
        Ok(())
    }

    async fn next(&mut self) -> Result<Option<(Vec<u8>, Vec<u8>)>, TempestError> {
        if self.is_done {
            return Ok(None);
        }

        // We need to find the next logical key that is <= self.seq
        // If we have a current_key, we start searching from there + 1.
        let range_start = if let Some(ref k) = self.current_key {
            // If we just started or seeked, we want to include this key
            // but jump to the specific version.
            Bound::Included((k.clone(), Reverse(self.seq)))
        } else {
            Bound::Included((self.prefix.clone(), Reverse(self.seq)))
        };

        // We iterate until we find a key that:
        // 1. Matches the prefix
        // 2. Is different from the current_key (if we've already returned one)
        // 3. Is not a Delete tombstone

        let mut iter = self.guard.range((range_start, Bound::Unbounded));

        while let Some(((found_key, Reverse(found_seq)), (found_val, kind))) = iter.next() {
            // 1. Prefix check
            if !found_key.starts_with(&self.prefix) {
                break;
            }

            // 2. Skip versions from the future
            if *found_seq > self.seq {
                continue;
            }

            // 3. Handle key transitions
            if let Some(ref k) = self.current_key {
                // If we are looking at the same user-key but a different version, skip.
                // Because of Reverse(SeqNum), the first one we see is the newest.
                if found_key == k {
                    continue;
                }
            }

            // 4. We found the newest visible version of a NEW key
            self.current_key = Some(found_key.clone());

            match kind {
                KeyKind::Set => {
                    let res = (found_key.clone(), found_val.clone());
                    self.current_value = Some(found_val.clone());
                    return Ok(Some(res));
                }
                KeyKind::Delete => {
                    // It's a tombstone. We mark it as the current_key so we don't
                    // look at older versions of it, then keep looping for the next logical key.
                    self.current_value = None;
                    continue;
                }
            }
        }

        self.is_done = true;
        self.current_key = None;
        self.current_value = None;
        Ok(None)
    }

    fn current(&self) -> Option<(&[u8], &[u8])> {
        match (&self.current_key, &self.current_value) {
            (Some(k), Some(v)) => Some((k.as_slice(), v.as_slice())),
            _ => None,
        }
    }

    fn is_valid(&self) -> bool {
        !self.is_done && self.current_key.is_some()
    }
}

#[derive(Debug, Default)]
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
        println!(
            "Setting key [{}] to value [{}] (seq: {}, kind: {})",
            key.iter().map(|b| format!("{:02X}", b)).format(" "),
            value.iter().map(|b| format!("{:02X}", b)).format(" "),
            seq,
            kind
        );
        self.inner
            .write()
            .await
            .insert((key, Reverse(seq)), (value, kind));
    }

    fn cursor_at_prefix(&self, prefix: Vec<u8>, seq: SeqNum) -> Box<dyn KvCursor> {
        // We use try_read_owned or we must handle the async nature.
        // Since cursor_at_prefix is sync in the signature, we assume the lock is available
        // or we block_on. Better yet, we make the store return the guard.

        // For the sake of the signature provided:
        let guard = self
            .inner
            .clone()
            .try_read_owned()
            .expect("In-memory store lock contention");

        Box::new(VersionedKvCursor {
            guard,
            seq,
            prefix,
            current_key: None,
            current_value: None,
            is_done: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;

    fn create_seqnum_iter() -> impl Iterator<Item = SeqNum> {
        (SeqNum::START.get()..=SeqNum::MAX.get())
            .map(|n| SeqNum::new(n).expect("seqnums should be in valid range"))
    }

    #[tokio::test]
    async fn test_in_memory_kv_store() {
        // setup the kv store
        let kv_store = InMemoryKvStore::new();
        // use this to generate new incrementing sequence numbers
        let mut next_seqnum = create_seqnum_iter();
        let politics_key = "politics and economics";
        let physics_key = "physics";
        let kv_pairs = [
            ("mathematics", "just as awesome"),
            ("maths", "awesome"),
            (physics_key, "boring"),
            ("computer science", "incredible"),
            (politics_key, "exhausting"),
        ]
        .into_iter()
        .sorted_by_key(|(k, _v)| *k)
        .map(|(k, v)| (k, v, next_seqnum.next().unwrap()))
        .collect_vec();
        println!("kv pairs: {:?}", kv_pairs);
        for &(key, value, seqnum) in kv_pairs.iter() {
            kv_store
                .set(key.into(), value.into(), seqnum, KeyKind::Set)
                .await;
        }

        // -- Cursor Scanning without Prefix --
        let mut cursor = kv_store.cursor_at_prefix(vec![], next_seqnum.next().unwrap());
        let mut i = 0;
        while i < kv_pairs.len()
            && let Some((k, v)) = cursor.next().await.unwrap()
        {
            let (exp_k, exp_v, _s) = kv_pairs[i];
            assert_eq!(str::from_utf8(&k).unwrap(), exp_k);
            assert_eq!(str::from_utf8(&v).unwrap(), exp_v);
            i += 1;
        }
        assert_eq!(i, kv_pairs.len(), "should have found every key once");
        assert_eq!(cursor.next().await.unwrap(), None, "cursor should be eof");
        drop(cursor);

        // -- Cursor Scanning with Prefix --
        let mut cursor = kv_store.cursor_at_prefix("math".into(), next_seqnum.next().unwrap());
        assert!(matches!(cursor.next().await, Ok(Some((k, v)))
                if &k == "mathematics".as_bytes() && &v == "just as awesome".as_bytes()));
        assert!(matches!(cursor.next().await, Ok(Some((k, v)))
                if &k == "maths".as_bytes() && &v == "awesome".as_bytes()));
        drop(cursor);

        // -- Shadowing: Overwrite an old entry --
        let new_physics_value = "fascinating";
        let physics_seqnum = next_seqnum.next().unwrap();
        kv_store
            .set(
                physics_key.into(),
                new_physics_value.into(),
                physics_seqnum,
                KeyKind::Set,
            )
            .await;
        let phyics_entry = kv_store.get(physics_key.as_bytes(), physics_seqnum).await;
        assert_eq!(phyics_entry, Some(new_physics_value.into()));

        // -- Tombstone: Delete an old entry --
        let politics_seqnum = next_seqnum.next().unwrap();
        kv_store
            .set(
                politics_key.into(),
                Vec::new(),
                politics_seqnum,
                KeyKind::Delete,
            )
            .await;
        let val = kv_store.get(politics_key.as_bytes(), SeqNum::MAX).await;
        assert!(val.is_none(), "just deleted entry");
        assert_eq!(
            kv_store
                .cursor_at_prefix(vec![], politics_seqnum)
                .into_stream()
                .collect::<Vec<_>>()
                .await
                .len(),
            kv_pairs.len() - 1
        );
        for ((start_key, start_value), (kv_key, kv_value)) in kv_pairs
            .iter()
            // updated physics
            .map(|&(k, v, _s)| {
                if k == physics_key {
                    (physics_key, new_physics_value)
                } else {
                    (k, v)
                }
            })
            // removed politics
            .filter(|&(k, _v)| k != politics_key)
            .zip_eq(
                kv_store
                    .cursor_at_prefix(vec![], politics_seqnum)
                    .into_stream()
                    .collect::<Vec<_>>()
                    .await,
            )
        {
            println!(
                "start key: {}, kv key: {}",
                start_key,
                String::from_utf8_lossy(&kv_key)
            );
            assert_eq!(start_key.as_bytes(), &kv_key);
            println!(
                "start value: {}, kv value: {}",
                start_value,
                String::from_utf8_lossy(&kv_value)
            );
            assert_eq!(start_value.as_bytes(), &kv_value);
        }
    }
}
