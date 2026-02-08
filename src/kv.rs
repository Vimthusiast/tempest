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
    fn scan<'a>(
        &self,
        start: Bound<&'a [u8]>,
        end: Bound<&'a [u8]>,
        seq: SeqNum,
    ) -> BoxStream<'a, (Vec<u8>, Vec<u8>)>;
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
        let kv = InMemoryKvStore::new();
        let mut next_seqnum = create_seqnum_iter();
        let politics_key = "politics and economics";
        let physics_key = "physics";
        let kv_pairs = [
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
            kv.set(key.into(), value.into(), seqnum, KeyKind::Set).await;
        }

        // -- Scanning --
        let mut pairs_from_store = kv.scan(
            Bound::Unbounded,
            Bound::Unbounded,
            next_seqnum.next().unwrap(),
        );
        let mut i = 0;
        while let Some((key, value)) = pairs_from_store.next().await {
            println!("read key: {:?}, value: {:?}", key, value);
            assert_eq!(&key, kv_pairs[i].0.as_bytes());
            assert_eq!(&value, kv_pairs[i].1.as_bytes());
            i += 1;
        }
        assert_eq!(i, kv_pairs.len());

        // -- Shadowing: Overwrite an old entry --
        let new_physics_value = "fascinating";
        let physics_seqnum = next_seqnum.next().unwrap();
        kv.set(
            physics_key.into(),
            new_physics_value.into(),
            physics_seqnum,
            KeyKind::Set,
        )
        .await;
        let phyics_entry = kv.get(physics_key.as_bytes(), physics_seqnum).await;
        assert_eq!(phyics_entry, Some(new_physics_value.into()));

        // -- Tombstone: Delete an old entry --
        let politics_seqnum = next_seqnum.next().unwrap();
        kv.set(
            politics_key.into(),
            Vec::new(),
            politics_seqnum,
            KeyKind::Delete,
        )
        .await;
        let val = kv.get(politics_key.as_bytes(), SeqNum::MAX).await;
        assert!(val.is_none(), "just deleted entry");
        assert_eq!(
            kv.scan(Bound::Unbounded, Bound::Unbounded, politics_seqnum,)
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
                kv.scan(Bound::Unbounded, Bound::Unbounded, politics_seqnum)
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
