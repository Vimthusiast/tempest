use std::collections::BTreeMap;

use bytes::Bytes;

use crate::base::{Comparer, InternalKey, KeyKind, KeyTrailer, SeqNum};

pub(crate) struct MemTableIter<'a, C: Comparer> {
    inner: std::collections::btree_map::Iter<'a, InternalKey<C>, Bytes>,
}

impl<'a, C: Comparer> Iterator for MemTableIter<'a, C> {
    type Item = (InternalKey<C>, Bytes);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (k.clone(), v.clone()))
    }
}

#[derive(Debug, Default)]
pub(crate) struct MemTable<C: Comparer> {
    // TODO: Replace BTreeMap with a Skiplist
    map: BTreeMap<InternalKey<C>, Bytes>,
    approximate_size: usize,
    min_seqnum: Option<SeqNum>,
    max_seqnum: Option<SeqNum>,
    /// Represents the smallest filenum of the write-ahead logs that back this memtable.
    wal_filenum: u64,
}

impl<C: Comparer> MemTable<C> {
    pub(crate) fn new(wal_filenum: u64) -> Self {
        Self {
            wal_filenum,
            ..Default::default()
        }
    }

    pub(crate) fn insert(&mut self, key: InternalKey<C>, value: Bytes) {
        trace!(
            key_kind = ?key.trailer().kind(), key_len = key.key().len(),
            key=?key.key(), ?value, seqnum=?key.trailer().seqnum(),
            "inserting kv pair into memtable",
        );
        self.approximate_size += key.key().len() + value.len() + 16; // 16 for trailer + overhead
        let seqnum = key.trailer().seqnum();
        self.map.insert(key, value);
        self.min_seqnum = Some(match self.min_seqnum {
            Some(s) => s.min(seqnum),
            None => seqnum,
        });
        self.max_seqnum = Some(match self.max_seqnum {
            Some(s) => s.max(seqnum),
            None => seqnum,
        });
    }

    pub(crate) fn get(&self, key: &Bytes, snapshot: SeqNum) -> Option<Bytes> {
        let search_trailer = KeyTrailer::new(snapshot, KeyKind::MAX);
        let search_key = InternalKey::new(key.clone(), search_trailer);

        for (found_key, found_value) in self.map.range(search_key..) {
            if found_key.key() != key {
                // Key not found, we skipped past it
                break;
            }

            return match found_key.trailer().kind() {
                KeyKind::Delete => None,
                KeyKind::Put => Some(found_value.clone()),
            };
        }

        // no value was found
        None
    }

    pub(crate) const fn approximate_size(&self) -> usize {
        self.approximate_size
    }

    /// Returns the length i.e. the number of entries in this memtable
    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the smallest key in this memtable.
    pub(crate) fn min_key(&self) -> Option<&InternalKey<C>> {
        self.map.keys().next()
    }

    /// Returns the largest key in this memtable.
    pub(crate) fn max_key(&self) -> Option<&InternalKey<C>> {
        self.map.keys().next_back()
    }

    /// Returns the smallest seqnum in this memtable.
    pub(crate) const fn min_seqnum(&self) -> Option<SeqNum> {
        self.min_seqnum
    }

    /// Returns the largest seqnum in this memtable.
    pub(crate) const fn max_seqnum(&self) -> Option<SeqNum> {
        self.max_seqnum
    }

    pub(crate) const fn wal_filenum(&self) -> u64 {
        self.wal_filenum
    }

    pub(crate) fn iter(&self) -> MemTableIter<'_, C> {
        MemTableIter {
            inner: self.map.iter(),
        }
    }
}
