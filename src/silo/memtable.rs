use std::collections::BTreeMap;

use bytes::Bytes;

use crate::base::{Comparer, InternalKey, KeyKind, KeyTrailer, SeqNum};

#[derive(Debug, Default)]
pub(super) struct MemTable<C: Comparer> {
    map: BTreeMap<InternalKey<C>, Bytes>,
}

// [main key (prefix)][8 bytes timestamp]:
// split(len-8);
// assert(len>=8);

impl<C: Comparer> MemTable<C> {
    pub(super) fn new() -> Self {
        Default::default()
    }

    pub(super) fn insert(&mut self, key: InternalKey<C>, value: Bytes) {
        trace!(
            key_kind = ?key.trailer().kind(), key_len = key.key().len(),
            key=?key.key(), ?value, seqnum=key.trailer().seqnum().get(),
            "Inserting kv pair into memtable",
        );
        self.map.insert(key, value);
    }

    pub(super) fn get(&self, key: Bytes, snapshot: SeqNum) -> Option<Bytes> {
        let search_trailer = KeyTrailer::new(snapshot, KeyKind::MAX);
        let search_key = InternalKey::new(key.clone(), search_trailer);

        for (found_key, found_value) in self.map.range(search_key..) {
            if found_key.key() != &key {
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
}
