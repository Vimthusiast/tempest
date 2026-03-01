use std::marker::PhantomData;

use bytes::{BufMut, Bytes, BytesMut};
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, LittleEndian, Ref, U32};

use crate::base::{Comparer, InternalKey, KeyTrailer};

pub const BLOCK_TARGET_SIZE: usize = 4096;
pub const BLOCK_RESTART_INTERVAL: u32 = 16;

#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct BlockEntryHeader {
    shared_key_len: U32<LittleEndian>,
    unshared_key_len: U32<LittleEndian>,
    value_len: U32<LittleEndian>,
}

pub enum BlockStatus {
    Ok,
    Full,
}

#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct BlockFooter {
    restart_count: U32<LittleEndian>,
}

pub struct BlockBuilder {
    buf: BytesMut,
    entry_count: u32,
    last_key: Option<Bytes>,
    restart_offsets: Vec<u32>,
}

impl BlockBuilder {
    pub fn new() -> Self {
        Self {
            // NB: we multiply by 2 here, to ideally prevent reallocations, otherwise it end up
            // reallocating at least once when writing the footer in `finalize()`
            buf: BytesMut::with_capacity(BLOCK_TARGET_SIZE * 2),
            entry_count: 0,
            last_key: None,
            restart_offsets: Vec::new(),
        }
    }

    pub fn write_entry(&mut self, key: &Bytes, trailer: KeyTrailer, value: &Bytes) -> BlockStatus {
        let restart_point_reached = self.entry_count % BLOCK_RESTART_INTERVAL == 0;
        if restart_point_reached {
            self.last_key = None;
            self.restart_offsets.push(self.buf.len() as u32);
        }
        let shared_key_len = self.shared_key_len(key);

        let unshared_key_len = key.len() as u32 - shared_key_len;
        let value_len = value.len() as u32;

        let header = BlockEntryHeader {
            shared_key_len: shared_key_len.into(),
            unshared_key_len: unshared_key_len.into(),
            value_len: value_len.into(),
        };

        self.buf.put(header.as_bytes());
        self.buf.put(&key[shared_key_len as usize..]);
        self.buf.put(trailer.as_bytes());
        self.buf.put(value.as_ref());

        // store the bytes reference for shared prefix compression
        self.last_key = Some(key.clone());
        self.entry_count += 1;

        self.get_status()
    }

    fn shared_key_len(&self, new_key: &[u8]) -> u32 {
        if let Some(last_key) = &self.last_key {
            let mut pos = 0;
            while pos < last_key.len() && pos < new_key.len() {
                if last_key[pos] == new_key[pos] {
                    pos += 1;
                } else {
                    break;
                }
            }
            pos as u32
        } else {
            0
        }
    }

    pub fn get_status(&self) -> BlockStatus {
        let is_full = self.buf.len() >= BLOCK_TARGET_SIZE;
        if is_full {
            BlockStatus::Full
        } else {
            BlockStatus::Ok
        }
    }

    pub fn finalize(mut self) -> BytesMut {
        self.buf.put(self.restart_offsets.as_slice().as_bytes());
        let restart_count = self.restart_offsets.len() as u32;
        let footer = BlockFooter {
            restart_count: restart_count.into(),
        };
        self.buf.put(footer.as_bytes());
        self.buf
    }
}

fn parse_block(buf: &[u8]) -> (&[u8], &[U32<LittleEndian>]) {
    let footer_start = buf.len() - size_of::<BlockFooter>();
    let count = BlockFooter::read_from_bytes(&buf[footer_start..])
        .unwrap()
        .restart_count
        .get() as usize;
    let offsets_start = footer_start - count * size_of::<U32<LittleEndian>>();
    let entries = &buf[..offsets_start];
    let offsets = <[U32<LittleEndian>]>::ref_from_bytes(&buf[offsets_start..footer_start]).unwrap();
    (entries, offsets)
}

fn parse_offsets(buf: &[u8], entries_end: usize) -> &[U32<LittleEndian>] {
    let footer_start = buf.len() - size_of::<BlockFooter>();
    <[U32<LittleEndian>]>::ref_from_bytes(&buf[entries_end..footer_start]).unwrap()
}

pub struct BlockIterator<C: Comparer> {
    buf: Bytes,
    pos: usize,
    restart_count: usize,
    entries_end: usize,
    last_key: Vec<u8>,
    _marker: PhantomData<C>,
}

impl<C: Comparer> BlockIterator<C> {
    pub fn new(buf: Bytes) -> Self {
        let (entries, offsets) = parse_block(&buf);
        let restart_count = offsets.len();
        let entries_end = entries.len();
        Self {
            buf,
            pos: 0,
            restart_count,
            entries_end,
            last_key: Vec::new(),
            _marker: PhantomData,
        }
    }
}

impl<C: Comparer> Iterator for BlockIterator<C> {
    type Item = (InternalKey<C>, Bytes);

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.entries_end {
            return None;
        }

        let entries = &self.buf[..self.entries_end];

        let (header, _) = Ref::<_, BlockEntryHeader>::from_prefix(&entries[self.pos..]).unwrap();
        let shared = header.shared_key_len.get() as usize;
        let unshared = header.unshared_key_len.get() as usize;
        let value_len = header.value_len.get() as usize;
        self.pos += size_of::<BlockEntryHeader>();

        // prefix decompress the user key
        self.last_key.truncate(shared);
        self.last_key
            .extend_from_slice(&entries[self.pos..self.pos + unshared]);
        self.pos += unshared;

        // read trailer
        let (trailer, _) = Ref::<_, KeyTrailer>::from_prefix(&entries[self.pos..]).unwrap();
        let trailer = *trailer;
        self.pos += size_of::<KeyTrailer>();

        // zero-copy slice into the buffer for the value
        let value = self.buf.slice(self.pos..self.pos + value_len);
        self.pos += value_len;

        let key = InternalKey::new(Bytes::copy_from_slice(&self.last_key), trailer);
        Some((key, value))
    }
}

pub struct BlockReader<C: Comparer> {
    buf: Bytes,
    _marker: PhantomData<C>,
}

impl<C: Comparer> BlockReader<C> {
    pub fn new(buf: Bytes) -> Self {
        Self {
            buf,
            _marker: PhantomData,
        }
    }

    pub fn get<K: AsRef<[u8]>>(&self, key: &InternalKey<C, K>) -> Option<Bytes> {
        // convert this generic key to a borrowed key so we can compare it with ours
        let key = InternalKey::<C, &[u8]>::new(key.key().as_ref(), key.trailer());

        // parse the block into sections
        let (entries, offsets) = parse_block(&self.buf);

        // phase 1: binary search for the right restart interval
        let restart_key = |offset: usize| -> InternalKey<C, &[u8]> {
            let (header, rest) =
                Ref::<_, BlockEntryHeader>::from_prefix(&entries[offset..]).unwrap();
            // NB: for keys at restart points, we explicitly do not account for the shared part,
            // since restart keys will - by their nature - never have a shared prefix
            let unshared = header.unshared_key_len.get() as usize;
            let key = &rest[..unshared];
            let trailer_bytes = &rest[unshared..unshared + size_of::<KeyTrailer>()];
            let trailer = KeyTrailer::read_from_bytes(trailer_bytes).unwrap();
            InternalKey::new(key, trailer)
        };

        let start_i =
            match offsets.binary_search_by(|offset| restart_key(offset.get() as usize).cmp(&key)) {
                // if we found it, we start here (and will get it immediately)
                Ok(i) => i,
                // if we did not find it, start searching in the previous restart interval,
                // but if ends up underflowing, it is outside of this blocks bounds and we return
                Err(i) => i.checked_sub(1)?,
            };

        let start_offset = offsets[start_i].get() as usize;
        let end_offset = offsets
            .get(start_i + 1)
            .map(|o| o.get() as usize)
            .unwrap_or(entries.len());

        // phase 2: linearly search through this interval
        let mut pos = start_offset;
        let mut last_key: Vec<u8> = Vec::new();

        while pos < end_offset {
            let (header, _) = Ref::<_, BlockEntryHeader>::from_prefix(&entries[pos..]).unwrap();
            let shared = header.shared_key_len.get() as usize;
            let unshared = header.unshared_key_len.get() as usize;
            let value_len = header.value_len.get() as usize;
            pos += size_of::<BlockEntryHeader>();

            // prefix decompress the key
            last_key.truncate(shared);
            last_key.extend_from_slice(&entries[pos..pos + unshared]);
            pos += unshared;

            // read trailer
            let (trailer, _) = Ref::<_, KeyTrailer>::from_prefix(&entries[pos..]).unwrap();
            let trailer = *trailer;
            pos += size_of::<KeyTrailer>();

            // compare with the search key
            let current = InternalKey::<C, &[u8]>::new(&last_key, trailer);
            match current.cmp(&key) {
                std::cmp::Ordering::Less => pos += value_len,
                std::cmp::Ordering::Equal => return Some(self.buf.slice(pos..pos + value_len)),
                std::cmp::Ordering::Greater => return None,
            }
        }

        None
    }

    pub fn iter(&self) -> BlockIterator<C> {
        BlockIterator::new(self.buf.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::{DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum};
    use bytes::Bytes;

    fn make_trailer(seqnum: u64, kind: KeyKind) -> KeyTrailer {
        KeyTrailer::new(unsafe { SeqNum::new_unchecked(seqnum) }, kind)
    }

    fn make_key(s: &str, seqnum: u64) -> InternalKey<DefaultComparer> {
        InternalKey::new(
            Bytes::copy_from_slice(s.as_bytes()),
            make_trailer(seqnum, KeyKind::Put),
        )
    }

    fn build_block(entries: &[(&str, u64, &str)]) -> Bytes {
        let mut builder = BlockBuilder::new();
        for (key, seqnum, value) in entries {
            let k = Bytes::copy_from_slice(key.as_bytes());
            let v = Bytes::copy_from_slice(value.as_bytes());
            let t = make_trailer(*seqnum, KeyKind::Put);
            builder.write_entry(&k, t, &v);
        }
        builder.finalize().freeze()
    }

    #[test]
    fn test_get_existing_key() {
        let buf = build_block(&[
            ("apple", 1, "fruit"),
            ("banana", 1, "yellow"),
            ("cherry", 1, "red"),
        ]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        let result = reader.get(&make_key("banana", 1));
        assert_eq!(result.unwrap(), Bytes::from("yellow"));
    }

    #[test]
    fn test_get_missing_key() {
        let buf = build_block(&[("apple", 1, "fruit"), ("cherry", 1, "red")]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert!(reader.get(&make_key("banana", 1)).is_none());
    }

    #[test]
    fn test_get_key_before_first() {
        let buf = build_block(&[("banana", 1, "yellow"), ("cherry", 1, "red")]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert!(reader.get(&make_key("apple", 1)).is_none());
    }

    #[test]
    fn test_get_key_after_last() {
        let buf = build_block(&[("apple", 1, "fruit"), ("banana", 1, "yellow")]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert!(reader.get(&make_key("cherry", 1)).is_none());
    }

    #[test]
    fn test_prefix_compression_across_restart_interval() {
        // fill more than one restart interval to exercise prefix compression
        let mut entries: Vec<(String, u64, String)> = Vec::new();
        for i in 0..40u32 {
            entries.push((format!("prefix:key:{:04}", i), 1, format!("value:{}", i)));
        }
        let entries_ref: Vec<(&str, u64, &str)> = entries
            .iter()
            .map(|(k, s, v)| (k.as_str(), *s, v.as_str()))
            .collect();

        let buf = build_block(&entries_ref);
        let reader = BlockReader::<DefaultComparer>::new(buf);

        // spot check a few entries across restart boundaries
        for i in [0, 1, 15, 16, 17, 31, 32, 39] {
            let key = format!("prefix:key:{:04}", i);
            let expected = format!("value:{}", i);
            let result = reader.get(&make_key(&key, 1));
            assert_eq!(
                result.unwrap(),
                Bytes::copy_from_slice(expected.as_bytes()),
                "failed at index {}",
                i
            );
        }
    }

    #[test]
    fn test_restart_offsets_written_in_finalize() {
        // a block with exactly BLOCK_RESTART_INTERVAL + 1 entries should have 2 restart points
        let mut builder = BlockBuilder::new();
        for i in 0..=BLOCK_RESTART_INTERVAL {
            let k = Bytes::copy_from_slice(format!("key:{:04}", i).as_bytes());
            let v = Bytes::from("v");
            builder.write_entry(&k, make_trailer(1, KeyKind::Put), &v);
        }
        let buf = builder.finalize().freeze();

        let (_, footer) = Ref::<_, BlockFooter>::from_suffix(buf.as_ref()).unwrap();
        assert_eq!(footer.restart_count.get(), 2);
    }

    #[test]
    fn test_get_first_and_last_entry() {
        let buf = build_block(&[
            ("aaa", 1, "first"),
            ("mmm", 1, "middle"),
            ("zzz", 1, "last"),
        ]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert_eq!(
            reader.get(&make_key("aaa", 1)).unwrap(),
            Bytes::from("first")
        );
        assert_eq!(
            reader.get(&make_key("zzz", 1)).unwrap(),
            Bytes::from("last")
        );
    }

    #[test]
    fn test_empty_value() {
        let buf = build_block(&[("key", 1, "")]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert_eq!(reader.get(&make_key("key", 1)).unwrap(), Bytes::new());
    }

    #[test]
    fn test_iterator_all_entries() {
        let buf = build_block(&[
            ("apple", 1, "fruit"),
            ("banana", 1, "yellow"),
            ("cherry", 1, "red"),
        ]);
        let iter = BlockIterator::<DefaultComparer>::new(buf);
        let results: Vec<_> = iter.map(|(k, v)| (k.key().clone(), v)).collect();

        assert_eq!(results[0], (Bytes::from("apple"), Bytes::from("fruit")));
        assert_eq!(results[1], (Bytes::from("banana"), Bytes::from("yellow")));
        assert_eq!(results[2], (Bytes::from("cherry"), Bytes::from("red")));
        assert_eq!(results.len(), 3);
    }

    #[test]
    fn test_iterator_prefix_compression() {
        // all keys share a long common prefix to stress prefix decompression
        let buf = build_block(&[
            ("tempest:key:0001", 1, "a"),
            ("tempest:key:0002", 1, "b"),
            ("tempest:key:0003", 1, "c"),
        ]);
        let iter = BlockIterator::<DefaultComparer>::new(buf);
        let keys: Vec<_> = iter.map(|(k, _)| k.key().clone()).collect();

        assert_eq!(keys[0], Bytes::from("tempest:key:0001"));
        assert_eq!(keys[1], Bytes::from("tempest:key:0002"));
        assert_eq!(keys[2], Bytes::from("tempest:key:0003"));
    }

    #[test]
    fn test_iterator_across_restart_boundary() {
        let mut entries: Vec<(String, u64, String)> = Vec::new();
        for i in 0..40u32 {
            entries.push((format!("prefix:key:{:04}", i), 1, format!("val:{}", i)));
        }
        let entries_ref: Vec<(&str, u64, &str)> = entries
            .iter()
            .map(|(k, s, v)| (k.as_str(), *s, v.as_str()))
            .collect();

        let buf = build_block(&entries_ref);
        let results: Vec<_> = BlockIterator::<DefaultComparer>::new(buf)
            .map(|(k, v)| (k.key().clone(), v))
            .collect();

        assert_eq!(results.len(), 40);
        for i in 0..40usize {
            assert_eq!(
                results[i].0,
                Bytes::copy_from_slice(format!("prefix:key:{:04}", i).as_bytes())
            );
            assert_eq!(
                results[i].1,
                Bytes::copy_from_slice(format!("val:{}", i).as_bytes())
            );
        }
    }

    #[test]
    fn test_iterator_trailers_preserved() {
        let mut builder = BlockBuilder::new();
        let k = Bytes::from("key");
        let v = Bytes::from("val");
        let trailer = make_trailer(42, KeyKind::Put);
        builder.write_entry(&k, trailer, &v);
        let buf = builder.finalize().freeze();

        let mut iter = BlockIterator::<DefaultComparer>::new(buf);
        let (key, _) = iter.next().unwrap();
        assert_eq!(key.trailer().seqnum().get(), 42);
        assert_eq!(key.trailer().kind(), KeyKind::Put);
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_iterator_empty_values() {
        let buf = build_block(&[("a", 1, ""), ("b", 1, ""), ("c", 1, "")]);
        let results: Vec<_> = BlockIterator::<DefaultComparer>::new(buf)
            .map(|(k, v)| (k.key().clone(), v))
            .collect();

        assert_eq!(results.len(), 3);
        for (_, v) in &results {
            assert_eq!(*v, Bytes::new());
        }
    }

    #[test]
    fn test_iterator_matches_get() {
        // every entry found by the iterator should also be found by get()
        let mut entries: Vec<(String, u64, String)> = Vec::new();
        for i in 0..20u32 {
            entries.push((format!("key:{:04}", i), 1, format!("val:{}", i)));
        }
        let entries_ref: Vec<(&str, u64, &str)> = entries
            .iter()
            .map(|(k, s, v)| (k.as_str(), *s, v.as_str()))
            .collect();

        let buf = build_block(&entries_ref);
        let reader = BlockReader::<DefaultComparer>::new(buf.clone());

        for (key, value) in BlockIterator::<DefaultComparer>::new(buf) {
            let found = reader.get(&key);
            assert_eq!(found.unwrap(), value);
        }
    }
}
