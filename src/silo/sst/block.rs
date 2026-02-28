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

    pub fn get<K: AsRef<[u8]>>(&self, key: InternalKey<C, K>) -> Option<Bytes> {
        // convert this generic key to a borrowed key so we can compare it with ours
        let key = InternalKey::<C, &[u8]>::new(key.key().as_ref(), key.trailer());

        // phase 1: split up the buffer into footer, offset index, and entries
        let (rest, footer) = Ref::<_, BlockFooter>::from_suffix(self.buf.as_ref())
            .expect("buf should at least fit the footer");
        let count = footer.restart_count.get() as usize;
        let (entries, offsets) =
            Ref::<_, [U32<LittleEndian>]>::from_suffix_with_elems(rest, count).unwrap();

        // phase 2: binary search for the right restart interval
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

        // phase 3: linearly search through this interval
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
}

#[cfg(test)]
mod tests {
    use bytes::Bytes;
    use crate::base::{DefaultComparer, KeyKind, KeyTrailer, SeqNum, InternalKey};
    use super::*;

    fn make_trailer(seqnum: u64, kind: KeyKind) -> KeyTrailer {
        KeyTrailer::new(
            unsafe { SeqNum::new_unchecked(seqnum) },
            kind,
        )
    }

    fn make_key(s: &str, seqnum: u64) -> InternalKey<DefaultComparer> {
        InternalKey::new(Bytes::copy_from_slice(s.as_bytes()), make_trailer(seqnum, KeyKind::Put))
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
        let result = reader.get(make_key("banana", 1));
        assert_eq!(result.unwrap(), Bytes::from("yellow"));
    }

    #[test]
    fn test_get_missing_key() {
        let buf = build_block(&[
            ("apple", 1, "fruit"),
            ("cherry", 1, "red"),
        ]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert!(reader.get(make_key("banana", 1)).is_none());
    }

    #[test]
    fn test_get_key_before_first() {
        let buf = build_block(&[
            ("banana", 1, "yellow"),
            ("cherry", 1, "red"),
        ]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert!(reader.get(make_key("apple", 1)).is_none());
    }

    #[test]
    fn test_get_key_after_last() {
        let buf = build_block(&[
            ("apple", 1, "fruit"),
            ("banana", 1, "yellow"),
        ]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert!(reader.get(make_key("cherry", 1)).is_none());
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
            let result = reader.get(make_key(&key, 1));
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
        assert_eq!(reader.get(make_key("aaa", 1)).unwrap(), Bytes::from("first"));
        assert_eq!(reader.get(make_key("zzz", 1)).unwrap(), Bytes::from("last"));
    }

    #[test]
    fn test_empty_value() {
        let buf = build_block(&[("key", 1, "")]);
        let reader = BlockReader::<DefaultComparer>::new(buf);
        assert_eq!(reader.get(make_key("key", 1)).unwrap(), Bytes::new());
    }
}
