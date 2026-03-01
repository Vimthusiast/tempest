use bytes::{BufMut, Bytes, BytesMut};
use std::marker::PhantomData;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, LittleEndian, Ref, U32, U64};

use crate::base::{Comparer, InternalKey, KeyTrailer};

#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct IndexEntryHeader {
    key_len: U32<LittleEndian>,
    block_offset: U64<LittleEndian>,
    block_size: U32<LittleEndian>,
}

#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct IndexFooter {
    entry_count: U32<LittleEndian>,
}

impl IndexFooter {
    fn new(entry_count: impl Into<U32<LittleEndian>>) -> Self {
        let entry_count = entry_count.into();
        Self { entry_count }
    }
}

pub struct IndexBuilder {
    buf: BytesMut,
    entry_offsets: Vec<u32>,
}

impl IndexBuilder {
    pub fn new() -> Self {
        Self {
            buf: BytesMut::new(),
            entry_offsets: Vec::new(),
        }
    }

    pub fn push<C: Comparer, K: AsRef<[u8]>>(
        &mut self,
        last_key: &InternalKey<C, K>,
        block_offset: u64,
        block_size: u32,
    ) {
        self.entry_offsets.push(self.buf.len() as u32);

        let key = last_key.key().as_ref();
        let header = IndexEntryHeader {
            key_len: (key.len() as u32).into(),
            block_offset: block_offset.into(),
            block_size: block_size.into(),
        };
        self.buf.put(header.as_bytes());
        self.buf.put(key);
        self.buf.put(last_key.trailer().as_bytes());
    }

    pub fn finalize(mut self) -> BytesMut {
        self.buf.put(self.entry_offsets.as_slice().as_bytes());
        let footer = IndexFooter::new(self.entry_offsets.len() as u32);
        self.buf.put(footer.as_bytes());
        self.buf
    }
}

fn parse_index(buf: &[u8]) -> (&[u8], &[U32<LittleEndian>]) {
    let footer_start = buf.len() - size_of::<IndexFooter>();
    let count = IndexFooter::read_from_bytes(&buf[footer_start..])
        .unwrap()
        .entry_count
        .get() as usize;
    let offsets_start = footer_start - count * size_of::<U32<LittleEndian>>();
    let entries = &buf[..offsets_start];
    let offsets = <[U32<LittleEndian>]>::ref_from_bytes(&buf[offsets_start..footer_start]).unwrap();
    (entries, offsets)
}

pub struct IndexReader<C: Comparer> {
    buf: Bytes,
    _marker: PhantomData<C>,
}

impl<C: Comparer> IndexReader<C> {
    pub fn new(buf: Bytes) -> Self {
        Self {
            buf,
            _marker: PhantomData,
        }
    }

    /// Returns the (block_offset, block_size) of the block that may contain `key`,
    /// or None if the key is out of range.
    pub fn get_block_for<K: AsRef<[u8]>>(&self, key: &InternalKey<C, K>) -> Option<(u64, u32)> {
        let key = InternalKey::<C, &[u8]>::new(key.key().as_ref(), key.trailer());
        let (entries, offsets) = parse_index(&self.buf);
        let c = C::default();

        let decode_entry = |offset: usize| -> (InternalKey<C, &[u8]>, u64, u32) {
            let (header, rest) =
                Ref::<_, IndexEntryHeader>::from_prefix(&entries[offset..]).unwrap();
            let key_len = header.key_len.get() as usize;
            let block_offset = header.block_offset.get();
            let block_size = header.block_size.get();
            let entry_key = &rest[..key_len];
            let trailer =
                KeyTrailer::read_from_bytes(&rest[key_len..key_len + size_of::<KeyTrailer>()])
                    .unwrap();
            (
                InternalKey::new(entry_key, trailer),
                block_offset,
                block_size,
            )
        };

        // binary search for the first entry whose key >= search key
        let result = offsets.binary_search_by(|offset| {
            let (entry_key, _, _) = decode_entry(offset.get() as usize);
            c.compare_physical(entry_key.key(), key.key())
        });

        // we still check if first > key, because we just have the last block key in the index
        let i = result.unwrap_or_else(|i| i);

        if i >= offsets.len() {
            return None;
        }

        let (_, block_offset, block_size) = decode_entry(offsets[i].get() as usize);
        Some((block_offset, block_size))
    }
}
