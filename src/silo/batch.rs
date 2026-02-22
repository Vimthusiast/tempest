use bytes::{BufMut, BytesMut};
use integer_encoding::VarInt;

use crate::base::{KeyKind, SeqNum};

/// Header:
/// - 8 bytes seqnum
/// - 4 bytes count
///
/// Body:
/// - Record[]
///
/// Record:
/// - KeyKind::Delete   varstring
/// - KeyKind::Put      varstring   varstring
#[derive(Debug)]
pub(crate) struct WriteBatch {
    #[debug("BytesMut(len={},cap={})", buf.len(), buf.capacity())]
    buf: BytesMut,
    count: u32,
    committed: bool,
}

impl WriteBatch {
    /// Create a new write batch, that stores its encoded data in the buffer.
    pub fn new_in(mut buf: BytesMut) -> Self {
        buf.clear();
        buf.put_bytes(0, 12);
        Self {
            buf,
            count: 0,
            committed: false,
        }
    }

    /// Create a new write batch, that already has some data written into `buf`.
    pub fn new_with_content(buf: BytesMut, count: u32) -> Self {
        Self {
            buf,
            count,
            committed: false,
        }
    }

    /// Add a `put KEY=VALUE` command to this batch.
    pub fn put(&mut self, key: &[u8], value: &[u8]) {
        trace!("WriteBatch: put '{:?}'='{:?}'", key, value);
        self.count += 1;
        self.buf.put_u8(KeyKind::Put.into());
        self.put_varint(key.len());
        self.buf.put(key);
        self.put_varint(value.len());
        self.buf.put(value);
    }

    /// Add a `delete KEY` command to this batch.
    pub fn delete(&mut self, key: &[u8]) {
        trace!("WriteBatch: delete '{:?}'", key);
        self.count += 1;
        self.buf.put_u8(KeyKind::Delete.into());
        self.put_varint(key.len());
        self.buf.put(key);
    }

    fn put_varint(&mut self, i: usize) {
        // reserve space
        let varint_size = i.required_space();
        self.buf.put_bytes(0, varint_size);
        // encode varint
        let buflen = self.buf.len();
        let written = i.encode_var(&mut self.buf[buflen - varint_size..]);
        debug_assert_eq!(written, varint_size);
    }

    pub fn commit(&mut self, seqnum: SeqNum) {
        assert!(!self.committed);
        self.buf[0..8].copy_from_slice(&seqnum.get().to_le_bytes());
        self.buf[8..12].copy_from_slice(&self.count.to_le_bytes());
        self.committed = true;
    }

    pub fn take_buf(self) -> BytesMut {
        assert!(
            self.committed,
            "Trying to access a write batch, that was not assigned a seqnum."
        );
        self.buf
    }
}
