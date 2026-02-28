use bytes::{BufMut, BytesMut};
use integer_encoding::VarInt;

use crate::base::{KeyKind, PrettyBytes, SeqNum};

/// # Write Batch
///
/// This defines an aggregation of different write operations into the silo.
///
/// Every batch starts with a header of the following layout:
///
/// ```not_rust
/// +-------------+------------+--- ... ---+
/// | SeqNum (8B) | Count (4B) |  Entries  |
/// +-------------+------------+--- ... ---+
/// ```
///
/// As you can see, after the 12 byte header, there can be up to `u32::MAX` (Count) **Entries**.
///
///
/// There are different entry types, each identified by the [`KeyKind`].
/// Every entry is encoded as the kind, followed by 1 or 2 **varstrings**, depending on the kind.
/// A varstring is a length-prefixed string, where the length itself is also encoded as a varint.
///
/// ```not_rust
/// +-----------+-----------------+-------------------+
/// | Kind (1B) | Key (varstring) | Value (varstring) |
/// +-----------+-----------------+-------------------+
/// ```
///
/// "Key -> Value" is not always a good description. While [`KeyKind::Put`] does set a `Key` to a
/// `Value`, other operations, like range deletions, actually just have two keys as their params.
///
/// The following table shows the format for entries of each [`KeyKind`]:
///
/// ```not_rust
/// Delete      varstring
/// Put         varstring   varstring
// -- TODO --
// RangeDelete
// merging operations
/// ```
#[derive(Debug)]
#[debug("WriteBatch(len={}, count={})", buf.len(), count)]
pub struct WriteBatch {
    buf: BytesMut,
    count: u32,
    committed: bool,
}

impl WriteBatch {
    /// Create a new write batch.
    pub fn new() -> Self {
        let mut buf = BytesMut::with_capacity(4096);
        buf.put_bytes(0, 12);
        Self {
            buf,
            count: 0,
            committed: false,
        }
    }

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

    pub fn new_from_wal(buf: BytesMut) -> Self {
        Self {
            // contains our checked data
            buf,
            // count does not matter, as it has already been written to the buf
            count: 0,
            // this comes from the wal, so it has already been committed
            committed: true,
        }
    }

    /// Add a `put KEY=VALUE` command to this batch.
    pub fn put(&mut self, key: &[u8], value: &[u8]) {
        trace!(
            key = ?PrettyBytes(key), value = ?PrettyBytes(value),
            "write batch: put",
        );
        self.count += 1;
        self.buf.put_u8(KeyKind::Put.into());
        self.put_varint(key.len());
        self.buf.put(key);
        self.put_varint(value.len());
        self.buf.put(value);
    }

    /// Add a `delete KEY` command to this batch.
    pub fn delete(&mut self, key: &[u8]) {
        trace!(
            key = ?PrettyBytes(key),
            "write batch: delete",
        );
        self.count += 1;
        self.buf.put_u8(KeyKind::Delete.into());
        self.put_varint(key.len());
        self.buf.put(key);
    }

    pub(crate) fn put_varint(&mut self, i: usize) {
        // reserve space
        let varint_size = i.required_space();
        self.buf.put_bytes(0, varint_size);
        // encode varint
        let buflen = self.buf.len();
        let written = i.encode_var(&mut self.buf[buflen - varint_size..]);
        debug_assert_eq!(written, varint_size);
    }

    pub(crate) fn commit(&mut self, seqnum: SeqNum) {
        assert!(!self.committed);
        self.buf[0..8].copy_from_slice(&seqnum.get().to_le_bytes());
        self.buf[8..12].copy_from_slice(&self.count.to_le_bytes());
        self.committed = true;
    }

    pub(crate) fn take_buf(self) -> BytesMut {
        assert!(
            self.committed,
            "trying to access a write batch, that was not assigned a seqnum"
        );
        self.buf
    }
}
