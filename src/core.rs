use std::{
    borrow::Cow,
    io,
    str::{self, Utf8Error},
    string::FromUtf8Error,
};

use serde::{Deserialize, Serialize};

pub(crate) const CATALOG_NS: u8 = 0;
pub(crate) const DATA_NS: u8 = 1;

pub(crate) fn encode_i64_sortable(val: i64) -> [u8; 8] {
    let unsigned = (val as u64) ^ 0x8000_0000_0000_0000;
    unsigned.to_be_bytes()
}

pub(crate) fn decode_i64_sortable(bytes: [u8; 8]) -> i64 {
    let unsigned = u64::from_be_bytes(bytes);
    (unsigned ^ 0x8000_0000_0000_0000) as i64
}

/// Encodes a null-terminated byte sequence into a buffer. The string may contain null bytes, at
/// the cost of potentially increased encoded size.
/// Most often (without \0 occurances), for strings the size will be `s.len() + 2`; this knowledge
/// may be used for pre-allocating the buffer to fit this amount of bytes.
pub(crate) fn encode_bytes_null_terminated_escaped(buf: &mut Vec<u8>, s: impl AsRef<[u8]>) {
    let bytes = s.as_ref();
    for &b in bytes {
        if b == 0 {
            // null bytes within get escaped by being followed with a \xff
            buf.push(0x00);
            buf.push(0xFF);
        } else {
            buf.push(b);
        }
    }
    // double null-byte \0\0 is the new escape sequence
    buf.push(0x00);
    buf.push(0x00);
}

/// Decodes a null-termianted byte sequence with internal null bytes from a buffer,
/// advancing the slice past it.
pub(crate) fn decode_bytes_null_terminated_escaped(
    buf: &mut &[u8],
) -> Result<Vec<u8>, DecodeError> {
    // arbitrarily sized pre-allocation of 32 bytes, which is most often enough
    let mut result = Vec::with_capacity(32);
    let mut i = 0;
    loop {
        if i + 1 >= buf.len() {
            return Err(DecodeError::EOF);
        }
        match (buf[i], buf[i + 1]) {
            // terminator null-bytes \0\0
            (0x00, 0x00) => {
                *buf = &buf[i + 2..];
                return Ok(result);
            }
            // escaped null-byte \0\xFF
            (0, 0xFF) => {
                result.push(0);
                i += 2;
            }
            // normal byte
            (b, _) => {
                result.push(b);
                i += 1;
            }
        }
    }
}

/// Encodes a null-terminated string into a buffer. The string must not contain any null byte.
pub(crate) fn encode_string_null_terminated(buf: &mut Vec<u8>, s: &str) {
    let bytes = s.as_bytes();
    for (pos, &b) in bytes.iter().enumerate() {
        debug_assert_ne!(b, 0u8, "string contains null-byte at position {}", pos)
    }
    buf.extend_from_slice(bytes);
    buf.push(0);
}

/// Decodes a null-termianted string from a buffer, advancing the slice past it.
pub(crate) fn decode_string_null_terminated<'buf>(
    buf: &mut &'buf [u8],
) -> Result<&'buf str, DecodeError> {
    let Some(end) = buf.iter().position(|&b| b == 0) else {
        return Err(DecodeError::EOF);
    };
    let (s_bytes, remaining) = buf.split_at(end + 1);
    let s = str::from_utf8(&s_bytes[..end])?;
    *buf = remaining;
    Ok(s)
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[repr(u8)]
pub enum DataType {
    /// 1 byte big. 0x0 for `false`, 0x1 for `true`.
    Bool = 0,
    /// i64 encoded in big-endian byte order.
    Int8 = 1,
    // TODO: implement encode/decode strat that conserves lexicographical ordering.
    // Float8 = 2,
    /// A varint `length`, followed by `length` bytes.
    String = 3,
    // Blob
    // Bytes(u8) // A binary value with a schema-fixed length; at most 255 bytes long?
}

#[derive(Debug, From, Display, Error)]
pub enum DecodeError {
    InvalidVarInt,
    EOF,
    FromUtf8Error(FromUtf8Error),
    Utf8Error(Utf8Error),
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Key<'a> {
    db: Cow<'a, str>,
    table: Cow<'a, str>,
    /// The encoded bytes of the primary key(s).
    pk_bytes: Cow<'a, [u8]>,
}

impl<'a> Key<'a> {
    pub(crate) fn new_owned(db: String, table: String, pk_bytes: Vec<u8>) -> Key<'static> {
        Key {
            db: Cow::Owned(db),
            table: Cow::Owned(table),
            pk_bytes: Cow::Owned(pk_bytes),
        }
    }

    pub(crate) fn new_borrowed(db: &'a str, table: &'a str, pk_bytes: &'a [u8]) -> Key<'a> {
        Key {
            db: Cow::Borrowed(db),
            table: Cow::Borrowed(table),
            pk_bytes: Cow::Borrowed(pk_bytes),
        }
    }

    pub(crate) fn into_static(self) -> Key<'static> {
        Key {
            db: Cow::Owned(self.db.into_owned()),
            table: Cow::Owned(self.table.into_owned()),
            pk_bytes: Cow::Owned(self.pk_bytes.into_owned()),
        }
    }

    pub(crate) fn encode(&self) -> Vec<u8> {
        // the expected size of the key, used for preallocation of the vec
        let key_size =
            // namespace
            1
            // db name + null-term
            + self.db.len() + 1
            // table name + null-term
            + self.table.len() + 1
            // primary key bytes (already encoded)
            + self.pk_bytes.len();

        let mut key = Vec::with_capacity(key_size);
        key.push(DATA_NS);
        encode_string_null_terminated(&mut key, &self.db);
        encode_string_null_terminated(&mut key, &self.table);
        key.extend_from_slice(&self.pk_bytes);
        key
    }

    pub(crate) fn decode(buf: &mut &'a [u8]) -> Result<Key<'a>, DecodeError> {
        if buf.len() < 1 {
            return Err(DecodeError::EOF);
        }
        let ns = buf[0];
        *buf = &buf[1..];
        debug_assert_eq!(
            ns, DATA_NS,
            "Keys should always be within the data namespace"
        );
        let db = decode_string_null_terminated(buf)?;
        let table = decode_string_null_terminated(buf)?;
        // pk is in the remaining bytes
        let pk_bytes = &buf[..];
        *buf = &[];

        Ok(Self {
            db: Cow::Borrowed(db),
            table: Cow::Borrowed(table),
            pk_bytes: Cow::Borrowed(pk_bytes),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DataValue<'a> {
    Bool(bool),
    Int8(i64),
    String(Cow<'a, str>),
}

impl<'a> DataValue<'a> {
    pub fn encode(&self, buf: &mut Vec<u8>) {
        match self {
            DataValue::Bool(b) => {
                buf.push(if *b { 1 } else { 0 });
            }
            DataValue::Int8(i) => {
                buf.extend_from_slice(&i.to_be_bytes());
            }
            DataValue::String(s) => {
                use integer_encoding::VarIntWriter;
                buf.write_varint(s.len())
                    .expect("Internal buffer failure: Encoding varints to a vec should succeed (unless OOM)");
                buf.extend_from_slice(s.as_bytes());
            }
        }
    }

    /// Decodes a Value of the expected DataType from a byte slice reader, advancing the reader
    /// past the read bytes.
    /// When decoding fails, does not advance reader and safely returns the error.
    pub fn decode(reader: &mut &'a [u8], data_type: DataType) -> Result<Self, DecodeError> {
        match data_type {
            DataType::Bool => {
                if reader.len() < 1 {
                    return Err(DecodeError::EOF);
                }
                let byte = reader[0];

                *reader = &reader[1..];
                // TODO: error on invalid value; for now, recover to true
                Ok(DataValue::Bool(byte != 0))
            }
            DataType::Int8 => {
                if reader.len() < 8 {
                    return Err(DecodeError::EOF);
                }
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&reader[..8]);
                let val = i64::from_be_bytes(buf);

                *reader = &reader[8..];
                Ok(DataValue::Int8(val))
            }
            DataType::String => {
                use integer_encoding::VarIntReader;
                let len: usize = reader
                    .read_varint()
                    .map_err(|_| DecodeError::InvalidVarInt)?;

                if reader.len() < len {
                    return Err(DecodeError::EOF);
                }
                let (s_bytes, remaining) = reader.split_at(len);
                let s = str::from_utf8(s_bytes)?;

                *reader = remaining;
                Ok(DataValue::String(Cow::Borrowed(s)))
            }
        }
    }

    // This way of encoding keeps lexicographical ordering, at the cost of additional compute power
    // and increased final size.
    pub fn encode_lexicographically(&self, buf: &mut Vec<u8>) {
        match self {
            DataValue::Bool(b) => {
                buf.push(if *b { 1 } else { 0 });
            }
            DataValue::Int8(i) => {
                let encoded = encode_i64_sortable(*i);
                buf.extend_from_slice(&encoded);
            }
            DataValue::String(s) => {
                // this is enough, as long as the value does not contain any null-bytes (unlikely)
                buf.reserve(s.len() + 2);
                encode_bytes_null_terminated_escaped(buf, s.as_bytes());
            }
        }
    }

    /// Decodes a Value of the expected [`DataType`] from a byte slice reader, advancing the reader
    /// past the read bytes.
    /// When decoding fails, does not advance reader and safely returns the error.
    pub fn decode_lexicographically(
        reader: &mut &[u8],
        data_type: DataType,
    ) -> Result<Self, DecodeError> {
        match data_type {
            DataType::Bool => {
                if reader.len() < 1 {
                    return Err(DecodeError::EOF);
                }
                let byte = reader[0];

                *reader = &reader[1..];
                Ok(DataValue::Bool(byte != 0))
            }
            DataType::Int8 => {
                if reader.len() < 8 {
                    return Err(DecodeError::EOF);
                }
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&reader[..8]);
                let decoded = decode_i64_sortable(buf);

                *reader = &reader[8..];
                Ok(DataValue::Int8(decoded))
            }
            DataType::String => {
                let bytes = decode_bytes_null_terminated_escaped(reader)?;
                let s = String::from_utf8(bytes)?;
                Ok(DataValue::String(Cow::Owned(s)))
            }
        }
    }
}

#[derive(Debug)]
pub struct Row<'a> {
    values: Vec<DataValue<'a>>,
}

impl<'a> Row<'a> {
    pub fn decode(reader: &mut &[u8], schema: &[DataType]) -> Result<Self, DecodeError> {
        let mut values = Vec::with_capacity(schema.len());

        for data_type in schema {
            let val = DataValue::decode(reader, *data_type)?;
            values.push(val);
        }

        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_null_terminated_encoding_decoding() {
        let strings = ["apple", "orange", "banana"];
        let mut buf: Vec<u8> = Vec::new();
        for s in strings {
            encode_string_null_terminated(&mut buf, s);
        }
        let mut slice = &buf[..];
        let mut pos = 0;
        while slice.len() > 0 {
            let result = decode_string_null_terminated(&mut slice).unwrap();
            assert_eq!(&strings[pos], &result);
            pos += 1;
        }
    }

    #[test]
    fn test_bytes_null_terminated_escaped_encoding_decoding() {
        let byte_seqs = [
            "apples\0with\0apple-juice",
            "oranges\0with\0orange-juice",
            "banana-juice without nulls",
            "strawberry\0sorbet",
        ]
        .map(|s| s.as_bytes());
        let mut buf: Vec<u8> = Vec::new();
        for s in byte_seqs {
            encode_bytes_null_terminated_escaped(&mut buf, s);
        }

        let mut slice = &buf[..];
        let mut pos = 0;
        while slice.len() > 0 {
            let result = decode_bytes_null_terminated_escaped(&mut slice).unwrap();
            assert_eq!(byte_seqs[pos], result);
            pos += 1;
        }
    }

    #[test]
    pub fn test_value_encoding_decoding() {
        macro_rules! test_for {
            ($buf:ident, $value:expr, $dt:expr) => {{
                $buf.clear();
                let val = $value;
                val.encode(&mut $buf);
                let mut slice = $buf.as_slice();
                let value_dec = DataValue::decode(&mut slice, $dt).unwrap();
                assert_eq!(slice.len(), 0, "reader should be exhausted");
                assert_eq!(value_dec, val, "decoded value should equal original value");
            }};
        }

        macro_rules! test_for_bool {
            ($buf:ident, $val:expr) => {
                test_for!($buf, DataValue::Bool($val), DataType::Bool)
            };
        }

        macro_rules! test_for_integer {
            ($buf:ident, $val:expr) => {
                test_for!($buf, DataValue::Int8($val), DataType::Int8)
            };
        }

        macro_rules! test_for_text {
            ($buf:ident, $val:expr) => {{
                let s = String::from($val);
                test_for!($buf, DataValue::String(s.into()), DataType::String);
            }};
        }

        // the buffer to encode into/decode from
        // only allocated once for mem optimization
        let mut buf: Vec<u8> = Vec::new();

        // -- Boolean --
        test_for_bool!(buf, true);
        test_for_bool!(buf, false);

        // -- Integer --
        test_for_integer!(buf, 0);
        test_for_integer!(buf, 1);
        test_for_integer!(buf, -1);
        test_for_integer!(buf, i64::MAX);
        test_for_integer!(buf, i64::MIN);

        // -- Text --
        // empty string
        test_for_text!(buf, "");
        // basic word
        test_for_text!(buf, "apple");
        // long string
        test_for_text!(buf, "A".repeat(2 << 12));
    }

    #[test]
    fn test_key_encoding_decoding() {
        let key = Key::new_borrowed("db1", "table1", &[1, 2, 3]);
        let encoded = key.encode();
        let mut slice = &encoded[..];
        let decoded = match Key::decode(&mut slice) {
            Ok(v) => v,
            Err(e) => panic!("could not decode key: {}", e),
        };
        assert_eq!(decoded, key, "decoded key does not match original");
        assert_eq!(slice.len(), 0, "decoded slice/buffer should be exhausted");
    }
}
