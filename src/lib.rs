use std::{collections::BTreeMap, io, string::FromUtf8Error, sync::Arc};

use futures::StreamExt;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

pub use kv::*;
pub use query::*;

#[macro_use]
extern crate derive_more;

mod kv;
mod query;

fn encode_i64_sortable(val: i64) -> [u8; 8] {
    let unsigned = (val as u64) ^ 0x8000_0000_0000_0000;
    unsigned.to_be_bytes()
}

fn decode_i64_sortable(bytes: [u8; 8]) -> i64 {
    let unsigned = u64::from_be_bytes(bytes);
    (unsigned ^ 0x8000_0000_0000_0000) as i64
}

/// Encodes a null-terminated string into a buffer. The string must not contain any null byte.
fn encode_string_null_terminated(buf: &mut Vec<u8>, s: impl AsRef<[u8]>) {
    let bytes = s.as_ref();
    for (pos, &b) in bytes.iter().enumerate() {
        debug_assert_ne!(b, 0u8, "string contains null-byte at position {}", pos)
    }
    buf.extend_from_slice(bytes);
    buf.push(0);
}

/// Decodes a null-termianted string from a buffer, advancing the slice past it.
fn decode_string_null_terminated(buf: &mut &[u8]) -> io::Result<String> {
    let Some(end) = buf.iter().position(|&b| b == 0) else {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "reached end of slice without encountering null-byte",
        ));
    };
    let (s_bytes, remaining) = buf.split_at(end + 1);
    let s = std::str::from_utf8(&s_bytes[..end])
        .map_err(|err| io::Error::new(io::ErrorKind::Other, err))?;
    *buf = remaining;
    Ok(s.to_string())
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[repr(u8)]
pub enum DataType {
    /// 1 byte big. 0x0 for `false`, 0x1 for `true`.
    Bool = 0,
    /// i64 encoded in big-endian byte order.
    Int8 = 1,
    // TODO: implement encode/decode strat that conserves lexicographical ordering.
    // Float = 2,
    /// A varint `length`, followed by `length` bytes.
    String = 3,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    Bool(bool),
    Int8(i64),
    String(String),
}

#[derive(Debug, From, Display, Error)]
pub enum ValueDecodeError {
    InvalidVarInt,
    EOF,
    InvalidUTF8(FromUtf8Error),
}

impl Value {
    /// Decodes a Value of the expected DataType from a byte slice reader, advancing the reader
    /// past the read bytes.
    /// When decoding fails, does not advance reader and safely returns the error.
    pub fn decode(reader: &mut &[u8], data_type: DataType) -> Result<Self, ValueDecodeError> {
        match data_type {
            DataType::Bool => {
                if reader.len() < 1 {
                    return Err(ValueDecodeError::EOF);
                }
                let byte = reader[0];

                *reader = &reader[1..];
                // TODO: error on invalid value; for now, recover to true
                Ok(Value::Bool(byte != 0))
            }
            DataType::Int8 => {
                if reader.len() < 8 {
                    return Err(ValueDecodeError::EOF);
                }
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&reader[0..8]);
                let val = decode_i64_sortable(buf);

                *reader = &reader[8..];
                Ok(Value::Int8(val))
            }
            DataType::String => {
                use integer_encoding::VarIntReader;
                let len: usize = reader
                    .read_varint()
                    .map_err(|_| ValueDecodeError::InvalidVarInt)?;

                if reader.len() < len {
                    return Err(ValueDecodeError::EOF);
                }
                let (s_bytes, remaining) = reader.split_at(len);
                let s = String::from_utf8(s_bytes.to_vec())?;

                *reader = remaining;
                Ok(Value::String(s))
            }
        }
    }

    pub fn encode(&self, buf: &mut Vec<u8>) {
        match self {
            Value::Bool(b) => {
                buf.push(if *b { 1 } else { 0 });
            }
            Value::Int8(i) => {
                let encoded = encode_i64_sortable(*i);
                buf.extend_from_slice(&encoded);
            }
            Value::String(s) => {
                use integer_encoding::VarIntWriter;
                buf.write_varint(s.len())
                    .expect("Internal buffer failure: Encoding varints to a vec should succeed (unless OOM)");
                buf.extend_from_slice(s.as_bytes());
            }
        }
    }
}

#[derive(Debug, From, Display, Error)]
pub enum RowDecodeError {
    ValueDecodeError(ValueDecodeError),
}

#[derive(Debug)]
pub struct Row {
    values: Vec<Value>,
}

impl Row {
    pub fn decode(reader: &mut &[u8], schema: &[DataType]) -> Result<Self, RowDecodeError> {
        let mut values = Vec::with_capacity(schema.len());

        for data_type in schema {
            let val = Value::decode(reader, *data_type)?;
            values.push(val);
        }

        todo!()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Column {
    pub(crate) name: String,
    pub(crate) data_type: DataType,
    //pub(crate) nullable: bool,
    //pub(crate) default: Option<Expr>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableSchema {
    /// Every column's name and it's type.
    pub(crate) columns: Vec<Column>,
    /// The columns used to uniquely identify rows of this table.
    pub(crate) primary_key: Vec<usize>,
}

impl TableSchema {
    pub fn new(columns: Vec<Column>, primary_key: Vec<usize>) -> Self {
        Self {
            columns,
            primary_key,
        }
    }
}

/// Catalog implementation. The catalog keeps track of the database metadata,
/// such as the [`TableSchema`]s.
///
/// [`TableSchema`]: TableSchema
pub struct Catalog {
    kv: Arc<dyn KvStore>,
    /// Maps `DB_NAME` and `TABLE_NAME` to the schema for that table.
    cache: RwLock<BTreeMap<(String, String), TableSchema>>,
}

impl Catalog {
    pub async fn bootstrap(kv: Arc<dyn KvStore>) -> Self {
        let mut stream = kv.scan(
            CATALOG_NS.to_be_bytes().to_vec(),
            (CATALOG_NS + 1).to_be_bytes().to_vec(),
        );
        let cache = BTreeMap::new();

        while let Some((_key, _value)) = stream.next().await {
            todo!("implement reading of old schema");
        }
        drop(stream);

        let cache = RwLock::new(cache);

        Self { kv, cache }
    }

    pub async fn set_schema(&self, database: String, table: String, schema: TableSchema) {
        let mut cache_guard = self.cache.write().await;
        match cache_guard.entry((database, table)) {
            std::collections::btree_map::Entry::Vacant(e) => {
                e.insert(schema);
            }
            std::collections::btree_map::Entry::Occupied(_e) => {
                todo!("implement schema modification")
            }
        }
    }

    pub async fn get_schema(&self, database: String, table: String) -> Option<TableSchema> {
        return self.cache.read().await.get(&(database, table)).cloned();
    }
}

const CATALOG_NS: u8 = 0;
const DATA_NS: u8 = 1;

/// Tempest implementation. Always uses the first byte of the key for the namespace.
///
/// ## Datatypes
///
/// ### Boolean
///
/// Stored as a single byte of `0` or `1`.
///
/// ### Integer
///
/// Encoded in a way that retains lexicographical ordering for negative values.
///
/// ### String
///
/// Strings must only contain valid UTF-8. For other data, see Blob (todo).
///
// TODO:
// - Blob
///
/// ## Basic Key Layout
///
/// `[NS] + [DB_NAME] + [0] + [TABLE_NAME] + [0]`
///
/// - `[NS]`: Namespace (Single Byte)
/// - `[DB_NAME]`: Database Name (String; null-terminated)
/// - `[TABLE_NAME]`: Table Name (String; null-terminated)
///
/// ## Namespaces
///
/// - [`CATALOG_NS`]: catalog namespace
/// - [`DATA_NS`]: data namespace
///
/// ### Catalog Namespace
///
/// This contains the catalog data, which is handled by the [`Catalog`] instance.
///
/// ### Data Namespace
///
/// This contains the data of all databases.
///
/// [`CATALOG_NS`]: CATALOG_NS
/// [`DATA_NS`]: DATA_NS
/// [`Catalog`]: Catalog
pub struct Tempest {
    kv: Arc<dyn KvStore>,
    catalog: Catalog,
}

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init<KV: KvStore + 'static>(kv: KV) -> Self {
        let kv = Arc::new(kv);
        let catalog = Catalog::bootstrap(kv.clone()).await;
        Self { kv, catalog }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    pub fn test_value_encoding_decoding() {
        macro_rules! test_for {
            ($buf:ident, $value:expr, $dt:expr) => {{
                $buf.clear();
                let val = $value;
                val.encode(&mut $buf);
                let mut slice = $buf.as_slice();
                let value_dec = Value::decode(&mut slice, $dt).unwrap();
                assert_eq!(slice.len(), 0, "reader should be exhausted");
                assert_eq!(value_dec, val, "decoded value should equal original value");
            }};
        }

        macro_rules! test_for_bool {
            ($buf:ident, $val:expr) => {
                test_for!($buf, Value::Bool($val), DataType::Bool)
            };
        }

        macro_rules! test_for_integer {
            ($buf:ident, $val:expr) => {
                test_for!($buf, Value::Int8($val), DataType::Int8)
            };
        }

        macro_rules! test_for_text {
            ($buf:ident, $val:expr) => {{
                let s = String::from($val);
                test_for!($buf, Value::String(s), DataType::String);
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
            assert_eq!(strings[pos], &result);
            pos += 1;
        }
    }
}
