use std::sync::Arc;

use crate::{
    core::{
        DecodeError, NS, SliceReader, TempestReader, TempestStr, TempestWriter,
        value::{TempestType, TempestValue},
    },
    kv::KvStore,
};

#[derive(Debug)]
pub(crate) struct ColumnSchema {
    /// Name of this column. May not contain `\0`.
    name: TempestStr<'static>,
    // value type
    col_type: TempestType,
}

#[derive(Debug)]
pub(crate) struct TableSchema {
    /// Name of this table. May not contain `\0`.
    name: TempestStr<'static>,
    columns: Vec<ColumnSchema>,
    /// Indices of the primary key columns
    ///
    /// **Example:**
    ///
    /// `[1, 3]` means that `columns[1]` and `columns[3]` both compose the primary key together.
    /// It is important that the ordering of these stays consistent across operations: When this is
    /// defined as `[1, 3]`, it means that the priority of the database index is also meant to be:
    /// "first column 1, then column 3".
    primary_key: Vec<usize>,
}

impl TableSchema {
    pub(crate) fn value_indices(&self) -> Vec<usize> {
        (0..self.columns.len())
            .filter(|idx| !self.primary_key.contains(idx))
            .collect()
    }
}

#[derive(Debug)]
pub(crate) struct DatabaseSchema {
    /// Name of this database. May not contain `\0`.
    name: TempestStr<'static>,
    tables: Vec<TableSchema>,
}

/// Maps database names, to their table schemas.
/// Persists them in the [`KvStore`] for retrieval (later).
///
/// [`KvStore`]: crate::kv::KvStore
pub(crate) struct Catalog {
    kv: Arc<dyn KvStore>,
    cache: Vec<TableSchema>,
}

impl Catalog {
    pub(crate) fn init(kv: Arc<dyn KvStore>) -> Catalog {
        // TODO: read from and store schema to kv
        let cache = Vec::new();
        Self { kv, cache }
    }
}

pub(crate) struct TempestRow {
    pub values: Vec<TempestValue>,
}

#[derive(Debug)]
pub(crate) struct RowEncoder<'a> {
    schema: &'a TableSchema,
    db: &'a TempestStr<'a>,
    prefix_bytes: Vec<u8>,
    /// Pre-calculated indices of columns that live in the value blob.
    /// This avoids re-scanning the `primary_key` during every encode.
    value_indices: Vec<usize>,
}

impl<'a> RowEncoder<'a> {
    fn new(db: &'a TempestStr<'a>, schema: &'a TableSchema) -> Self {
        let value_indices = schema.value_indices();
        let mut prefix_bytes = Vec::with_capacity(3 + db.len() + schema.name.len());
        prefix_bytes.write_u8(NS::DATA.into());
        prefix_bytes.write_string_null_terminated(db);
        prefix_bytes.write_string_null_terminated(&schema.name);
        Self {
            schema,
            db,
            prefix_bytes,
            value_indices,
        }
    }

    fn encode(&self, values: &[TempestValue]) -> (Vec<u8>, Vec<u8>) {
        let mut key_bytes = self.prefix_bytes.clone();
        for idx in &self.schema.primary_key {
            // NB: Use encode_lexic here, to keep lexicographical ordering of keys on byte level
            values[*idx].encode_lexic(&mut key_bytes);
        }

        let mut value_bytes = Vec::new();
        for idx in &self.value_indices {
            values[*idx].encode(&mut value_bytes);
        }

        (key_bytes, value_bytes)
    }
}

#[derive(Debug)]
pub(crate) struct RowDecoder<'a> {
    schema: &'a TableSchema,
    db: &'a TempestStr<'a>,
    key_prefix_len: usize,
    value_indices: Vec<usize>,
}

impl<'a> RowDecoder<'a> {
    pub(crate) fn new(db: &'a TempestStr<'a>, schema: &'a TableSchema) -> Self {
        let value_indices = schema.value_indices();
        let key_prefix_len = 3 + db.len() + schema.name.len();
        Self {
            schema,
            db,
            key_prefix_len,
            value_indices,
        }
    }

    /// Decodes a row from the raw key bytes and value bytes. Does not validate the key prefix.
    /// The key prefix is instead skipped over, to increase decoding speed.
    pub(crate) fn decode(
        &self,
        key_bytes: &[u8],
        value_bytes: &[u8],
    ) -> Result<Vec<TempestValue>, DecodeError> {
        let mut values = vec![None; self.schema.columns.len()];

        let mut key_reader = SliceReader::new(key_bytes);
        // PERF: Just skip over the key prefix, i.e. namespace, db name, table name
        key_reader.advance(self.key_prefix_len)?;
        for &pk_idx in &self.schema.primary_key {
            let col_schema = &self.schema.columns[pk_idx];
            let val = TempestValue::decode_lexic(&mut key_reader, col_schema.col_type)?;
            values[pk_idx] = Some(val);
        }
        if !key_reader.is_eof() {
            return Err(DecodeError::RemainingBytes(
                key_reader.bytes_left(),
                "Key-bytes reader",
            ));
        }

        let mut value_reader = SliceReader::new(value_bytes);
        for &col_idx in &self.value_indices {
            let col_schema = &self.schema.columns[col_idx];
            let val = TempestValue::decode_lexic(&mut value_reader, col_schema.col_type)?;
            values[col_idx] = Some(val);
        }
        if !value_reader.is_eof() {
            return Err(DecodeError::RemainingBytes(
                value_reader.bytes_left(),
                "Value-bytes reader",
            ));
        }

        Ok(values
            .into_iter()
            .map(|v| v.expect("every value should have been filled"))
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;

    #[test]
    fn test_row_encoder_decoder() {
        let db = TempestStr::try_from("db1").unwrap();
        let schema = TableSchema {
            name: "table1".try_into().unwrap(),
            columns: vec![
                ColumnSchema {
                    name: "int8_col".try_into().unwrap(),
                    col_type: TempestType::Int8,
                },
                ColumnSchema {
                    name: "bool_col".try_into().unwrap(),
                    col_type: TempestType::Bool,
                },
            ],
            // primary key (int8_col)
            primary_key: vec![0],
        };
        let row_encoder = RowEncoder::new(&db, &schema);
        println!("initialized row encoder: {:?}", row_encoder);
        let row_decoder = RowDecoder::new(&db, &schema);
        println!("initialized row decoder: {:?}", row_decoder);
        let values = [(0, true), (1, false), (2, false), (4, true), (5, false)]
            .map(|(id, b)| (TempestValue::Int8(id), TempestValue::Bool(b)));

        for (v1, v2) in values {
            let (key_bytes, value_bytes) = row_encoder.encode(&[v1.clone(), v2.clone()]);
            println!(
                "Encoded row ({:?}, {:?}) to key: [{}], value: [{}]",
                v1,
                v2,
                key_bytes.iter().map(|v| format!("{:02X}", v)).format(" "),
                value_bytes.iter().map(|v| format!("{:02X}", v)).format(" ")
            );

            let (decoded_v1, decoded_v2) = row_decoder
                .decode(&key_bytes, &value_bytes)
                .unwrap()
                .into_iter()
                .collect_tuple::<(_, _)>()
                .expect("expected to have two columns returned");
            println!("Decoded row: ({:?}, {:?})", decoded_v1, decoded_v2);

            assert_eq!(v1, decoded_v1);
            assert_eq!(v2, decoded_v2);
        }
    }
}
