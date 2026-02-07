use crate::core::{
    TempestKey, TempestStr,
    value::{TempestType, TempestValue},
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
    //kv: Arc<dyn KvStore>
    cache: Vec<TableSchema>,
}

pub(crate) struct TempestRow {
    pub values: Vec<TempestValue>,
}

pub(crate) struct RowEncoder<'a> {
    schema: &'a TableSchema,
    db: &'a TempestStr<'a>,
    /// Pre-calculated indices of columns that live in the value blob.
    /// This avoids re-scanning the `primary_key` during every encode.
    value_indices: Vec<usize>,
}

impl<'a> RowEncoder<'a> {
    fn new(db: &'a TempestStr<'a>, schema: &'a TableSchema) -> Self {
        let value_indices = (0..schema.columns.len())
            .filter(|idx| !schema.primary_key.contains(idx))
            .collect();
        Self {
            schema,
            db,
            value_indices,
        }
    }

    fn encode(&self, values: Vec<TempestValue>) -> (Vec<u8>, Vec<u8>) {
        let mut key_bytes = Vec::new();
        let mut pk_bytes = Vec::new();
        for idx in &self.schema.primary_key {
            // NB: Use encode_lexic here, to keep lexicographical ordering of keys on byte level
            values[*idx].encode_lexic(&mut pk_bytes);
        }
        let key = TempestKey::new_borrowed(
            self.db.borrowed_clone(),
            self.schema.name.borrowed_clone(),
            &pk_bytes,
        );
        key.encode(&mut key_bytes);

        let mut value_bytes = Vec::new();
        for idx in &self.value_indices {
            values[*idx].encode(&mut value_bytes);
        }

        (key_bytes, value_bytes)
    }
}

// TODO: RowDecoder<'a>
