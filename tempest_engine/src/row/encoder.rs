use bytes::{BufMut, BytesMut};

use crate::{
    base::KeySpace,
    catalog::schema::{TableId, TableSchema},
    ctrl::hlc::HlcTimestamp,
    types::TempestValue,
};

#[derive(Debug)]
pub(crate) struct RowEncoder<'a> {
    table_id: TableId,
    schema: &'a TableSchema,
}

impl<'a> RowEncoder<'a> {
    pub(crate) fn new(table_id: TableId, schema: &'a TableSchema) -> Self {
        Self { table_id, schema }
    }

    fn typecheck(&self, row: &[TempestValue<'_>]) {
        assert_eq!(row.len(), self.schema.columns.len());
        for (val, col) in row.iter().zip(self.schema.columns.iter()) {
            assert!(
                val.ty() == col.ty,
                "invalid type for column '{}': expected {:?}, but got {:?}",
                col.name,
                col.ty,
                val.ty(),
            )
        }
    }

    fn encode_key(&self, row: &[TempestValue<'_>], hlc: HlcTimestamp, key_buf: &mut BytesMut) {
        // -- encode table row key prefix --
        key_buf.put_u8(KeySpace::TableRow as u8);

        // -- encode database id --
        key_buf.put_slice(&self.schema.database_id.to_be_bytes());

        // -- encode table id --
        key_buf.put_slice(&self.table_id.to_be_bytes());

        // -- encode primary key columns --
        let pk_cols: Vec<_> = self
            .schema
            .primary_key
            .iter()
            .map(|&idx| &row[idx])
            .collect();
        for col in pk_cols {
            col.encode_lexical(key_buf);
        }

        // -- encode the hlc timestamp --
        key_buf.put_u64(*hlc);
    }

    fn encode_value(&self, row: &[TempestValue<'_>], value_buf: &mut BytesMut) {
        // -- get all non-pk columns --
        let val_cols = row.iter().enumerate().filter_map(|(idx, val)| {
            if !self.schema.primary_key.contains(&idx) {
                Some(val)
            } else {
                None
            }
        });

        // -- encode all value columns --
        for col in val_cols {
            col.encode(value_buf);
        }
    }

    /// Encodes a full row into `key_buf` and `value_buf`.
    /// `row` is the full row - the encoder picks out PK columns via `schema.primary_key`.
    /// The row must be in order of the schema's column definitions.
    ///
    /// # Panics
    ///
    /// Panics if `row.len() != schema.columns.len()`, or if the type of any
    /// `row[i]` does not match `schema.columns[i].ty`.
    #[instrument(level = "trace")]
    pub(crate) fn encode_row(
        &self,
        row: &[TempestValue<'_>],
        hlc: HlcTimestamp,
        key_buf: &mut BytesMut,
        value_buf: &mut BytesMut,
    ) {
        self.typecheck(row);
        self.encode_key(row, hlc, key_buf);
        self.encode_value(row, value_buf);
    }
}
