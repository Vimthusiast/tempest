use bytes::{BufMut, BytesMut};

use crate::{
    base::KeySpace, ctrl::hlc::HlcTimestamp, row::resolved::ResolvedTable, types::TempestValue,
};

#[derive(Debug)]
pub(crate) struct RowEncoder<'a> {
    table: &'a ResolvedTable<'a>,
    pk_indices: Vec<usize>,
}

impl<'a> RowEncoder<'a> {
    pub(crate) fn new(table: &'a ResolvedTable<'a>) -> Self {
        let pk_indices = table
            .primary_key
            .iter()
            .map(|fid| table.fields.keys().position(|k| k == fid).unwrap())
            .collect();
        Self { table, pk_indices }
    }

    fn typecheck(&self, row: &[TempestValue<'_>]) {
        assert_eq!(row.len(), self.table.fields.len());
        for (val, def) in row.iter().zip(self.table.fields.values()) {
            assert!(
                val.ty() == def.ty,
                "invalid type for column '{}': expected {:?}, but got {:?}",
                def.name,
                def.ty,
                val.ty(),
            )
        }
    }

    fn encode_key(&self, row: &[TempestValue<'_>], hlc: HlcTimestamp, key_buf: &mut BytesMut) {
        // -- encode table row key prefix --
        key_buf.put_u8(KeySpace::TableRow as u8);

        // -- encode table id --
        key_buf.put_slice(&self.table.id.to_be_bytes());

        // -- encode primary key columns --
        for &idx in &self.pk_indices {
            row[idx].encode_lexical(key_buf);
        }

        // -- encode the hlc timestamp --
        key_buf.put_u64(*hlc);
    }

    fn encode_value(&self, row: &[TempestValue<'_>], value_buf: &mut BytesMut) {
        // -- get all non-pk columns --
        // TODO: precompute and store this?
        let val_cols = row.iter().enumerate().filter_map(|(idx, val)| {
            if !self.pk_indices.contains(&idx) {
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
    /// The row must be in order of the schema's column definitions, ordered by field ID.
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
