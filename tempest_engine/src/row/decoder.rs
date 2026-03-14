use bytes::{Buf, Bytes};
use tempest_core::encoding::{LexicalDecodeError, RawDecodeError};

use crate::{
    base::KeySpace, catalog::schema::TableSchema, ctrl::hlc::HlcTimestamp, types::TempestValue,
};

#[derive(Debug, Display, From, Error)]
pub enum RowDecodeError {
    #[from(skip)]
    #[display("invalid key space: {}", _0)]
    InvalidKeySpace(#[error(not(source))] u8),
    LexicalDecodeError(LexicalDecodeError),
    RawDecodeError(RawDecodeError),
}

#[derive(Debug)]
pub(crate) struct RowDecoder<'a> {
    schema: &'a TableSchema,
}

impl<'a> RowDecoder<'a> {
    pub(crate) fn new(schema: &'a TableSchema) -> Self {
        Self { schema }
    }

    /// Decodes the PK columns and HLC from a key buffer.
    /// Expects the key to start with the KeySpace prefix.
    pub(crate) fn decode_key(
        &self,
        buf: &mut Bytes,
    ) -> Result<(Vec<TempestValue<'static>>, HlcTimestamp), RowDecodeError> {
        // -- strip keyspace prefix --
        let ks = buf.get_u8();
        if ks != KeySpace::TableRow as u8 {
            return Err(RowDecodeError::InvalidKeySpace(ks));
        };

        // -- skip table id (already know it from context) --
        // TODO: should we verify?? -> not our concern
        buf.advance(4);

        // -- decode pk columns in schema order --
        let mut pk_values = Vec::with_capacity(self.schema.columns.len());
        for &idx in &self.schema.primary_key {
            let ty = self.schema.columns[idx].ty;
            let val = TempestValue::decode_lexical(buf, ty)?;
            pk_values.push(val);
        }

        // -- decode hlc suffix (last 8 bytes) --
        let hlc = HlcTimestamp::from_u64(buf.get_u64());

        Ok((pk_values, hlc))
    }

    /// Decodes the non-PK columns from a value buffer.
    pub(crate) fn decode_value(
        &self,
        buf: &mut Bytes,
    ) -> Result<Vec<TempestValue<'static>>, RowDecodeError> {
        // -- get all non-pk columns --
        let val_cols: Vec<_> = self
            .schema
            .columns
            .iter()
            .enumerate()
            .filter_map(|(idx, val)| {
                if !self.schema.primary_key.contains(&idx) {
                    Some(val)
                } else {
                    None
                }
            })
            .collect();

        let mut values = Vec::with_capacity(val_cols.len());
        for (idx, col) in self.schema.columns.iter().enumerate() {
            if !self.schema.primary_key.contains(&idx) {
                let val = TempestValue::decode(buf, col.ty)?;
                values.push(val);
            }
        }

        Ok(values)
    }

    /// Decodes a full row, returning all column values in schema order.
    #[instrument(level = "trace")]
    pub(crate) fn decode_row(
        &self,
        key_buf: &mut Bytes,
        value_buf: &mut Bytes,
    ) -> Result<Vec<TempestValue<'static>>, RowDecodeError> {
        let (pk_vals, _hlc) = self.decode_key(key_buf)?;
        let val_vals = self.decode_value(value_buf)?;

        // -- merge pk and non-pk back into schema order --
        let mut row = Vec::with_capacity(self.schema.columns.len());
        let mut pk_iter = pk_vals.into_iter();
        let mut val_iter = val_vals.into_iter();
        for idx in 0..self.schema.columns.len() {
            if self.schema.primary_key.contains(&idx) {
                row.push(pk_iter.next().unwrap());
            } else {
                row.push(val_iter.next().unwrap());
            }
        }

        Ok(row)
    }
}
