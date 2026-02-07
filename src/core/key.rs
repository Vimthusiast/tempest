use std::borrow::Cow;

use crate::core::{
    NS,
    errors::TempestError,
    io::{TempestReader, TempestWriter},
    primitives::TempestStr,
};

/// A key for a value within tempest.
/// Generally every key must be stored in the [`NS::DATA`] namespace.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TempestKey<'a> {
    /// Null-terminated string that identifies the database.
    /// Must not contain any `\0` byte.
    db: TempestStr<'a>,
    /// Null-terminated string that identifies the table.
    /// Must not contain any `\0` byte.
    table: TempestStr<'a>,
    /// Final byte-encoded version of the primary key(s).
    /// May contain `\0` bytes.
    pk_bytes: Cow<'a, [u8]>,
}

impl TempestKey<'_> {
    #[inline(always)]
    pub(crate) const fn prefix_size(db_len: usize, table_len: usize) -> usize {
        return
            // namespace
            1
            // db name + null-term
            + db_len + 1
            // table name + null-term
            + table_len + 1;
    }

    pub(crate) fn encode_prefix<W: TempestWriter>(
        writer: &mut W,
        db: TempestStr<'_>,
        table: TempestStr<'_>,
    ) {
        let prefix_size = Self::prefix_size(db.len(), table.len());
        writer.reserve(prefix_size);
        writer.write_u8(NS::DATA as u8);
        writer.write_string_null_terminated(&db);
        writer.write_string_null_terminated(&table);
    }

    pub(crate) fn new_borrowed<'a>(
        db: TempestStr<'a>,
        table: TempestStr<'a>,
        pk_bytes: &'a [u8],
    ) -> TempestKey<'a> {
        TempestKey {
            db,
            table,
            pk_bytes: pk_bytes.into(),
        }
    }

    pub(crate) fn new_owned(
        db: TempestStr<'static>,
        table: TempestStr<'static>,
        pk_bytes: Cow<'static, [u8]>,
    ) -> TempestKey<'static> {
        TempestKey {
            db,
            table,
            pk_bytes,
        }
    }

    pub(crate) fn into_static(self) -> TempestKey<'static> {
        TempestKey {
            db: self.db.into_static(),
            table: self.table.into_static(),
            pk_bytes: Cow::Owned(self.pk_bytes.into_owned()),
        }
    }

    pub(crate) fn encode<W: TempestWriter>(&self, writer: &mut W) {
        let key_size = Self::prefix_size(self.db.len(), self.table.len()) + self.pk_bytes.len();
        writer.reserve(key_size);
        writer.write_u8(NS::DATA as u8);
        writer.write_string_null_terminated(&self.db);
        writer.write_string_null_terminated(&self.table);
        writer.write_bytes(&self.pk_bytes);
    }

    pub(crate) fn decode<'buf, R: TempestReader<'buf>>(
        reader: &mut R,
    ) -> Result<TempestKey<'buf>, TempestError> {
        let ns: NS = reader.read_u8()?.try_into()?;
        if !matches!(ns, NS::DATA) {
            return Err(TempestError::InvalidNamespace {
                expected: NS::DATA,
                found: ns,
            });
        }
        let db = reader.read_string_null_terminated()?;
        let table = reader.read_string_null_terminated()?;
        let pk_bytes = reader.read_remaining();
        let pk_bytes = pk_bytes.into();

        Ok(TempestKey {
            db,
            table,
            pk_bytes,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::core::io::SliceReader;

    use super::*;

    #[test]
    fn test_tempest_key_encode_decode() {
        let pk_bytes = "pk_bytes".as_bytes();
        let tempest_keys = [
            TempestKey::new_owned(
                Cow::from("db1").try_into().unwrap(),
                Cow::from("table1").try_into().unwrap(),
                pk_bytes.into(),
            ),
            TempestKey::new_owned(
                Cow::from("main").try_into().unwrap(),
                Cow::from("users").try_into().unwrap(),
                pk_bytes.into(),
            ),
        ];

        let mut buf = Vec::new();
        for k in &tempest_keys {
            buf.clear();
            k.encode(&mut buf);
            let mut reader = SliceReader::new(&buf);
            let decoded = TempestKey::decode(&mut reader).unwrap();
            assert_eq!(&decoded, k);
            assert!(
                reader.is_eof(),
                "reader should have reached end of byte sequence"
            );
        }
    }
}
