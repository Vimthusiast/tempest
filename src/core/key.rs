use std::{borrow::Cow, ops::Bound};

use crate::core::{
    NS,
    errors::TempestError,
    io::{TempestReader, TempestWriter},
    primitives::TempestStr,
};

pub(crate) fn successor(mut prefix: Vec<u8>) -> Option<Vec<u8>> {
    while let Some(last_byte) = prefix.pop() {
        if last_byte < 0xFF {
            // Found a byte we can increment
            prefix.push(last_byte + 1);
            return Some(prefix);
        }
        // If it was 0xFF, it stays popped (the carry)
    }
    // If the loop finishes, the prefix was all 0xFFs or empty
    None
}

pub(crate) fn prefix_range(prefix: Vec<u8>) -> (Bound<Vec<u8>>, Bound<Vec<u8>>) {
    let start = Bound::Included(prefix.clone());
    let end = match successor(prefix) {
        Some(succ) => Bound::Excluded(succ),
        None => Bound::Unbounded,
    };
    (start, end)
}

/// # Tempest Key
///
/// A key for a key-value pair i.e. a row within Tempest.
///
/// ## Layout
///
/// `[NS::DATA] + [DB] + [TABLE] + [INDEX_BYTES] + [PK_BYTES]`:
///
/// - [`NS::DATA`]: Every key-value pair of Tempest databases starts with this prefix.
/// - [`DB_NAME`]: A string that refers to the database this row belongs to.
/// - [`TABLE_NAME`]: A string that refers to the table this row belongs to.
/// - [`INDEX_BYTES`]: May have some bytes that allows for creating indices over the dataset for
///   efficient retrieval, by having rows be sorted and `O(log(n))` accessible based on that index,
///   through use of algorithms like binary-search (ignoring disc read performance impact here).
/// - [`PK_BYTES`]: Primary key encoded bytes that can be decoded into the primary key values.
///   This will result in the rows being ordered by the primary keys, automatically allowing for
///   efficient retrieval, just like with the `[INDEX_BYTES]`.
///
/// [`Tempest`]: crate::Tempest
/// [`DB_NAME`]: Self::db
/// [`TABLE_NAME`]: Self::table
/// [`INDEX_BYTES`]: Self::index_bytes
/// [`PK_BYTES`]: Self::pk_bytes
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct TempestKey<'a> {
    /// Null-terminated string that identifies the database.
    /// Must not contain any `\0` byte.
    db: TempestStr<'a>,
    /// Null-terminated string that identifies the table.
    /// Must not contain any `\0` byte.
    table: TempestStr<'a>,
    // TODO: Additional index bytes for faster reads at the cost of more storage space.
    // index_bytes: Cow<'a, [u8]>
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
        writer.write_u8(NS::DATA.into());
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
        writer.write_u8(NS::DATA.into());
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

    #[test]
    fn test_successor_prefix() {
        // Standard case: increment last byte
        assert_eq!(successor(vec![1, 2, 3]), Some(vec![1, 2, 4]));

        // Incrementing 0x00 (shouldn't be different from the standard case)
        assert_eq!(successor(vec![1, 0]), Some(vec![1, 1]));

        // Ripple case: last byte is 0xFF, carry to the left
        assert_eq!(successor(vec![1, 2, 255]), Some(vec![1, 3]));

        // Multiple ripple case: multiple 0xFFs
        assert_eq!(successor(vec![1, 255, 255]), Some(vec![2]));

        // Ceiling case: all bytes are 0xFF
        assert_eq!(successor(vec![255, 255]), None);

        // Empty case
        assert_eq!(successor(vec![]), None);
    }

    #[test]
    fn test_prefix_range() {
        // Normal table prefix
        let prefix = vec![1, 100, 0];
        let (start, end) = prefix_range(prefix.clone());

        assert_eq!(start, Bound::Included(vec![1, 100, 0]));
        assert_eq!(end, Bound::Excluded(vec![1, 100, 1]));

        // Prefix ending in 0xFF (ripple)
        let prefix_ff = vec![1, 255];
        let (start_ff, end_ff) = prefix_range(prefix_ff.clone());

        assert_eq!(start_ff, Bound::Included(vec![1, 255]));
        assert_eq!(end_ff, Bound::Excluded(vec![2]));

        // Unbounded ceiling
        let prefix_max = vec![255, 255];
        let (_, end_max) = prefix_range(prefix_max);

        assert_eq!(end_max, Bound::Unbounded);
    }
}
