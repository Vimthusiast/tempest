use std::borrow::Cow;

use super::{decoder::*, encoder::*};

use crate::{
    base::{EngineComparer, KeySpace},
    catalog::schema::{ColumnDef, DatabaseId, TableId, TableSchema},
    ctrl::hlc::HlcTimestamp,
    types::{TempestType, TempestValue},
};

use bytes::BytesMut;
use tempest_kv::base::Comparer;

fn make_schema() -> (TableId, TableSchema) {
    let table_id = TableId(1);
    let schema = TableSchema {
        database_id: DatabaseId(0),
        name: "users".into(),
        columns: vec![
            ColumnDef {
                name: "id".into(),
                ty: TempestType::Int64,
            },
            ColumnDef {
                name: "name".into(),
                ty: TempestType::String,
            },
        ],
        primary_key: vec![0], // `id` is the PK
    };
    (table_id, schema)
}

fn encode(row: &[TempestValue<'_>], hlc: HlcTimestamp) -> (BytesMut, BytesMut) {
    let (table_id, schema) = make_schema();
    let encoder = RowEncoder::new(table_id, &schema);
    let mut key_buf = BytesMut::new();
    let mut val_buf = BytesMut::new();
    encoder.encode_row(row, hlc, &mut key_buf, &mut val_buf);
    (key_buf, val_buf)
}

#[test]
fn test_encode_decode_row() {
    let rows = [
        (1, "john"),
        (6, "vimthusiast"),
        (7, "jam06452"),
        (24, "bob"),
        (42, "contai\0ns\0nu\0ll"),
    ]
    .map(|(id, name)| {
        (
            TempestValue::Int64(id),
            TempestValue::String(Cow::Borrowed(name)),
        )
    });

    let (table_id, schema) = make_schema();
    let encoder = RowEncoder::new(table_id, &schema);
    let decoder = RowDecoder::new(&schema);

    for (hlc, (id, name)) in rows
        .into_iter()
        .enumerate()
        .map(|(i, cols)| (HlcTimestamp::from_u64((i * 10) as u64), cols))
    {
        let mut key_buf = BytesMut::with_capacity(128);
        let mut value_buf = BytesMut::with_capacity(128);

        let input_row = &[id.clone(), name.clone()];

        encoder.encode_row(input_row, hlc, &mut key_buf, &mut value_buf);
        let result = decoder
            .decode_row(&mut key_buf.freeze(), &mut value_buf.freeze())
            .unwrap();

        assert_eq!(result[0], input_row[0]);
        assert_eq!(result[1], input_row[1]);
        assert_eq!(result.len(), input_row.len());
    }
}

#[test]
fn encode_row_key_starts_with_keyspace_prefix() {
    let row = &[TempestValue::Int64(1), TempestValue::String("alice".into())];
    let (key, _) = encode(row, HlcTimestamp::new(0, 0));
    assert_eq!(key[0], KeySpace::TableRow as u8);
}

#[test]
fn encode_row_key_ends_with_hlc() {
    let hlc = HlcTimestamp::new(12345, 7);
    let row = &[TempestValue::Int64(1), TempestValue::String("alice".into())];
    let (key, _) = encode(row, hlc);
    let suffix = &key[key.len() - 8..];
    let decoded = u64::from_be_bytes(suffix.try_into().unwrap());
    assert_eq!(decoded, *hlc);
}

#[test]
fn encode_row_value_contains_non_pk_columns_only() {
    let row = &[TempestValue::Int64(42), TempestValue::String("bob".into())];
    let (_, val) = encode(row, HlcTimestamp::new(0, 0));
    // value must be non-empty since there is one non-PK column
    assert!(!val.is_empty());
}

#[test]
#[should_panic]
fn typecheck_rejects_wrong_type() {
    let row = &[TempestValue::Bool(true), TempestValue::String("x".into())];
    encode(row, HlcTimestamp::new(0, 0));
}

#[test]
fn different_pk_values_produce_different_keys() {
    let row_a = &[TempestValue::Int64(1), TempestValue::String("alice".into())];
    let row_b = &[TempestValue::Int64(2), TempestValue::String("alice".into())];
    let hlc = HlcTimestamp::new(0, 0);
    let (key_a, _) = encode(row_a, hlc);
    let (key_b, _) = encode(row_b, hlc);
    assert_ne!(key_a, key_b);
}

#[test]
fn newer_hlc_sorts_before_older_for_same_pk() {
    let row = &[TempestValue::Int64(1), TempestValue::String("alice".into())];
    let (key_old, _) = encode(row, HlcTimestamp::new(1, 0));
    let (key_new, _) = encode(row, HlcTimestamp::new(2, 0));
    // newer HLC should sort first (descending suffix order)
    assert!(EngineComparer::compare_physical(&key_new, &key_old).is_lt());
}
