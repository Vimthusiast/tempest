use tempest_core::test_utils::setup_tracing;

use super::*;
use crate::catalog::schema::{DatabaseSchema, TableSchema, TypeId};

fn make_db(name: &'static str) -> DatabaseSchema {
    DatabaseSchema {
        name: name.into(),
        tables: Default::default(),
        types: Default::default(),
    }
}

fn make_table(database_id: DatabaseId, name: &'static str) -> TableSchema {
    TableSchema {
        database_id,
        name: name.into(),
        type_id: TypeId(0),
        primary_key: vec![],
    }
}

#[test]
fn create_database_assigns_incrementing_ids() {
    setup_tracing();

    let mut state = CatalogState::initial();
    let (id_a, edit_a) = state.create_database_edit(make_db("a")).unwrap();
    state.apply(edit_a);
    let (id_b, edit_b) = state.create_database_edit(make_db("b")).unwrap();
    state.apply(edit_b);

    assert_ne!(id_a, id_b);
    assert!(id_b.0 > id_a.0);

    debug!("final state: {:#?}", state);
}

#[test]
fn create_database_rejects_duplicate_name() {
    setup_tracing();

    let mut state = CatalogState::initial();
    let (_, edit) = state.create_database_edit(make_db("mydb")).unwrap();
    state.apply(edit);

    assert!(matches!(
        state.create_database_edit(make_db("mydb")),
        Err(CatalogError::DatabaseAlreadyExists(_))
    ));

    debug!("final state: {:#?}", state);
}

#[test]
fn create_table_rejects_unknown_database() {
    setup_tracing();

    let state = CatalogState::initial();
    assert!(matches!(
        state.create_table_edit(make_table(DatabaseId(99), "users")),
        Err(CatalogError::DatabaseNotFound(_))
    ));

    debug!("final state: {:#?}", state);
}

#[test]
fn create_table_rejects_duplicate_name_within_same_but_not_different_database() {
    setup_tracing();

    let mut state = CatalogState::initial();
    let (db_id, edit) = state.create_database_edit(make_db("mydb")).unwrap();
    state.apply(edit);

    let (_, edit) = state.create_table_edit(make_table(db_id, "users")).unwrap();
    state.apply(edit);

    assert!(matches!(
        state.create_table_edit(make_table(db_id, "users")),
        Err(CatalogError::TableAlreadyExists(_))
    ));

    let (other_id, edit) = state.create_database_edit(make_db("otherdb")).unwrap();
    state.apply(edit);

    let (_, edit) = state
        .create_table_edit(make_table(other_id, "users"))
        .unwrap();
    state.apply(edit);

    debug!("final state: {:#?}", state);
}

#[test]
fn snapshot_roundtrip_restores_state() {
    setup_tracing();

    let mut state = CatalogState::initial();
    let (db_id, edit) = state.create_database_edit(make_db("mydb")).unwrap();
    state.apply(edit);
    let (_, edit) = state.create_table_edit(make_table(db_id, "users")).unwrap();
    state.apply(edit);

    // take snapshot, replay into fresh state
    let snapshot = state.snapshot();
    let mut restored = CatalogState::initial();
    restored.apply(snapshot);

    assert!(restored.databases.contains_key(&db_id));
    assert_eq!(restored.tables.len(), 1);
    assert_eq!(restored.next_database_id, state.next_database_id);
    assert_eq!(restored.next_table_id, state.next_table_id);

    debug!("final state: {:#?}", state);
}
