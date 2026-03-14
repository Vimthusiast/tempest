use std::str::FromStr;

use derive_more::{Display, Error};
use tempest_core::tempest_str::TempestStr;
use tempest_tql::ast::Path;

use crate::{
    catalog::{
        CatalogState,
        schema::{DatabaseId, DatabaseSchema, TypeId, TypeSchema},
    },
    row::resolved::ResolvedTable,
    types::TempestType,
};

#[derive(Debug, Display, Error)]
pub enum ResolveError {
    #[display("database with the name '{}' was not found", _0)]
    DatabaseNotFound(#[error(not(source))] TempestStr<'static>),
    #[display("table with the name '{}' was not found inside of this scope", _0)]
    TableNotFound(#[error(not(source))] TempestStr<'static>),
    #[display("unqualified path: please specify scope")]
    UnqualifiedPath,
    #[display("type with the name '{}' was not found inside of this scope", _0)]
    UnknownType(#[error(not(source))] TempestStr<'static>),
    TypeNotFound(#[error(not(source))] TempestStr<'static>),
}

pub(crate) fn resolve_database<'a>(
    path: &Path,
    catalog: &'a CatalogState,
) -> Result<(DatabaseId, &'a DatabaseSchema), ResolveError> {
    let name = path
        .database
        .as_ref()
        .ok_or(ResolveError::UnqualifiedPath)?;
    catalog
        .get_database_by_name(&name.name)
        .ok_or_else(|| ResolveError::DatabaseNotFound(name.name.clone().into_owned()))
}

pub(crate) fn resolve_type_schema<'a>(
    path: &Path<'a>,
    catalog: &'a CatalogState,
) -> Result<(TypeId, &'a TypeSchema), ResolveError> {
    let (db_id, _) = resolve_database(path, catalog)?;
    catalog
        .get_type_by_name(db_id, &path.name.name)
        .ok_or_else(|| ResolveError::TypeNotFound(path.name.name.clone().into_owned()))
}

pub(crate) fn resolve_type(
    path: &Path,
    _catalog: &CatalogState,
) -> Result<TempestType, ResolveError> {
    // TODO: This will later have to resolve actual types as well, to allow embedding and
    // referencing, but it is not required for the mvp
    if path.database.is_none() {
        if let Ok(ty) = TempestType::from_str(&path.name.name) {
            return Ok(ty);
        }
    }
    Err(ResolveError::UnknownType(
        path.name.name.clone().into_owned(),
    ))
}

pub(crate) fn resolve_table<'a>(
    path: &Path,
    // when we implement session state / `use`, we may supply a database scope as context
    // scope: Option<DatabaseId>,
    catalog: &'a CatalogState,
) -> Result<ResolvedTable<'a>, ResolveError> {
    let (database_id, _) = resolve_database(path, catalog)?;

    let table_name = &path.name.name;
    let (table_id, table_schema) = catalog
        .get_table_by_name(database_id, table_name)
        .ok_or_else(|| ResolveError::TableNotFound(table_name.clone().into_owned()))?;

    let type_schema = catalog
        .types
        .get(&table_schema.type_id)
        .expect("type referenced by table not found in catalog - catalog is corrupt");

    Ok(ResolvedTable {
        id: table_id,
        fields: &type_schema.fields,
        primary_key: &table_schema.primary_key,
    })
}

#[cfg(test)]
mod tests {
    use crate::catalog::{schema::TableId, testing::create_catalog_state_for_testing};

    use super::*;

    #[test]
    fn resolve_basic() {
        let state = create_catalog_state_for_testing();
        let path = Path::for_testing(Some("main".into()), "users".into());
        let resolved = resolve_table(&path, &state).unwrap();
        assert_eq!(resolved.id, TableId(0));
        assert_eq!(resolved.fields.len(), 2);
    }

    #[test]
    fn resolve_database_not_found() {
        let state = create_catalog_state_for_testing();
        let path = Path::for_testing(Some("missing".into()), "users".into());
        assert!(matches!(
            resolve_table(&path, &state),
            Err(ResolveError::DatabaseNotFound(_))
        ));
    }

    #[test]
    fn resolve_table_not_found() {
        let state = create_catalog_state_for_testing();
        let path = Path::for_testing(Some("main".into()), "missing".into());
        assert!(matches!(
            resolve_table(&path, &state),
            Err(ResolveError::TableNotFound(_))
        ));
    }

    #[test]
    fn resolve_unqualified_path() {
        let state = create_catalog_state_for_testing();
        let path = Path::for_testing(None, "users".into());
        assert!(matches!(
            resolve_table(&path, &state),
            Err(ResolveError::UnqualifiedPath)
        ));
    }
}
