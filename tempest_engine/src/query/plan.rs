use std::collections::BTreeMap;

use derive_more::{Display, Error, From};
use itertools::Itertools;
use tempest_core::{fio::FioFS, tempest_str::TempestStr};
use tempest_tql::ast::{CreateDatabaseStmt, CreateTableStmt, CreateTyStmt, Stmt};

use crate::{
    catalog::{
        Catalog, CatalogError,
        schema::{DatabaseId, DatabaseSchema, FieldDef, FieldId, TableSchema, TypeId, TypeSchema},
    },
    query::resolve::{ResolveError, resolve_database, resolve_type, resolve_type_schema},
};

#[derive(Debug, Display, From, Error)]
pub enum PlanError {
    #[display("catalog error: {}", _0)]
    CatalogError(CatalogError),
    #[display("resolve error: {}", _0)]
    ResolveError(ResolveError),
    #[display("field with the name '{}' not found on type", _0)]
    FieldNotFound(#[error(not(source))] TempestStr<'static>),
}

pub(crate) enum PlanNode {
    CreateDatabase(DatabaseSchema),
    CreateType(TypeSchema),
    CreateTable(TableSchema),
}

pub(crate) struct Planner<'a, F: FioFS> {
    catalog: &'a Catalog<F>,
}

impl<'a, F: FioFS> Planner<'a, F> {
    pub(crate) fn new(catalog: &'a Catalog<F>) -> Self {
        Self { catalog }
    }

    fn plan_create_database(&self, stmt: CreateDatabaseStmt) -> Result<PlanNode, PlanError> {
        let name = stmt.name.name.into_owned();
        Ok(PlanNode::CreateDatabase(DatabaseSchema::new(name)))
    }

    fn plan_create_type(&self, stmt: CreateTyStmt) -> Result<PlanNode, PlanError> {
        let (db_id, _) = resolve_database(&stmt.path, self.catalog)?;

        let fields = stmt
            .body
            .fields
            .into_iter()
            .enumerate()
            .map(|(i, field)| {
                let ty = resolve_type(&field.ty, self.catalog)?;
                Ok((
                    FieldId(i as u32),
                    FieldDef {
                        name: field.name.name.into_owned(),
                        ty,
                    },
                ))
            })
            .collect::<Result<BTreeMap<_, _>, PlanError>>()?;

        Ok(PlanNode::CreateType(TypeSchema {
            database_id: db_id,
            name: stmt.path.name.name.into_owned(),
            fields,
        }))
    }

    fn plan_create_table(&self, stmt: CreateTableStmt) -> Result<PlanNode, PlanError> {
        let (db_id, _) = resolve_database(&stmt.path, self.catalog)?;
        let (type_id, type_schema) = resolve_type_schema(&stmt.ty, self.catalog)?;

        let primary_key: Vec<_> = stmt
            .body
            .primary_key
            .columns
            .iter()
            .map(|ident| {
                type_schema
                    .fields
                    .iter()
                    .find(|(_, def)| def.name == ident.name)
                    .map(|(fid, _)| *fid)
                    .ok_or_else(|| PlanError::FieldNotFound(ident.name.clone().into_owned()))
            })
            .try_collect()?;

        Ok(PlanNode::CreateTable(TableSchema {
            database_id: db_id,
            name: stmt.path.name.name.into_owned(),
            type_id,
            primary_key,
        }))
    }

    // TODO: how to do planning with multiple statements in a row, like in transactions?
    pub(crate) fn plan(&self, stmt: Stmt<'_>) -> Result<PlanNode, PlanError> {
        match stmt {
            Stmt::CreateDatabase(stmt) => self.plan_create_database(stmt),
            Stmt::CreateTy(stmt) => self.plan_create_type(stmt),
            Stmt::CreateTable(stmt) => self.plan_create_table(stmt),
            _ => todo!("plan statement {:?}", stmt),
        }
    }
}
