use std::collections::{BTreeMap, HashMap};

use derive_more::{Display, Error, From};
use itertools::Itertools;
use strum::IntoDiscriminant;
use tempest_core::{fio::FioFS, tempest_str::TempestStr};
use tempest_tql::ast::{
    CreateDatabaseStmt, CreateTableStmt, CreateTyStmt, Expr, InsertIntoStmt, ProjectionKind,
    SelectFromStmt, Stmt,
};

use crate::{
    catalog::{
        Catalog, CatalogError,
        schema::{DatabaseSchema, FieldDef, FieldId, TableId, TableSchema, TypeSchema},
    },
    query::{
        eval::eval,
        resolve::{
            ResolveError, resolve_database, resolve_table, resolve_type, resolve_type_schema,
        },
    },
    types::{TempestType, TempestValue},
};

#[derive(Debug, Display, From, Error)]
pub enum PlanError {
    #[display("catalog error: {}", _0)]
    CatalogError(CatalogError),
    #[display("resolve error: {}", _0)]
    ResolveError(ResolveError),
    #[from(skip)]
    #[display("field with the name '{}' not found on type", _0)]
    FieldNotFound(#[error(not(source))] TempestStr<'static>),
    #[from(skip)]
    #[display("field supplied named '{}' not found on type", _0)]
    UnknownField(#[error(not(source))] TempestStr<'static>),
    #[from(skip)]
    #[display("missing field named '{}' for creating this type", _0)]
    MissingField(#[error(not(source))] TempestStr<'static>),
    #[display("type mismatch: expected value of type {}, but got value of type {}", expected.name(), got.name())]
    TypeMismatch {
        expected: TempestType,
        got: TempestType,
    },
}

pub(crate) enum PlanNode {
    CreateDatabase(DatabaseSchema),
    CreateType(TypeSchema),
    CreateTable(TableSchema),
    Insert {
        table_id: TableId,
        row: Vec<TempestValue<'static>>,
    },
    Select {
        table_id: TableId,
        columns: Vec<FieldId>,
    },
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

    pub(crate) fn plan_insert_into<'b>(
        &self,
        stmt: InsertIntoStmt<'b>,
    ) -> Result<PlanNode, PlanError> {
        let table = resolve_table(&stmt.table, self.catalog)?;

        let supplied: HashMap<&TempestStr<'b>, &Expr> = stmt
            .values
            .values
            .iter()
            .map(|v| (&v.column.name, &v.value))
            .collect();

        // check for unknown fields
        for &name in supplied.keys() {
            if !table.fields.values().any(|f| &f.name == name) {
                return Err(PlanError::UnknownField(name.clone().into_owned()));
            }
        }

        // build row in field order
        let mut row = Vec::new();
        for (_, def) in table.fields {
            // evaluate the expression for this field from the supplied value list
            let expr = supplied
                .get(&def.name)
                .ok_or_else(|| PlanError::MissingField(def.name.clone().into_owned()))?;
            let value = eval(expr);

            // type check
            if value.discriminant() != def.ty {
                return Err(PlanError::TypeMismatch {
                    expected: def.ty,
                    got: value.discriminant(),
                });
            }

            // push the final value
            row.push(value);
        }

        Ok(PlanNode::Insert {
            table_id: table.id,
            row,
        })
    }

    pub(crate) fn plan_select_from(&self, stmt: SelectFromStmt) -> Result<PlanNode, PlanError> {
        let table = resolve_table(&stmt.table, self.catalog)?;

        let columns = match stmt.projection.kind {
            ProjectionKind::All => table.fields.keys().copied().collect_vec(),
            ProjectionKind::Columns(idents) => idents
                .iter()
                .map(|ident| {
                    table
                        .fields
                        .iter()
                        .find(|(_, def)| def.name == ident.name)
                        .map(|(fid, _)| *fid)
                        .ok_or_else(|| PlanError::FieldNotFound(ident.name.clone().into_owned()))
                })
                .collect::<Result<Vec<FieldId>, PlanError>>()?,
        };

        Ok(PlanNode::Select {
            table_id: table.id,
            columns,
        })
    }

    // TODO: how to do planning with multiple statements in a row, like in transactions?
    pub(crate) fn plan(&self, stmt: Stmt<'_>) -> Result<PlanNode, PlanError> {
        match stmt {
            Stmt::CreateDatabase(stmt) => self.plan_create_database(stmt),
            Stmt::CreateTy(stmt) => self.plan_create_type(stmt),
            Stmt::CreateTable(stmt) => self.plan_create_table(stmt),
            Stmt::InsertInto(stmt) => self.plan_insert_into(stmt),
            Stmt::SelectFrom(stmt) => self.plan_select_from(stmt),
        }
    }
}
