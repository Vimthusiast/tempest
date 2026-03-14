use derive_more::{Display, Error, From};
use tempest_core::{fio::FioFS, tempest_str::TempestStr};
use tempest_tql::ast::{CreateDatabaseStmt, Stmt};

use crate::catalog::{Catalog, CatalogError};

#[derive(Debug, Display, From, Error)]
pub enum PlanError {
    #[display("catalog error: {}", _0)]
    CatalogError(CatalogError),
}

pub(crate) enum PlanNode {
    CreateDatabase { name: TempestStr<'static> },
}

pub(crate) struct Planner<'a, F: FioFS> {
    catalog: &'a Catalog<F>,
}

impl<'a, F: FioFS> Planner<'a, F> {
    pub(crate) fn new(catalog: &'a Catalog<F>) -> Self {
        Self { catalog }
    }

    fn plan_create_database(&self, stmt: CreateDatabaseStmt) -> Result<PlanNode, PlanError> {
        let name = TempestStr::from_owned(stmt.name.name.into_owned())
            .expect("identifier tokens are guranteed null-free by the lexer");
        Ok(PlanNode::CreateDatabase { name })
    }

    // TODO: how to do planning with multiple statements in a row, like in transactions?
    pub(crate) fn plan(&self, stmt: Stmt<'_>) -> Result<PlanNode, PlanError> {
        match stmt {
            Stmt::CreateDatabase(cd) => self.plan_create_database(cd),
            _ => todo!("plan statement {:?}", stmt),
        }
    }
}
