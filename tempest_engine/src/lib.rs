use std::{path::PathBuf, sync::Arc};

use derive_more::{Display, Error, From};
use itertools::Itertools;
use tempest_core::fio::FioFS;
use tempest_tql::{ParserError, parse};
use tokio::sync::RwLock;

use crate::{
    catalog::{Catalog, CatalogError, schema::DatabaseSchema},
    config::EngineConfig,
    query::{
        QueryResult,
        plan::{PlanError, PlanNode, Planner},
    },
};

#[macro_use]
extern crate tracing;

mod base;
mod catalog;
mod config;
mod ctrl;
mod query;
mod row;
mod types;

#[derive(Debug, Display, Error, From)]
pub enum EngineError {
    #[display("catalog error: {}", _0)]
    CatalogError(CatalogError),

    #[display("plan error: {}", _0)]
    PlanError(PlanError),

    #[display("parse query errors: {}", _0.iter().join(", "))]
    Parse(#[error(not(source))] Vec<ParserError>),
}

pub struct Engine<F: FioFS> {
    root: PathBuf,
    fs: F,

    catalog: Arc<RwLock<Catalog<F>>>,

    config: EngineConfig,
}

impl<F: FioFS> Engine<F> {
    pub async fn open(fs: F, root: PathBuf, config: EngineConfig) -> Result<Self, EngineError> {
        let catalog = Catalog::open(fs.clone(), root.clone(), config.catalog.clone()).await?;
        Ok(Self {
            root,
            fs,
            // TODO: make catalog thread-safe through internal partial locking / channels
            catalog: Arc::new(RwLock::new(catalog)),
            config,
        })
    }

    async fn execute_plan(&self, plan: PlanNode) -> Result<QueryResult, EngineError> {
        match plan {
            PlanNode::CreateDatabase(schema) => {
                self.catalog.write().await.create_database(schema).await?;
                Ok(QueryResult::Empty)
            }
            PlanNode::CreateType(schema) => {
                self.catalog.write().await.create_type(schema).await?;
                Ok(QueryResult::Empty)
            }
            PlanNode::CreateTable(schema) => {
                self.catalog.write().await.create_table(schema).await?;
                Ok(QueryResult::Empty)
            }
        }
    }

    pub async fn execute(&self, query: &str) -> Result<Vec<QueryResult>, EngineError> {
        let (stmts, errors) = parse(query);
        if !errors.is_empty() {
            return Err(EngineError::Parse(errors));
        }

        // TODO: group transactions here or in ast?
        // => ast as `transaction { ... }` seems good
        let mut results = Vec::new();
        for stmt in stmts {
            let catalog = self.catalog.read().await;
            let plan = Planner::new(&catalog).plan(stmt)?;
            drop(catalog);

            results.push(self.execute_plan(plan).await?);
        }
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use tempest_core::fio::VirtualFileSystem;

    use super::*;

    #[tokio::test]
    async fn test_engine() {
        let fs = VirtualFileSystem::new();
        let root = PathBuf::from("/tempest");
        let config = EngineConfig::default();
        let engine = Engine::open(fs, root, config).await.unwrap();
        engine.execute("create database main;").await.unwrap();
        engine
            .execute("create type main.User { id: Int64, username: String };")
            .await
            .unwrap();
        engine
            .execute("create table main.users : main.User { primary key (id) };")
            .await
            .unwrap();
    }
}
