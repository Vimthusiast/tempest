use std::path::PathBuf;

use bytes::BytesMut;
use derive_more::{Display, Error, From};
use itertools::Itertools;
use tempest_core::fio::FioFS;
use tempest_kv::{
    base::StorageError,
    batch::WriteBatch,
    worker::{StorageHandle, StorageWorker},
};
use tempest_tql::{ParseError, parse};

use crate::{
    base::{EngineComparer, KeySpace},
    catalog::{Catalog, CatalogError},
    config::EngineConfig,
    ctrl::hlc::HlcGenerator,
    query::{
        QueryResult,
        plan::{PlanError, PlanNode, Planner},
    },
    row::{
        decoder::{RowDecodeError, RowDecoder},
        encoder::RowEncoder,
        resolved::ResolvedTable,
    },
    types::TempestValue,
};

#[macro_use]
extern crate tracing;

mod base;
mod catalog;
pub mod config;
mod ctrl;
mod query;
mod row;
mod types;

pub(crate) fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}

#[derive(Debug, Display, Error, From)]
pub enum EngineError {
    #[display("catalog error: {}", _0)]
    CatalogError(CatalogError),

    #[display("plan error: {}", _0)]
    PlanError(PlanError),

    #[display("parse query errors: {}", _0.iter().join(", "))]
    ParseError(#[error(not(source))] Vec<ParseError>),

    #[display("storage error: {}", _0)]
    StorageError(StorageError),

    #[display("row decode error: {}", _0)]
    RowDecodeError(RowDecodeError),
}

pub struct Engine<F: FioFS> {
    root: PathBuf,
    fs: F,

    hlc: HlcGenerator,
    catalog: Catalog<F>,
    storage: StorageHandle,

    config: EngineConfig,

    is_shutdown: bool,
}

impl<F: FioFS> Engine<F> {
    pub async fn open(fs: F, root: PathBuf, config: EngineConfig) -> Result<Self, EngineError> {
        let hlc = HlcGenerator::new();
        let catalog = Catalog::open(fs.clone(), root.clone(), config.catalog.clone()).await?;
        let storage = StorageWorker::<F, EngineComparer>::spawn_worker(
            0,
            fs.clone(),
            root.clone(),
            config.storage.clone(),
        );
        Ok(Self {
            root,
            fs,

            hlc,
            catalog,
            storage,

            config,

            is_shutdown: false,
        })
    }

    async fn execute_plan(&mut self, plan: PlanNode) -> Result<QueryResult, EngineError> {
        match plan {
            PlanNode::CreateDatabase(schema) => {
                self.catalog.create_database(schema).await?;
                Ok(QueryResult::Empty)
            }
            PlanNode::CreateType(schema) => {
                self.catalog.create_type(schema).await?;
                Ok(QueryResult::Empty)
            }
            PlanNode::CreateTable(schema) => {
                self.catalog.create_table(schema).await?;
                Ok(QueryResult::Empty)
            }
            PlanNode::Insert { table_id, row } => {
                let table_schema = self
                    .catalog
                    .tables
                    .get(&table_id)
                    .expect("table in plan not found in catalog");
                let type_schema = self
                    .catalog
                    .types
                    .get(&table_schema.type_id)
                    .expect("type in plan not found in catalog");

                let resolved = ResolvedTable {
                    id: table_id,
                    fields: &type_schema.fields,
                    primary_key: &table_schema.primary_key,
                };

                let hlc = self.hlc.generate(now_ms());
                let encoder = RowEncoder::new(&resolved);
                let mut key_buf = BytesMut::new();
                let mut value_buf = BytesMut::new();
                encoder.encode_row(&row, hlc, &mut key_buf, &mut value_buf);

                // dispatch write command
                let mut batch = WriteBatch::new();
                batch.put(&key_buf, &value_buf);
                self.storage.write(batch).await?;

                // TODO: number of lines modified
                Ok(QueryResult::Empty)
            }
            PlanNode::Select { table_id, columns } => {
                let table_schema = self
                    .catalog
                    .tables
                    .get(&table_id)
                    .expect("table in plan not found in catalog");
                let type_schema = self
                    .catalog
                    .types
                    .get(&table_schema.type_id)
                    .expect("type in plan not found in catalog");

                let resolved = ResolvedTable {
                    id: table_id,
                    fields: &type_schema.fields,
                    primary_key: &table_schema.primary_key,
                };
                let decoder = RowDecoder::new(&resolved);

                let col_indices: Vec<_> = columns
                    .iter()
                    .map(|fid| {
                        resolved
                            .fields
                            .keys()
                            .position(|k| k == fid)
                            .expect("field id of resolved column should exist")
                    })
                    .collect();

                let col_names: Vec<_> = columns
                    .iter()
                    .map(|fid| resolved.fields[fid].name.clone())
                    .collect();

                let mut rx = self.storage.scan().await?;
                let mut rows = Vec::new();
                while let Some(result) = rx.recv().await {
                    let (mut key, mut value) = result?;
                    // filter to only this table's rows
                    // TODO: implement filtering and seeking on internal iterators
                    if key.len() < 5 || key[0] != KeySpace::TableRow as u8 {
                        continue;
                    }
                    let row_table_id = u32::from_be_bytes(key[1..5].try_into().unwrap());
                    if row_table_id != *table_id {
                        continue;
                    }
                    let decoded = decoder.decode_row(&mut key, &mut value)?;
                    // TODO: get around this clone by removing sparsely from the decoded values
                    let projected = col_indices.iter().map(|&i| decoded[i].clone()).collect();
                    rows.push(projected);
                }

                Ok(QueryResult::Rows {
                    columns: col_names,
                    rows,
                })
            }
        }
    }

    pub async fn execute(&mut self, query: &str) -> Result<Vec<QueryResult>, EngineError> {
        let (stmts, errors) = parse(query);
        if !errors.is_empty() {
            return Err(EngineError::ParseError(errors));
        }

        // TODO: group transactions here or in ast?
        // => ast as `transaction { ... }` seems good
        let mut results = Vec::new();
        for stmt in stmts {
            let plan = Planner::new(&self.catalog).plan(stmt)?;
            results.push(self.execute_plan(plan).await?);
        }
        Ok(results)
    }

    pub async fn shutdown(&mut self) -> Result<(), EngineError> {
        assert!(!self.is_shutdown);
        // NB: Set this to true, even if this function may return an error,
        // since we may shut down partially, which means we don't want to call shutdown again,
        // even though it did not complete the process
        // TODO: => do we *really* want this?
        self.is_shutdown = true;
        self.storage.shutdown().await?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use tempest_core::fio::VirtualFileSystem;

    use crate::types::TempestValue;

    use super::*;

    #[tokio::test]
    async fn test_engine() {
        let fs = VirtualFileSystem::new();
        let root = PathBuf::from("/tempest");
        let config = EngineConfig::default();
        let mut engine = Engine::open(fs, root, config).await.unwrap();

        engine.execute("create database main;").await.unwrap();
        engine
            .execute("create type main.User { id: Int64, username: String };")
            .await
            .unwrap();
        engine
            .execute("create table main.users : main.User { primary key (id) };")
            .await
            .unwrap();
        engine
            .execute("insert into main.users { id: 1, username: \"John\" };")
            .await
            .unwrap();
        let full_results = engine.execute("select * from main.users;").await.unwrap();
        let QueryResult::Rows { columns, rows } = &full_results[0] else {
            panic!("expected rows, got {:?}", &full_results[0])
        };
        assert_eq!(columns[0], "id".into());
        assert_eq!(columns[1], "username".into());

        assert_eq!(rows[0][0], TempestValue::Int64(1));
        assert_eq!(rows[0][1], TempestValue::String("John".into()));

        let projected_results = engine
            .execute("select username from main.users;")
            .await
            .unwrap();
        let QueryResult::Rows { columns, rows } = &projected_results[0] else {
            panic!("expected rows, got {:?}", &full_results[0])
        };
        assert_eq!(columns[0], "username".into());

        assert_eq!(rows[0][0], TempestValue::String("John".into()));

        engine.shutdown().await.unwrap();
    }
}
