use tempest_core::tempest_str::TempestStr;

use crate::types::TempestValue;

pub(crate) mod eval;
pub(crate) mod exec;
pub(crate) mod plan;
pub(crate) mod resolve;

#[derive(Debug)]
pub enum QueryResult {
    /// `select` queries return multiple rows. Every row has exactly `columns.len()` entries.
    Rows {
        columns: Vec<TempestStr<'static>>,
        rows: Vec<Vec<TempestValue<'static>>>,
    },
    /// DDL queries, such as `create database`, do not return any values.
    Empty,
}
