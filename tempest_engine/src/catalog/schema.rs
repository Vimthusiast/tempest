use std::collections::HashSet;

use derive_more::{Deref, Display};
use serde::{Deserialize, Serialize};
use tempest_core::tempest_str::TempestStr;

use crate::types::TempestType;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ColumnDef {
    /// Name of this column.
    pub name: TempestStr<'static>,
    /// Type of this column.
    pub ty: TempestType,
}

#[derive(
    Debug,
    Default,
    Display,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Deref,
    Serialize,
    Deserialize,
)]
pub struct TableId(pub u32);

#[derive(
    Debug,
    Default,
    Display,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Deref,
    Serialize,
    Deserialize,
)]
pub struct DatabaseId(pub u32);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TableSchema {
    /// The unique ID of the database this table belongs to.
    pub database_id: DatabaseId,
    /// Name of this table.
    pub name: TempestStr<'static>,
    /// The columns this table has.
    pub columns: Vec<ColumnDef>,
    /// Indices of the columns that make up the primary key, most significant first.
    /// For example, `[2, 0]` orders rows first by `columns[2]`, then by `columns[0]`.
    pub primary_key: Vec<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct DatabaseSchema {
    /// Name of this dtabase.
    pub name: TempestStr<'static>,
    /// The tables this database contains.
    pub tables: HashSet<TableId>,
}

impl DatabaseSchema {
    pub(crate) fn new(name: TempestStr<'static>) -> Self {
        Self {
            name,
            tables: HashSet::new(),
        }
    }
}
