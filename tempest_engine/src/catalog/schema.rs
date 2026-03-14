use std::collections::{BTreeMap, HashSet};

use derive_more::{Deref, Display};
use serde::{Deserialize, Serialize};
use tempest_core::tempest_str::TempestStr;

use crate::types::TempestType;

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
pub struct FieldId(pub u32);

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
pub struct TypeId(pub u32);

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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct FieldDef {
    /// Name of this column.
    pub name: TempestStr<'static>,
    /// Type of this column.
    pub ty: TempestType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TypeSchema {
    /// The ID of the database this type is scoped to.
    pub database_id: DatabaseId,
    /// The scope-unique name of this type.
    pub name: TempestStr<'static>,
    /// The fields of this type.
    pub fields: BTreeMap<FieldId, FieldDef>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TableSchema {
    /// The unique ID of the database this table belongs to.
    pub database_id: DatabaseId,
    /// Name of this table.
    pub name: TempestStr<'static>,
    /// The ID of the [`TypeSchema`] that this table has.
    pub type_id: TypeId,
    /// Field IDs of the columns that make up the primary key, most significant first.
    /// For example, `[2, 0]` orders rows first by `fields[2]`, then by `fields[0]`.
    pub primary_key: Vec<FieldId>,
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
pub struct DatabaseId(pub u32);

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
