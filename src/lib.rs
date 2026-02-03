use std::{collections::BTreeMap, sync::Arc};

use futures::StreamExt;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::{
    core::{CATALOG_NS, DataType},
    kv::KvStore,
};

#[macro_use]
extern crate derive_more;

pub mod core;
pub mod kv;
pub mod query;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Column {
    pub(crate) name: String,
    pub(crate) data_type: DataType,
    //pub(crate) nullable: bool,
    //pub(crate) default: Option<Expr>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TableSchema {
    /// Every column's name and it's type.
    pub(crate) columns: Vec<Column>,
    /// The columns (their indices) used to uniquely identify rows of this table.
    pub(crate) primary_key: Vec<usize>,
}

impl TableSchema {
    pub fn new(columns: Vec<Column>, primary_key: Vec<usize>) -> Self {
        Self {
            columns,
            primary_key,
        }
    }
}

/// Catalog implementation. The catalog keeps track of the database metadata,
/// such as the [`TableSchema`]s.
///
/// [`TableSchema`]: TableSchema
pub struct Catalog {
    kv: Arc<dyn KvStore>,
    /// Maps `DB_NAME` and `TABLE_NAME` to the schema for that table.
    cache: RwLock<BTreeMap<(String, String), TableSchema>>,
}

impl Catalog {
    pub async fn bootstrap(kv: Arc<dyn KvStore>) -> Self {
        let mut stream = kv.scan(
            CATALOG_NS.to_be_bytes().to_vec(),
            (CATALOG_NS + 1).to_be_bytes().to_vec(),
        );
        let cache = BTreeMap::new();

        while let Some((_key, _value)) = stream.next().await {
            todo!("implement reading of old schema");
        }
        drop(stream);

        let cache = RwLock::new(cache);

        Self { kv, cache }
    }

    pub async fn set_schema(&self, database: String, table: String, schema: TableSchema) {
        let mut cache_guard = self.cache.write().await;
        match cache_guard.entry((database, table)) {
            std::collections::btree_map::Entry::Vacant(e) => {
                e.insert(schema);
            }
            std::collections::btree_map::Entry::Occupied(_e) => {
                todo!("implement schema modification")
            }
        }
    }

    pub async fn get_schema(&self, database: String, table: String) -> Option<TableSchema> {
        return self.cache.read().await.get(&(database, table)).cloned();
    }
}

/// Tempest implementation. Always uses the first byte of the key for the namespace.
///
/// ## Datatypes
///
/// ### Boolean
///
/// Stored as a single byte of `0` or `1`.
///
/// ### Integer
///
/// Encoded in a way that retains lexicographical ordering for negative values.
///
/// ### String
///
/// Strings must only contain valid UTF-8. For other data, see Blob (todo).
///
// TODO:
// - Blob
///
/// ## Basic Key Layout
///
/// `[NS] + [DB_NAME] + [0] + [TABLE_NAME] + [0]`
///
/// - `[NS]`: Namespace (Single Byte)
/// - `[DB_NAME]`: Database Name (String; null-terminated)
/// - `[TABLE_NAME]`: Table Name (String; null-terminated)
///
/// ## Namespaces
///
/// - [`CATALOG_NS`]: catalog namespace
/// - [`DATA_NS`]: data namespace
///
/// ### Catalog Namespace
///
/// This contains the catalog data, which is handled by the [`Catalog`] instance.
///
/// ### Data Namespace
///
/// This contains the data of all databases.
///
/// [`CATALOG_NS`]: crate::core::CATALOG_NS
/// [`DATA_NS`]: crate::core::DATA_NS
/// [`Catalog`]: crate::Catalog
pub struct Tempest {
    kv: Arc<dyn KvStore>,
    catalog: Catalog,
}

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init<KV: KvStore + 'static>(kv: KV) -> Self {
        let kv = Arc::new(kv);
        let catalog = Catalog::bootstrap(kv.clone()).await;
        Self { kv, catalog }
    }
}
