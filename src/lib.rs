use std::sync::Arc;

#[macro_use]
extern crate derive_more;

use crate::kv::KvStore;

pub(crate) mod core;
pub(crate) mod kv;
pub mod prelude;
pub(crate) mod query;

/// Tempest implementation. Always uses the first byte of the key for the namespace.
///
/// ## Basic Key Layout
///
/// **`[NS] + [DB_NAME] + [0] + [TABLE_NAME] + [0]` (+ [INDEX_BYTES]) + [PK_BYTES]:**
///
/// - `[NS]`: Namespace (`u8`)
/// - `[DB_NAME]`: Database Name ([`TempestStr`])
/// - `[TABLE_NAME]`: Table Name ([`TempestStr`])
/// - `[INDEX_BYTES]`: Bytes of the columns used for an index.
/// - `[PK_BYTES]`: Bytes of the primary key.
///
/// ## Namespaces
///
/// Tempest namespaces are defined by the [`NS`] enum:
///
/// - [`NS::CATALOG`]: catalog namespace
/// - [`NS::DATA`]: data namespace
///
/// ### Catalog Namespace
///
/// This contains the catalog data, which is handled by the [`Catalog`] instance.
///
/// ### Data Namespace
///
/// This contains the data of all databases.
///
/// [`TempestStr`]: crate::core::TempestStr
/// [`NS`]: crate::core::NS
/// [`NS::CATALOG`]: crate::core::NS::CATALOG
/// [`NS::DATA`]: crate::core::NS::DATA
/// [`Catalog`]: crate::Catalog
pub struct Tempest {
    kv: Arc<dyn KvStore>,
}

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init<KV: KvStore + 'static>(kv: KV) -> Self {
        let kv = Arc::new(kv);
        Self { kv }
    }
}
