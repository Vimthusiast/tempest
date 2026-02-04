use std::sync::Arc;

#[macro_use]
extern crate derive_more;

use crate::kv::KvStore;

pub mod core;
pub mod kv;
pub mod prelude;

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
}

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init<KV: KvStore + 'static>(kv: KV) -> Self {
        let kv = Arc::new(kv);
        Self { kv }
    }
}
