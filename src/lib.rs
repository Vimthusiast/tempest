use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

#[macro_use]
extern crate derive_more;

use tokio::sync::{
    RwLock,
    mpsc::{self, UnboundedReceiver, UnboundedSender},
    oneshot,
};

use crate::{
    core::{TempestStr, schema::Catalog},
    kv::KvStore,
};

pub(crate) mod core;
pub(crate) mod kv;
pub mod prelude;
pub(crate) mod query;
pub(crate) mod scheduler;

/// Tempest implementation. Always uses the first byte of the key for the namespace.
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
    catalog: Arc<RwLock<Catalog>>,
}

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init<KV: KvStore + 'static>(kv: KV) -> Self {
        let kv = Arc::new(kv);
        let catalog = RwLock::new(Catalog::init(kv.clone())).into();
        Self { kv, catalog }
    }
}
