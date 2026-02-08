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
    manifest::ManifestManager,
    scheduler::AccessManager,
};

pub(crate) mod core;
pub(crate) mod kv;
pub(crate) mod manifest;
pub mod prelude;
pub(crate) mod query;
pub(crate) mod scheduler;

/// # Tempest DB
///
/// Implementation of a relational database on top of a key-value store.
/// Always uses the first byte of the key for the [namespace](#namespaces).
///
/// ## Components and Dependencies
///
/// | Component | Responsibility |
/// |-----------|----------------|
/// |[`KvStore`]|A key-value store implemented as an LSM-Tree (in the future; in-mem [`BTreeMap`] currently)|
/// |[`ManifestManager`]|Manages the [`Manifest`], a persistent record of the current maximum [`SeqNum`] and file locations|
/// |[`SnapshotRegistry`]|Thread-safe counter and ref-counting of snapshots by [`SeqNum`]s|
/// |[`AccessManager`]|Manages access to different objects through highly flexible lock-states|
///
/// All of the components are internally owned by the [`Tempest`] instance.
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
/// [`SeqNum`]: crate::kv::SeqNum
/// [`BTreeMap`]: std::collections::BTreeMap
/// [`TempestStr`]: crate::core::TempestStr
/// [`NS`]: crate::core::NS
/// [`NS::CATALOG`]: crate::core::NS::CATALOG
/// [`NS::DATA`]: crate::core::NS::DATA
/// [`Catalog`]: crate::Catalog
/// [`ManifestManager`]: crate::manifest::ManifestManager
/// [`Manifest`]: crate::manifest::Manifest
pub struct Tempest {
    kv_store: Arc<dyn KvStore>,
    manifest_manager: Arc<dyn ManifestManager>,
    access_manager: AccessManager,
    catalog: Catalog,
}

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init<KV, MM>(kv: KV, manifest_manager: MM) -> Self
    where
        KV: KvStore + 'static,
        MM: ManifestManager + 'static,
    {
        let kv_store = Arc::new(kv);
        let manifest_manager = Arc::new(manifest_manager);
        let catalog = Catalog::init(kv_store.clone());
        let access_manager = AccessManager::init(64).await;
        Self {
            kv_store,
            manifest_manager,
            catalog,
            access_manager,
        }
    }
}
