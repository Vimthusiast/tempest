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
    core::{TempestError, TempestStr, schema::Catalog},
    kv::KvStore,
    manifest::ManifestManager,
    scheduler::{AccessGuard, AccessManager, AccessMode, Resource},
};

pub(crate) mod core;
pub(crate) mod kv;
pub(crate) mod manifest;
pub mod prelude;
pub(crate) mod query;
pub(crate) mod scheduler;

/// The actual inner implementation of [`Tempest`], which itself is just a handle.
pub(crate) struct TempestEngine {
    kv_store: Arc<dyn KvStore>,
    manifest_manager: Arc<dyn ManifestManager>,
    access_manager: AccessManager,
    catalog: Arc<RwLock<Catalog>>,
}

#[derive(Debug)]
pub struct DatabaseConnection {
    /// A handle to the Tempest instance this database connection goes to.
    instance: Tempest,
    /// The access guard that gurantees the connected database cannot
    /// be deleted as long as this connection still exists.
    access_guard: AccessGuard,
    /// The name of the database this connection belongs to.
    db: TempestStr<'static>,
}

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
#[derive(Debug, Clone)]
pub struct Tempest(#[debug("{:p}", Arc::as_ptr(_0))] Arc<TempestEngine>);

impl Tempest {
    /// Initialize this `Tempest` instance.
    pub async fn init(
        kv_store: Arc<dyn KvStore>,
        manifest_manager: Arc<dyn ManifestManager>,
    ) -> Self {
        let catalog = RwLock::new(Catalog::init(kv_store.clone())).into();
        let access_manager = AccessManager::init(64).await;
        let engine = TempestEngine {
            kv_store,
            manifest_manager,
            catalog,
            access_manager,
        };
        Self(Arc::new(engine))
    }

    pub async fn try_connect(
        &self,
        db: TempestStr<'static>,
    ) -> Result<DatabaseConnection, TempestError> {
        // acquire IS perms to ensure database stays alive for the lifetime of this connection
        let mut access_guard_set = HashSet::new();
        access_guard_set.insert((Resource::Database(db.clone()), AccessMode::IntentShared));
        let access_guard = self.0.access_manager.acquire(access_guard_set).await;

        if self.0.catalog.read().await.has_db(&db) {
            Ok(DatabaseConnection {
                instance: self.clone(),
                access_guard,
                db,
            })
        } else {
            Err(TempestError::DatabaseNotFound(db))
        }
    }

    pub async fn create_db(
        &self,
        db: TempestStr<'static>,
    ) -> Result<DatabaseConnection, TempestError> {
        let mut access_guard_set = HashSet::new();
        access_guard_set.insert((Resource::Database(db.clone()), AccessMode::Exclusive));
        let mut access_guard = self.0.access_manager.acquire(access_guard_set).await;
        self.0.catalog.write().await.create_db(db.clone())?;
        // NB: downgrade to IS after creating the db to allow for modifications elsewhere, but do
        // not drop the old guard and create a new one with IS perms, to prevent race conditions,
        // where there is a delete_db call inbetween.
        access_guard.downgrade(AccessMode::IntentShared);

        Ok(DatabaseConnection {
            instance: self.clone(),
            access_guard,
            db,
        })
    }
}
