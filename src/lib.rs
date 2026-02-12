use std::{collections::HashSet, ops::Range, sync::Arc};

#[macro_use]
extern crate derive_more;

use tokio::sync::RwLock;

use crate::{
    core::{
        TempestError, TempestStr, TempestValue,
        schema::{Catalog, RowEncoder, TableSchema, TempestRow},
    },
    kv::{KeyKind, KvStore, SeqNum},
    manifest::ManifestManager,
    scheduler::{AccessGuard, AccessManager, AccessMode, Resource, ResourceAccessSet},
};

pub mod core;
pub mod kv;
pub mod manifest;
pub mod prelude;
pub mod query;
pub mod scheduler;

/// The actual inner implementation of [`Tempest`], which itself is just a handle.
pub(crate) struct TempestEngine {
    kv_store: Arc<dyn KvStore>,
    manifest_manager: Arc<dyn ManifestManager>,
    access_manager: AccessManager,
    catalog: Arc<RwLock<Catalog>>,
}

#[derive(Debug)]
pub struct TableContext {
    /// A handle to the Tempest instance this context belongs to.
    instance: Tempest,
    /// The access guard that keeps the permit for this context.
    access_guard: AccessGuard,
    /// Shows, if this context has exclusive table access, so it can perform write actions.
    exclusive: bool,
    /// The name of the database this context belongs to.
    db: TempestStr<'static>,
    /// The name of the table this context belongs to.
    table: TempestStr<'static>,
    schema: TableSchema,
    current_range: Option<Range<SeqNum>>,
}

impl TableContext {
    pub(crate) async fn create(
        instance: Tempest,
        access_guard: AccessGuard,
        exclusive: bool,
        db: TempestStr<'static>,
        table: TempestStr<'static>,
    ) -> Self {
        let schema = instance
            .0
            .catalog
            .read()
            .await
            .get_table(&db, &table)
            .expect("there should be a schema that belongs to this table context")
            .clone();
        Self {
            instance,
            access_guard,
            exclusive,
            db,
            table,
            schema,
            current_range: None,
        }
    }

    pub async fn insert(&mut self, rows: &[TempestRow]) -> Result<(), TempestError> {
        for row in rows {
            let values = &row.values;
            println!(
                "Inserting {:?} into table '{}' in database '{}'.",
                values, self.table, self.db
            );
            if !self.exclusive {
                return Err(TempestError::MissingAccessMode);
            }
            let encoder = RowEncoder::new(&self.db, &self.schema);
            let (key, value) = encoder.encode(values);
            let range = if let Some(r) = &mut self.current_range
                && !r.is_empty()
            {
                r
            } else {
                let r = self
                    .instance
                    .0
                    .manifest_manager
                    .allocate_seqnum_range(64)
                    .await?;
                self.current_range = Some(r);
                self.current_range.as_mut().expect("just inserted")
            };
            let seq = range.start;
            let new_start = SeqNum::new(seq.get() + 1)
                .expect("as seqnum range goes higher than seq, seq+1 is valid seqnum");
            range.start = new_start;
            self.instance
                .0
                .kv_store
                .set(key, value, seq, KeyKind::Set)
                .await;
        }
        Ok(())
    }
    // TODO: CRUD
}

#[derive(Debug)]
pub struct DatabaseContext {
    /// A handle to the Tempest instance this context belongs to.
    instance: Tempest,
    /// The access guard that gurantees the referenced database cannot
    /// be deleted as long as this context still exists.
    access_guard: AccessGuard,
    /// The name of the database this context belongs to.
    db: TempestStr<'static>,
}

impl DatabaseContext {
    pub async fn get_table(
        &self,
        table: TempestStr<'static>,
        exclusive: bool,
    ) -> Result<TableContext, TempestError> {
        let mut resources = ResourceAccessSet::new();
        let mode = if exclusive {
            AccessMode::Exclusive
        } else {
            AccessMode::Shared
        };
        resources.insert((Resource::Table(self.db.clone(), table.clone()), mode));
        let access_guard = self.instance.0.access_manager.acquire(resources).await;
        if self
            .instance
            .0
            .catalog
            .read()
            .await
            .has_table(&self.db, &table)
        {
            Ok(TableContext::create(
                self.instance.clone(),
                access_guard,
                exclusive,
                self.db.clone(),
                table,
            )
            .await)
        } else {
            Err(TempestError::TableNotFound(self.db.clone(), table))
        }
    }

    pub async fn create_table(
        &self,
        table: TempestStr<'static>,
        exclusive: bool,
        schema: TableSchema,
    ) -> Result<TableContext, TempestError> {
        let mut resources = ResourceAccessSet::new();
        resources.insert((
            Resource::Table(self.db.clone(), table.clone()),
            AccessMode::Exclusive,
        ));
        let mut access_guard = self.instance.0.access_manager.acquire(resources).await;
        self.instance.0.catalog.write().await.create_table(
            self.db.clone(),
            table.clone(),
            schema,
        )?;
        if !exclusive {
            access_guard.downgrade(AccessMode::Shared);
        }

        Ok(TableContext::create(
            self.instance.clone(),
            access_guard,
            exclusive,
            self.db.clone(),
            table,
        )
        .await)
    }
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

    pub async fn get_db(&self, db: TempestStr<'static>) -> Result<DatabaseContext, TempestError> {
        // acquire IS perms to ensure database stays alive for the lifetime of this connection
        let mut access_guard_set = HashSet::new();
        access_guard_set.insert((Resource::Database(db.clone()), AccessMode::IntentShared));
        let access_guard = self.0.access_manager.acquire(access_guard_set).await;

        if self.0.catalog.read().await.has_db(&db) {
            Ok(DatabaseContext {
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
    ) -> Result<DatabaseContext, TempestError> {
        let mut access_guard_set = ResourceAccessSet::new();
        access_guard_set.insert((Resource::Database(db.clone()), AccessMode::Exclusive));
        let mut access_guard = self.0.access_manager.acquire(access_guard_set).await;
        self.0.catalog.write().await.create_db(db.clone())?;
        // NB: downgrade to IS after creating the db to allow for modifications elsewhere, but do
        // not drop the old guard and create a new one with IS perms, to prevent race conditions,
        // where there is a delete_db call inbetween.
        access_guard.downgrade(AccessMode::IntentShared);

        Ok(DatabaseContext {
            instance: self.clone(),
            access_guard,
            db,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{kv::InMemoryKvStore, manifest::InMemoryManifestManager};

    use super::*;

    #[tokio::test]
    async fn test_tempest() {
        let kv_store = InMemoryKvStore::new();
        let manifest_manager = InMemoryManifestManager::new();
        let tempest = Tempest::init(Arc::new(kv_store), Arc::new(manifest_manager)).await;
        let db1_ctx = tempest.create_db("db1".try_into().unwrap()).await.unwrap();
        let table1_schema = schema!(Table("table1") {
            id: Int8,
            flag: Bool,
        }, pk(id));
        let table1_ctx = db1_ctx
            .create_table("table1".try_into().unwrap(), false, table1_schema)
            .await
            .unwrap();
        drop(db1_ctx);
        drop(table1_ctx);
        let db1_ctx = tempest.get_db("db1".try_into().unwrap()).await.unwrap();
        let table1_ctx = db1_ctx
            .get_table("table1".try_into().unwrap(), true)
            .await
            .unwrap();

        _ = table1_ctx;
        // TODO: CRUD table operations, i.e. actually setting up the schema, inserting, reading...
    }
}
