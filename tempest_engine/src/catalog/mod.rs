use std::{collections::HashMap, ops::Deref, path::PathBuf};

use derive_more::{Display, Error, From};
use serde::{Deserialize, Serialize};
use tempest_core::{
    fio::FioFS,
    journal::{Journal, JournalError, Replayable},
    tempest_str::TempestStr,
};

use crate::{
    catalog::schema::{DatabaseId, DatabaseSchema, TableId, TableSchema},
    config::CatalogConfig,
};

pub(crate) mod schema;

#[cfg(test)]
mod tests;

/// The set of mutations that can be applied to the catalog in format version 1.
///
/// Each variant represents a single atomic, semantic change to the catalog state.
/// Implementation details like ID allocation are never recorded as edits.
/// IDs are derived from the edits themselves during replay.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum CatalogEditV1 {
    /// Registers a new database with its assigned [`DatabaseId`].
    CreateDatabase((DatabaseId, DatabaseSchema)),
    /// Registers a new table with its assigned [`TableId`].
    CreateTable((TableId, TableSchema)),
    /// A point-in-time snapshot of the full catalog state, written on journal
    /// rotation. Contains only live entries - dropped tables and databases are
    /// omitted, collapsing any create/drop history into the current state.
    Snapshot(Vec<CatalogEdit>),
}

/// A versioned, append-only log of every mutation to the [`Catalog`].
///
/// Wrapping edits in a version enum allows the on-disk format to evolve
/// without breaking existing journals - old `V1` edits remain valid even
/// as new variants are added.
#[repr(u16)]
#[derive(derive_more::Debug, Serialize, Deserialize)]
pub(crate) enum CatalogEdit {
    #[debug("{:?}", _0)]
    V1(CatalogEditV1) = 1,
}

#[derive(Debug, Display, Error, From)]
pub enum CatalogError {
    #[display("journal error: {}", _0)]
    JournalError(JournalError),

    #[from(skip)]
    #[display("database with ID {} was not found", _0)]
    DatabaseNotFound(#[error(not(source))] DatabaseId),
    #[from(skip)]
    #[display("database with name '{}' already exists", _0)]
    DatabaseAlreadyExists(#[error(not(source))] TempestStr<'static>),

    #[from(skip)]
    #[display("table with ID {} was not found", _0)]
    TableNotFound(#[error(not(source))] TableId),
    #[from(skip)]
    #[display("table with name '{}' already exists", _0)]
    TableAlreadyExists(#[error(not(source))] TempestStr<'static>),
}

#[derive(Debug, Default)]
pub(crate) struct CatalogState {
    /// Contains the definitions of all tables, accessible through their unique, stable ID.
    pub(crate) tables: HashMap<TableId, TableSchema>,
    /// Contains the definitions of all databases, accessible through their unique, stable ID.
    pub(crate) databases: HashMap<DatabaseId, DatabaseSchema>,
    /// Monotonically increasing generator for the table IDs.
    /// Incremented automatically inside of [`Self::apply()].
    next_table_id: TableId,
    /// Monotonically increasing generator for the database IDs.
    /// Incremented automatically inside of [`Self::apply()].
    next_database_id: DatabaseId,
}

impl CatalogState {
    fn create_database_edit(
        &self,
        schema: DatabaseSchema,
    ) -> Result<(DatabaseId, CatalogEdit), CatalogError> {
        if self.databases.values().any(|db| db.name == schema.name) {
            return Err(CatalogError::DatabaseAlreadyExists(schema.name));
        }

        let id = self.next_database_id;
        trace!(?id, "assigned id to create database edit");

        Ok((
            id,
            CatalogEdit::V1(CatalogEditV1::CreateDatabase((id, schema))),
        ))
    }

    fn create_table_edit(
        &self,
        schema: TableSchema,
    ) -> Result<(TableId, CatalogEdit), CatalogError> {
        let db = self
            .databases
            .get(&schema.database_id)
            .ok_or(CatalogError::DatabaseNotFound(schema.database_id))?;

        let id = self.next_table_id;
        trace!(?id, "assigned id to create table edit");

        if db
            .tables
            .iter()
            .any(|id| self.tables[id].name == schema.name)
        {
            return Err(CatalogError::TableAlreadyExists(schema.name));
        }

        Ok((
            id,
            CatalogEdit::V1(CatalogEditV1::CreateTable((id, schema))),
        ))
    }
}

impl Replayable for CatalogState {
    type Edit = CatalogEdit;

    #[instrument(skip_all, level = "debug")]
    fn apply(&mut self, edit: Self::Edit) {
        match edit {
            CatalogEdit::V1(v1) => match v1 {
                CatalogEditV1::CreateDatabase((id, schema)) => {
                    debug!(?id, ?schema, "applying create database edit");
                    assert!(!self.databases.contains_key(&id));
                    self.next_database_id = DatabaseId(*id + 1).max(self.next_database_id);
                    self.databases.insert(id, schema);
                }
                CatalogEditV1::CreateTable((id, schema)) => {
                    debug!(?id, ?schema, "applying create table edit");
                    assert!(!self.tables.contains_key(&id));
                    self.next_table_id = TableId(*id + 1).max(self.next_table_id);
                    // add the id to the database's table set
                    self.databases
                        .get_mut(&schema.database_id)
                        .expect("database must exist when applying CreateTable")
                        .tables
                        .insert(id);
                    self.tables.insert(id, schema);
                }
                CatalogEditV1::Snapshot(edits) => {
                    debug!(count = edits.len(), "applying snapshot edits");
                    for e in edits {
                        self.apply(e);
                    }
                }
            },
        }
    }

    fn snapshot(&self) -> Self::Edit {
        let mut edits = Vec::new();

        edits.extend(self.databases.iter().map(|(id, schema)| {
            CatalogEdit::V1(CatalogEditV1::CreateDatabase((id.clone(), schema.clone())))
        }));

        edits.extend(self.tables.iter().map(|(id, schema)| {
            CatalogEdit::V1(CatalogEditV1::CreateTable((id.clone(), schema.clone())))
        }));

        CatalogEdit::V1(CatalogEditV1::Snapshot(edits))
    }

    fn filename_prefix() -> &'static str {
        "catalog"
    }

    fn initial() -> Self {
        CatalogState::default()
    }
}

/// # Catalog
///
/// The catalog is the authoritative registry of all databases and tables in a
/// Tempest instance. It maps stable numeric [`DatabaseId`]s and [`TableId`]s to
/// their definitions, and persists every mutation to a [`Journal`] for recovery
/// across restarts.
///
/// All mutations are validated before being written - nothing reaches the journal
/// that would not survive replay. Reads are served directly from the in-memory
/// [`CatalogState`] via [`Deref`].
pub(crate) struct Catalog<F: FioFS> {
    journal: Journal<CatalogState, F>,
}

impl<F: FioFS> Catalog<F> {
    /// Opens the catalog at `tempest_root/catalog`, replaying any existing
    /// journal to restore state. Creates the directory if it does not exist.
    #[instrument(skip_all, level = "info")]
    pub async fn open(
        fs: F,
        tempest_root: PathBuf,
        config: CatalogConfig,
    ) -> Result<Self, CatalogError> {
        info!("opening catalog at {:?}", tempest_root);
        let catalog_dir = tempest_root.join("catalog");
        let journal =
            Journal::<CatalogState, _>::open(fs, catalog_dir, config.journal_config()).await?;

        info!("finished opening catalog");

        Ok(Self { journal })
    }
    /// Registers a new database, returning its assigned [`DatabaseId`].
    ///
    /// # Errors
    ///
    /// - [`CatalogError::DatabaseAlreadyExists`]: A database with the same name already exists.
    #[instrument(skip_all, level = "info")]
    pub async fn create_database(
        &mut self,
        schema: DatabaseSchema,
    ) -> Result<DatabaseId, CatalogError> {
        let (id, edit) = self.create_database_edit(schema)?;
        debug!("perstisting database schema to journal");
        self.journal.append(edit).await?;
        Ok(id)
    }

    /// Registers a new table within an existing database, returning its assigned [`TableId`].
    ///
    /// # Errors
    ///
    /// - [`CatalogError::DatabaseNotFound`]: The table's `database_id` does not correspond to
    ///   a known database.
    /// - [`CatalogError::TableAlreadyExists`]: A table with the same name already exists within
    ///   that database.
    #[instrument(skip_all, level = "info")]
    pub async fn create_table(&mut self, schema: TableSchema) -> Result<TableId, CatalogError> {
        let (id, edit) = self.create_table_edit(schema)?;
        debug!("perstisting table schema to journal");
        self.journal.append(edit).await?;
        Ok(id)
    }
}

// Allow for accessing the current state, like the databases, tables, etc., directly through the
// `Catalog`, just as if it contained them itself. Makes the external use cleaner.
impl<F: FioFS> Deref for Catalog<F> {
    type Target = CatalogState;

    fn deref(&self) -> &Self::Target {
        &self.journal.state()
    }
}
