use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{
    Column, DataType, TableSchema, Tempest,
    core::{DataValue, Key, Row},
};

#[derive(logos::Logos)]
enum SqlToken<'buf> {
    #[token("(")]
    OpenParen,
    #[token(")")]
    CloseParen,
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]+")]
    Identifier(&'buf str),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BinaryOperator {
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UnaryOperator {
    Not,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr<'a> {
    Literal(DataValue<'a>),
    //Column(String),
    //BinaryOp {
    //    left: Box<Expr>,
    //    op: BinaryOperator,
    //    right: Box<Expr>,
    //},
    //UnaryOp {
    //    op: UnaryOperator,
    //    val: Box<Expr>,
    //},
}

#[derive(Debug)]
pub struct ColumnDef {
    /// Name of the column
    pub name: String,
    /// Type of the column value
    pub data_type: String,
    // Is this nullable?
    //pub nullable: bool,
    // Expression for a default value
    //pub default: Option<Expr>,
}

#[derive(Debug)]
pub struct CreateTableStmt {
    /// Name of the table
    pub name: String,
    /// List of column definitions
    pub column_defs: Vec<ColumnDef>,
    /// List of column names for the PK.
    // TODO: Make a list of indices later.
    pub primary_key: Vec<String>,
}

#[derive(Debug)]
pub struct InsertStmt<'a> {
    pub table: String,
    pub columns: HashMap<String, Expr<'a>>,
}

#[derive(Debug)]
pub enum QueryStmt<'a> {
    CreateTable(CreateTableStmt),
    Insert(InsertStmt<'a>),
}

#[derive(Debug)]
pub enum QueryPlan<'a> {
    CreateTable {
        name: String,
        schema: TableSchema,
    },
    Insert {
        table: String,
        columns: Vec<String>,
        values: Vec<DataValue<'a>>,
    },
}

#[derive(Debug, Display, Error)]
pub enum QueryError {
    #[display("Encountered duplicate column names in query: {}.", _0.iter().join(", "))]
    DuplicateColumnNames(#[error(not(source))] Vec<String>),
    ColumnDoesNotExist(#[error(not(source))] String),
    TableDoesNotExist(#[error(not(source))] String),
    #[display("The required columns where not provided: {}.", _0.iter().join(", "))]
    RequiredColumnsNotProvided(#[error(not(source))] Vec<String>),
}

impl Tempest {
    // this should handle possible 'lazy evaluation' and evaluation to
    // other columns in a query later
    fn evaluate_expr<'a>(&self, expr: &Expr<'a>) -> DataValue<'a> {
        match expr {
            Expr::Literal(lit) => lit.clone(),
        }
    }

    async fn plan_execution(
        &self,
        db: String,
        query: QueryStmt<'_>,
    ) -> Result<QueryPlan<'_>, QueryError> {
        println!("Planning query: {:#?}", query);
        match query {
            QueryStmt::CreateTable(stmt) => {
                // check for duplicates
                let mut duplicates = Vec::new();
                let mut col_names = HashSet::new();
                for def in &stmt.column_defs {
                    if col_names.contains(&def.name) {
                        duplicates.push(def.name.clone());
                    }
                    col_names.insert(def.name.clone());
                }
                if !duplicates.is_empty() {
                    return Err(QueryError::DuplicateColumnNames(duplicates));
                }

                let mut columns = Vec::new();
                for def in stmt.column_defs {
                    let data_type = match def.data_type.as_ref() {
                        "int8" => DataType::Int8,
                        "string" => DataType::String,
                        "bool" => DataType::Bool,
                        _ => panic!("unknown data type: {}", def.data_type),
                    };
                    let col = Column {
                        name: def.name,
                        data_type,
                        //nullable: def.nullable,
                        //default: def.default,
                    };
                    columns.push(col)
                }

                let pk_duplicates = stmt.primary_key.iter().duplicates().cloned().collect_vec();
                if pk_duplicates.len() > 0 {
                    return Err(QueryError::DuplicateColumnNames(pk_duplicates));
                }

                let primary_key = stmt
                    .primary_key
                    .into_iter()
                    .map(|pk_name| {
                        columns
                            .iter()
                            .position(|col| col.name == pk_name)
                            .ok_or_else(|| QueryError::ColumnDoesNotExist(pk_name))
                    })
                    .try_collect()?;

                let schema = TableSchema {
                    columns,
                    primary_key,
                };

                Ok(QueryPlan::CreateTable {
                    name: stmt.name,
                    schema,
                })
            }
            QueryStmt::Insert(stmt) => {
                let Some(schema) = self
                    .catalog
                    .get_schema(db.clone(), stmt.table.clone())
                    .await
                else {
                    return Err(QueryError::TableDoesNotExist(stmt.table));
                };

                // get the key columns from the schema
                let schema_pk_cols = schema
                    .primary_key
                    .iter()
                    .map(|&i| &schema.columns[i])
                    .collect_vec();
                // check if any pk is missing from the insert statement
                let missing_pks = schema_pk_cols
                    .iter()
                    .map(|&pk| &pk.name)
                    // NB: here, we could also let through if the column has a default definition that
                    // can be evaluated successfully, i.e. not another unsupplied column.
                    // NB: we should likely evaluate unsupplied columns with defaults before, do
                    // keep this simple here, just like it is now
                    .filter(|schema_pk| {
                        // TODO: horrible performance here? check that
                        !stmt.columns.keys().contains(schema_pk)
                    })
                    .cloned();

                // get the value columns from the schema
                let schema_value_cols = schema
                    .columns
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, col)| {
                        if !schema.primary_key.contains(&idx) {
                            Some(col)
                        } else {
                            None
                        }
                    })
                    .collect_vec();
                // check which value columns are missing
                let missing_value_cols = schema_value_cols
                    .iter()
                    .map(|col| &col.name)
                    .filter(|schema_value_col| !stmt.columns.keys().contains(schema_value_col))
                    .cloned();

                let missing_cols = missing_pks.chain(missing_value_cols).collect_vec();
                if missing_cols.len() > 0 {
                    return Err(QueryError::RequiredColumnsNotProvided(missing_cols));
                }

                // now we have every required value and can begin encoding the kv pair
                let mut pk_bytes = Vec::new();
                for val_expr in schema_pk_cols.iter().map(|col| {
                    stmt.columns
                        .get(&col.name)
                        .expect("just checked that every col is supplied")
                }) {
                    // evaluate expression
                    let val = self.evaluate_expr(val_expr);
                    // store value in primary key bytes
                    val.encode_lexicographically(&mut pk_bytes);
                }
                let key = Key::new_borrowed(&db, &stmt.table, &pk_bytes);
                let key_bytes = key.encode();
                println!(
                    "encoded key bytes: [{}]",
                    key_bytes.iter().map(|b| format!("{:02x}", b)).join(" ")
                );

                todo!()
            }
        }
    }

    pub async fn execute_plan(
        &self,
        database: String,
        plan: QueryPlan<'_>,
    ) -> Result<Vec<Row<'_>>, QueryError> {
        println!("Executing query {:#?}", plan);
        let rows = Vec::new();
        match plan {
            QueryPlan::CreateTable {
                name: table,
                schema,
            } => self.catalog.set_schema(database, table, schema).await,
            QueryPlan::Insert {
                table,
                columns,
                values,
            } => {
                // retrieve the schema for the table
                let Some(schema) = self
                    .catalog
                    .get_schema(database.clone(), table.clone())
                    .await
                else {
                    return Err(QueryError::TableDoesNotExist(table));
                };

                // check for missing values
                let missing = schema
                    .columns
                    .iter()
                    .filter(|&col| columns.contains(&col.name))
                    .map(|v| v.name.clone())
                    .collect_vec();
                if !missing.is_empty() {
                    return Err(QueryError::RequiredColumnsNotProvided(missing));
                }

                todo!()
            }
        }
        Ok(rows)
    }

    /// Execute a sql statement. Currently the input sql is the raw ast, but may be a string later.
    pub async fn execute(
        &self,
        database: String,
        sql: QueryStmt<'_>,
    ) -> Result<Vec<Row<'_>>, QueryError> {
        // -- Phase 1: Query Statement Planning --
        let plan = self.plan_execution(database.clone(), sql).await?;

        // -- Phase 2: Execute the Query --
        self.execute_plan(database, plan).await
    }
}
