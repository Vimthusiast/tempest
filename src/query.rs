use std::collections::HashSet;

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::{Column, DataType, Row, TableSchema, Tempest, Value};

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
pub enum Expr {
    Literal(Value),
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

pub struct CreateTableStmt {
    /// Name of the table
    pub name: String,
    /// List of column definitions
    pub column_defs: Vec<ColumnDef>,
    /// List of column names for the PK.
    // TODO: Make a list of indices later.
    pub primary_key: Vec<String>,
}

pub struct InsertStmt {
    pub table: String,
    pub columns: Vec<String>,
    pub values: Vec<Expr>,
}

pub enum QueryStmt {
    CreateTable(CreateTableStmt),
    Insert(InsertStmt),
}

#[derive(Debug)]
pub enum QueryPlan {
    CreateTable {
        name: String,
        schema: TableSchema,
    },
    Insert {
        table: String,
        columns: Vec<String>,
        values: Vec<Value>,
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
    async fn plan_execution(&self, sql: QueryStmt) -> Result<QueryPlan, QueryError> {
        match sql {
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

                let mut primary_key = Vec::new();
                for col in stmt.primary_key {
                    let pos = columns
                        .iter()
                        .position(|c| c.name == col)
                        .ok_or_else(|| QueryError::ColumnDoesNotExist(col.clone()))?;
                    if primary_key.contains(&pos) {
                        println!(
                            "WARNING: duplicate definition of column for primary key found in query for '{}'",
                            col
                        );
                        continue;
                    }
                    primary_key.push(pos);
                }

                let schema = TableSchema {
                    columns,
                    primary_key,
                };

                Ok(QueryPlan::CreateTable {
                    name: stmt.name,
                    schema,
                })
            }
            QueryStmt::Insert(stmt) => todo!(),
        }
    }

    pub async fn execute_plan(
        &self,
        database: String,
        plan: QueryPlan,
    ) -> Result<Vec<Row>, QueryError> {
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
    pub async fn execute(&self, database: String, sql: QueryStmt) -> Result<Vec<Row>, QueryError> {
        // -- Phase 1: Query Statement Planning --
        let plan = self.plan_execution(sql).await?;

        // -- Phase 2: Execute the Query --
        self.execute_plan(database, plan).await
    }
}
