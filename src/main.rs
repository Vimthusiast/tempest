use std::collections::HashMap;

use tempest::{
    Tempest,
    core::{TempestType, TempestValue},
    kv::InMemoryKvStore,
    query::{ColumnDef, CreateTableStmt, Expr, InsertStmt, QueryStmt},
};

#[tokio::main]
async fn main() {
    let kv = InMemoryKvStore::new();
    let tempest = Tempest::init(kv).await;

    let db = "db1".to_string();
    tempest
        .execute(
            db.clone(),
            QueryStmt::CreateTable(CreateTableStmt {
                name: "users".into(),
                column_defs: vec![
                    ColumnDef {
                        name: "name".into(),
                        tempest_type: vec![TempestType::String],
                    },
                    ColumnDef {
                        name: "age".into(),
                        tempest_type: vec![TempestType::Int8],
                    },
                ],
                primary_key: vec!["name".into()],
            }),
        )
        .await
        .unwrap();

    let table = "users".into();
    let mut columns = HashMap::new();
    columns.insert(
        "name".into(),
        Expr::Literal(TempestValue::String("john".into())),
    );
    columns.insert("age".into(), Expr::Literal(TempestValue::Int8(30)));
    let query_stmt = QueryStmt::Insert(InsertStmt { table, columns });
    tempest.execute(db.clone(), query_stmt).await.unwrap();
}
