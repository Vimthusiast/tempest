use std::collections::HashMap;

use tempest::{
    Tempest,
    core::DataValue,
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
                        data_type: "string".into(),
                    },
                    ColumnDef {
                        name: "age".into(),
                        data_type: "int8".into(),
                    },
                ],
                primary_key: vec!["name".into()],
            }),
        )
        .await
        .unwrap();

    let table = "users".into();
    let mut columns = HashMap::new();
    columns.insert("name".into(), Expr::Literal(DataValue::String("john".into())));
    columns.insert("age".into(), Expr::Literal(DataValue::Int8(30)));
    let query_stmt = QueryStmt::Insert(InsertStmt { table, columns });
    tempest.execute(db.clone(), query_stmt).await.unwrap();
}
