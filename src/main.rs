use tempest::{ColumnDef, CreateTableStmt, InMemoryKvStore, QueryStmt, Tempest};

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
}
