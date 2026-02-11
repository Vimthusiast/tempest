use std::sync::Arc;

use tempest::{prelude::*, schema};
use tokio::fs;

#[tokio::main]
async fn main() {
    let data_dir = "data";
    fs::create_dir_all(data_dir)
        .await
        .expect("could not create data directory");
    let kv = InMemoryKvStore::new();
    let manifest_manager = FileSystemManifestManager::open(data_dir)
        .await
        .expect("could not open manifest manager");
    let tempest = Tempest::init(Arc::new(kv), Arc::new(manifest_manager)).await;
    let db_ctx = tempest
        .create_db("main".try_into().unwrap())
        .await
        .expect("could not create main database");
    println!("database main: {:#?}", db_ctx);
    // insert some data in this scope
    {
        let users_schema = schema!(Table("users") {
            id: Int8,
            alive: Bool,
        }, pk(id));
        println!("schema for users: {:#?}", users_schema);
        let users_ctx = db_ctx
            .create_table("users".try_into().unwrap(), true, users_schema)
            .await
            .expect("could not create users table");
        println!("table users: {:#?}", users_ctx);
    }
}
