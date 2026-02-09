use std::sync::Arc;

use tempest::prelude::*;
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
    let conn = tempest
        .create_db("main".try_into().unwrap())
        .await
        .expect("could not create main database");
    println!("connection: {:#?}", conn);
}
