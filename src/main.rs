use std::path::PathBuf;

use tempest_core::fio::UringFileSystem;
use tempest_engine::{Engine, config::EngineConfig};

fn main() {
    tokio_uring::start(async {
        let fs = UringFileSystem;
        let root = PathBuf::from("./tmp/tempest");
        let config = EngineConfig::default();
        let mut engine = Engine::open(fs.clone(), root, config).await.unwrap();
        engine.execute("create database main;").await.unwrap();
        engine
            .execute("create type main.User { id: Int64, username: String };")
            .await
            .unwrap();
        engine
            .execute("create table main.users : main.User { primary key (id) };")
            .await
            .unwrap();
        engine
            .execute("insert into main.users { id: 4, username: \"John\" };")
            .await
            .unwrap();

        engine.shutdown().await.unwrap();
    })
}
