use tempest::prelude::*;

#[tokio::main]
async fn main() {
    let kv = InMemoryKvStore::new();
    let tempest = Tempest::init(kv).await;
}
