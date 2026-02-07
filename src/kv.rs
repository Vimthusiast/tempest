use std::{ops::Bound, sync::Arc};

use async_trait::async_trait;
use futures::{
    StreamExt,
    stream::{self, BoxStream},
};
use tokio::sync::RwLock;

#[async_trait]
pub trait KvStore: Send + Sync {
    async fn get(&self, key: &[u8]) -> Option<Vec<u8>>;
    async fn set(&self, key: Vec<u8>, value: Option<Vec<u8>>);
    fn scan<'a>(
        &self,
        start: Bound<&'a [u8]>,
        end: Bound<&'a [u8]>,
    ) -> BoxStream<'a, (Vec<u8>, Vec<u8>)>;
}

#[derive(Default)]
pub struct InMemoryKvStore {
    inner: Arc<RwLock<std::collections::BTreeMap<Vec<u8>, Vec<u8>>>>,
}

impl InMemoryKvStore {
    pub fn new() -> Self {
        Default::default()
    }
}

#[async_trait]
impl KvStore for InMemoryKvStore {
    async fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.inner.read().await.get(key).cloned()
    }

    async fn set(&self, key: Vec<u8>, value: Option<Vec<u8>>) {
        if let Some(value) = value {
            self.inner.write().await.insert(key, value);
        } else {
            self.inner.write().await.remove(&key);
        }
    }

    fn scan<'a>(
        &self,
        start: Bound<&'a [u8]>,
        end: Bound<&'a [u8]>,
    ) -> BoxStream<'a, (Vec<u8>, Vec<u8>)> {
        let inner_clone = self.inner.clone();

        stream::once(async move {
            let read_guard = inner_clone.read_owned().await;

            let data: Vec<(Vec<u8>, Vec<u8>)> = read_guard
                .range::<[u8], _>((start, end))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            data
        })
        .flat_map(stream::iter)
        .boxed()
    }
}
