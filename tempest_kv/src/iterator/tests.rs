use tempest_core::test_utils::setup_tracing;

use crate::base::{DefaultComparer, FixedSuffixComparer, KeyKind, KeyTrailer};

use super::*;
use std::task::Context;

// A simple mock iterator for testing
#[derive(Default, Clone)]
struct MockIterator<C: Comparer> {
    data: Vec<(InternalKey<C>, Bytes)>,
    pos: usize,
    pending_once: bool,
}

impl<C: Comparer> MockIterator<C> {
    fn new() -> Self {
        Default::default()
    }

    fn add(mut self, key_id: u64, value: impl Into<Bytes>) -> Self {
        self.data.push((InternalKey::test(key_id), value.into()));
        self
    }

    fn add_with_key(mut self, key: InternalKey<C>, value: impl Into<Bytes>) -> Self {
        self.data.push((key, value.into()));
        self
    }

    fn pending_once(mut self, val: bool) -> Self {
        self.pending_once = val;
        self
    }
}

impl<C: Comparer> StorageIterator<'static, C> for MockIterator<C> {
    fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<StorageResult<Option<()>>> {
        if self.pending_once {
            self.pending_once = false;
            // We must wake the context, or the executor hangs forever
            cx.waker().wake_by_ref();
            return Poll::Pending;
        }
        if self.pos < self.data.len() {
            self.pos += 1;
            Poll::Ready(Ok(Some(())))
        } else {
            Poll::Ready(Ok(None))
        }
    }

    fn poll_seek(&mut self, key: &[u8], cx: &mut Context<'_>) -> Poll<StorageResult<()>> {
        if self.pending_once {
            self.pending_once = false;
            cx.waker().wake_by_ref();
            return Poll::Pending;
        }
        self.pos = match self
            .data
            .iter()
            .position(|(k, _)| C::compare_prefix(k.key(), key) != std::cmp::Ordering::Less)
        {
            Some(i) => i + 1,
            None => self.data.len() + 1,
        };
        Poll::Ready(Ok(()))
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.data.get(self.pos - 1).map(|x| &x.0)
    }

    fn value(&self) -> Option<&Bytes> {
        self.data.get(self.pos - 1).map(|x| &x.1)
    }
}

#[tokio::test]
async fn test_merging_interleave() {
    setup_tracing();

    let mut sources = Vec::new();
    sources.push(MergingIteratorHeapEntry::new(
        MockIterator::new().add(1, "a").add(3, "c"),
        1,
    ));
    sources.push(MergingIteratorHeapEntry::new(
        MockIterator::new().add(2, "b").add(4, "d"),
        2,
    ));

    let mut merger = MergingIterator::<DefaultComparer>::new(sources);
    let mut results = Vec::new();

    while let Ok(Some(())) = merger.next().await {
        results.push(merger.key().unwrap().test_key_as_u64());
    }

    assert_eq!(results, vec![1, 2, 3, 4]);
}

#[tokio::test]
async fn test_merging_source_priority() {
    setup_tracing();

    let mut sources = Vec::new();
    sources.push(MergingIteratorHeapEntry::new(
        MockIterator::new().add(1, "old"),
        10,
    ));
    sources.push(MergingIteratorHeapEntry::new(
        MockIterator::new().add(1, "new"),
        100,
    ));

    let mut merger = MergingIterator::<DefaultComparer>::new(sources);

    // First item: source_id 100 wins
    assert!(matches!(merger.next().await, Ok(Some(()))));
    assert_eq!(merger.value().unwrap(), &Bytes::from("new"));

    // Second item: source_id 10
    assert!(matches!(merger.next().await, Ok(Some(()))));
    assert_eq!(merger.value().unwrap(), &Bytes::from("old"));
}

#[tokio::test]
async fn test_merging_pending_propagation() {
    setup_tracing();

    let mut sources = Vec::new();
    sources.push(MergingIteratorHeapEntry::new(
        MockIterator::<DefaultComparer>::new()
            .add(1, "val")
            .pending_once(true),
        1,
    ));

    let mut merger = MergingIterator::<DefaultComparer>::new(sources);

    // The first .await will yield Pending and then resume.
    // If we want to test the intermediate Pending state specifically,
    // we'd use a manual poll, but for behavior, next().await is sufficient.
    let res = merger.next().await;
    assert!(matches!(res, Ok(Some(()))));
    assert_eq!(merger.key().unwrap().test_key_as_u64(), 1);
}

#[tokio::test]
async fn test_deduplicating_with_different_trailers() {
    setup_tracing();
    let key_a_bytes = Bytes::from("user1");
    let key_a_v2 = InternalKey::new(
        key_a_bytes.clone(),
        KeyTrailer::new(100.try_into().unwrap(), KeyKind::Put),
    );
    let key_a_v1 = InternalKey::new(
        key_a_bytes,
        KeyTrailer::new(50.try_into().unwrap(), KeyKind::Put),
    );

    let inner = MockIterator::<DefaultComparer>::new()
        .add_with_key(key_a_v2, "new-val")
        .add_with_key(key_a_v1, "old-val");

    let mut deduplicating_iter = DeduplicatingIterator::new(inner);

    // Version 2 comes first
    assert!(matches!(deduplicating_iter.next().await, Ok(Some(()))));
    assert_eq!(deduplicating_iter.value().unwrap(), &Bytes::from("new-val"));

    // Version 1 is skipped automatically by the deduplicator
    assert!(matches!(deduplicating_iter.next().await, Ok(None)));
}

#[tokio::test]
async fn test_deduplicating_with_fixed_suffix() {
    setup_tracing();

    let key_v2 = InternalKey::new(
        Bytes::from("user1B"),
        KeyTrailer::new(100.try_into().unwrap(), KeyKind::Put),
    );
    let key_v1 = InternalKey::new(
        Bytes::from("user1A"),
        KeyTrailer::new(50.try_into().unwrap(), KeyKind::Put),
    );

    let inner = MockIterator::<FixedSuffixComparer<1>>::new()
        .add_with_key(key_v2, "val-version-B")
        .add_with_key(key_v1, "val-version-A");

    let mut deduplicating_iter = DeduplicatingIterator::new(inner);

    // Yields B
    assert!(matches!(deduplicating_iter.next().await, Ok(Some(()))));
    assert_eq!(
        deduplicating_iter.value().unwrap(),
        &Bytes::from("val-version-B")
    );

    // Skips A because it shares the logical prefix "user1"
    assert!(matches!(deduplicating_iter.next().await, Ok(None)));
}
