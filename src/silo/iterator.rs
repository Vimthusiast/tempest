use std::{
    any::type_name,
    cmp::Ordering,
    collections::BinaryHeap,
    marker::PhantomData,
    pin::Pin,
    task::{self, Context, Poll},
};

use bytes::Bytes;

use crate::base::{Comparer, InternalKey, TempestResult};

pub trait TempestIterator<'a, C: Comparer> {
    /// Tries to poll the next key-value pair into this iterator.
    /// They can be accessed through the [`key`] and [`value`] methods.
    ///
    /// [`key`]: TempestIterator::key()
    /// [`value`]: TempestIterator::value()
    fn poll_next(&mut self, cx: &mut task::Context<'_>) -> Poll<TempestResult<Option<()>>>;

    /// Returns the last key that was polled.
    fn key(&self) -> Option<&InternalKey<C>>;
    /// Returns the last value that was polled.
    fn value(&self) -> Option<&Bytes>;

    /// Returns a future that resolves on the next element.
    fn next(&mut self) -> Next<'_, 'a, Self, C>
    where
        Self: Sized,
    {
        Next {
            iter: self,
            _marker: PhantomData,
        }
    }
}

pub struct Next<'b, 'a, I, C>
where
    I: TempestIterator<'a, C>,
    C: Comparer,
{
    iter: &'b mut I,
    _marker: PhantomData<&'a C>,
}

impl<'b, 'a, I, C> Future for Next<'b, 'a, I, C>
where
    I: TempestIterator<'a, C>,
    C: Comparer,
{
    type Output = TempestResult<Option<()>>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.iter.poll_next(cx)
    }
}

pub struct MemTableIterator<'a, C: Comparer> {
    inner: std::iter::Peekable<std::collections::btree_map::Iter<'a, InternalKey<C>, Bytes>>,
    current: Option<(InternalKey<C>, Bytes)>,
}

impl<'a, C: Comparer> MemTableIterator<'a, C> {
    pub(super) fn new(
        inner: std::iter::Peekable<std::collections::btree_map::Iter<'a, InternalKey<C>, Bytes>>,
    ) -> Self {
        Self {
            inner,
            current: None,
        }
    }
}

impl<'a, C: Comparer> TempestIterator<'a, C> for MemTableIterator<'a, C> {
    fn poll_next(&mut self, _cx: &mut task::Context<'_>) -> Poll<TempestResult<Option<()>>> {
        if let Some((k, v)) = self.inner.next() {
            // cheap arc increments
            self.current = Some((k.clone(), v.clone()));
            Poll::Ready(Ok(Some(())))
        } else {
            self.current = None;
            Poll::Ready(Ok(None))
        }
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.current.as_ref().map(|(k, _v)| k)
    }

    fn value(&self) -> Option<&Bytes> {
        self.current.as_ref().map(|(_k, v)| v)
    }
}

pub struct MergingIteratorHeapEntry<'a, C: Comparer> {
    /// The internal iterator implementation.
    pub iter: Box<dyn TempestIterator<'a, C> + 'a>,

    /// Higher ID = newer source. The active memtable has the highest priority, so u64::MAX.
    /// The first immutable memtable gets `u64::MAX-1`, then `-2`, and so on.
    /// The SST iterators are assigned their file id for newer to older ordering.
    pub source_id: u64,
}

impl<'a, C: Comparer> MergingIteratorHeapEntry<'a, C> {
    pub fn new<I: TempestIterator<'a, C> + 'a>(iter: I, source_id: u64) -> Self {
        Self {
            iter: Box::new(iter),
            source_id,
        }
    }
}

impl<'a, C: Comparer> PartialEq for MergingIteratorHeapEntry<'a, C> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl<'a, C: Comparer> Eq for MergingIteratorHeapEntry<'a, C> {}

impl<'a, C: Comparer> PartialOrd for MergingIteratorHeapEntry<'a, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// NB: When implementing ordering of max-heap entries, greater values will bubble up.
// Therefore, when a is some and b is none, a > b.
impl<'a, C: Comparer> Ord for MergingIteratorHeapEntry<'a, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.iter.key(), other.iter.key()) {
            (Some(a), Some(b)) => a
                .cmp(b)
                .reverse()
                .then_with(|| self.source_id.cmp(&other.source_id)),
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}

enum MergingIteratorState<'a, C: Comparer> {
    // The merging iterator still has to poll some source iterators.
    Initializing {
        sources: Vec<MergingIteratorHeapEntry<'a, C>>,
    },
    // The merging iterator has been initialized
    Active,
}

pub struct MergingIterator<'a, C: Comparer> {
    state: MergingIteratorState<'a, C>,
    heap: BinaryHeap<MergingIteratorHeapEntry<'a, C>>,
    current: Option<(InternalKey<C>, Bytes)>,
}

impl<'a, C: Comparer> MergingIterator<'a, C> {
    pub fn new(sources: Vec<MergingIteratorHeapEntry<'a, C>>) -> Self {
        Self {
            state: MergingIteratorState::Initializing { sources },
            heap: Default::default(),
            current: None,
        }
    }
}

impl<'a, C: Comparer> TempestIterator<'a, C> for MergingIterator<'a, C> {
    fn poll_next(&mut self, cx: &mut task::Context<'_>) -> Poll<TempestResult<Option<()>>> {
        if let MergingIteratorState::Initializing { ref mut sources } = self.state {
            trace!(sources = sources.len(), "initializing merging iterator");
            let mut i = 0;
            while i < sources.len() {
                match sources[i].iter.poll_next(cx) {
                    Poll::Ready(Ok(Some(()))) => {
                        trace!("source ready");
                        // Got more data, move to heap
                        let entry = sources.swap_remove(i);
                        self.heap.push(entry);
                    }
                    Poll::Ready(Ok(None)) => {
                        trace!("source empty");
                        // Source is empty, discard it
                        sources.swap_remove(i);
                    }
                    Poll::Pending => {
                        trace!("source still pending");
                        // Source is still pending, skip for now
                        i += 1;
                    }
                    Poll::Ready(Err(err)) => return Poll::Ready(Err(err)),
                }
            }

            if sources.is_empty() {
                trace!("finished initializing merging iterator");
                self.state = MergingIteratorState::Active;
                if self.heap.is_empty() {
                    return Poll::Ready(Ok(None));
                }
            } else {
                trace!("initializing finished, but still incomplete");
                return Poll::Pending;
            }
        }

        // If we already have a current value, the user is done with it and we must advance
        // our top iterator that provided the current value, before finding the next one.
        if self.current.is_some() {
            trace!("polling sources");
            let mut top = self
                .heap
                .pop()
                .expect("heap cannot be empty if current is not");
            match top.iter.poll_next(cx) {
                Poll::Ready(Ok(Some(()))) => self.heap.push(top),
                Poll::Ready(Ok(None)) => {} // Iterator empty, do not push back
                Poll::Pending => {
                    self.heap.push(top);
                    return Poll::Pending;
                }
                Poll::Ready(Err(err)) => return Poll::Ready(Err(err)),
            }
        }

        if let Some(top) = self.heap.peek() {
            self.current = Some((
                top.iter
                    .key()
                    .expect("iterators on heap must not be exhausted")
                    .clone(),
                top.iter
                    .value()
                    .expect("iterators on heap must not be exhausted")
                    .clone(),
            ));
            trace!(current = ?self.current, "got current value");
            Poll::Ready(Ok(Some(())))
        } else {
            self.current = None;
            Poll::Ready(Ok(None))
        }
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.current.as_ref().map(|(k, _v)| k)
    }

    fn value(&self) -> Option<&Bytes> {
        self.current.as_ref().map(|(_k, v)| v)
    }
}

pub struct DeduplicatingIterator<'a, I, C>
where
    I: TempestIterator<'a, C>,
    C: Comparer,
{
    inner: I,
    last_key: Option<Bytes>,
    _marker: PhantomData<(&'a (), C)>,
}

impl<'a, I, C> DeduplicatingIterator<'a, I, C>
where
    I: TempestIterator<'a, C>,
    C: Comparer,
{
    pub fn new(inner: I) -> Self {
        Self {
            inner,
            last_key: None,
            _marker: PhantomData,
        }
    }
}

impl<'a, I, C> TempestIterator<'a, C> for DeduplicatingIterator<'a, I, C>
where
    I: TempestIterator<'a, C>,
    C: Comparer,
{
    fn poll_next(&mut self, cx: &mut task::Context<'_>) -> Poll<TempestResult<Option<()>>> {
        trace!(inner = type_name::<I>(), "polling deduplicating iterator");
        let c = C::default();
        loop {
            match self.inner.poll_next(cx) {
                Poll::Ready(Ok(Some(()))) => {
                    let new_key = self.inner.key().expect("just polled the iterator");
                    let last_key = self.last_key.as_ref();

                    // if we have had a key already and the new one is logically equal
                    if let Some(last_key) = last_key
                        && c.compare_logical(new_key.key(), last_key).is_eq()
                    {
                        // skip this key
                        continue;
                    }
                    self.last_key = Some(new_key.key().clone());
                    return Poll::Ready(Ok(Some(())));
                }
                other => return other,
            }
        }
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.inner.key()
    }

    fn value(&self) -> Option<&Bytes> {
        self.inner.value()
    }
}

#[cfg(test)]
mod tests {
    use crate::base::{DefaultComparer, FixedSuffixComparer, KeyKind, KeyTrailer};
    use crate::tests::setup_tracing;

    use super::*;
    use std::task::Context;

    // A simple mock iterator for testing
    #[derive(Default)]
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

    impl<C: Comparer> TempestIterator<'static, C> for MockIterator<C> {
        fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<TempestResult<Option<()>>> {
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
}
