use std::{
    cmp::Ordering,
    collections::BinaryHeap,
    task::{self, Poll},
};

use bytes::Bytes;

use crate::base::{Comparer, InternalKey, TempestResult};

pub trait TempestIterator<C: Comparer> {
    /// Tries to poll the next key-value pair into this iterator.
    /// They can be accessed through the [`key`] and [`value`] methods.
    ///
    /// [`key`]: LocalTempestIterator::key()
    /// [`value`]: LocalTempestIterator::value()
    fn poll_next(&mut self, cx: &mut task::Context<'_>) -> Poll<TempestResult<Option<()>>>;

    /// Returns the last key that was polled.
    fn key(&self) -> Option<&InternalKey<C>>;
    /// Returns the last value that was polled.
    fn value(&self) -> Option<&Bytes>;
}

pub struct MemTableIterator<'a, C: Comparer> {
    inner: std::iter::Peekable<std::collections::btree_map::Iter<'a, InternalKey<C>, Bytes>>,
    current: Option<(InternalKey<C>, Bytes)>,
}

impl<'a, C: Comparer> TempestIterator<C> for MemTableIterator<'a, C> {
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

pub struct MergingIteratorHeapEntry<C: Comparer> {
    /// The internal iterator implementation.
    pub iter: Box<dyn TempestIterator<C>>,

    /// Higher ID = newer source. The active memtable has the highest priority, so u64::MAX.
    /// The first immutable memtable gets `u64::MAX-1`, then `-2`, and so on.
    /// The SST iterators are assigned their file id for newer to older ordering.
    pub source_id: u64,
}

impl<C: Comparer> PartialEq for MergingIteratorHeapEntry<C> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl<C: Comparer> Eq for MergingIteratorHeapEntry<C> {}

impl<C: Comparer> PartialOrd for MergingIteratorHeapEntry<C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// NB: When implementing ordering of max-heap entries, greater values will bubble up.
// Therefore, when a is some and b is none, a > b.
impl<C: Comparer> Ord for MergingIteratorHeapEntry<C> {
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

enum MergingIteratorState<C: Comparer> {
    // The merging iterator still has to poll some source iterators.
    Initializing {
        sources: Vec<MergingIteratorHeapEntry<C>>,
    },
    // The merging iterator has been initialized
    Active,
}

pub struct MergingIterator<C: Comparer> {
    state: MergingIteratorState<C>,
    heap: BinaryHeap<MergingIteratorHeapEntry<C>>,
    current: Option<(InternalKey<C>, Bytes)>,
}

impl<C: Comparer> MergingIterator<C> {
    pub fn new(sources: Vec<MergingIteratorHeapEntry<C>>) -> Self {
        Self {
            state: MergingIteratorState::Initializing { sources },
            heap: Default::default(),
            current: None,
        }
    }
}

impl<C: Comparer> TempestIterator<C> for MergingIterator<C> {
    fn poll_next(&mut self, cx: &mut task::Context<'_>) -> Poll<TempestResult<Option<()>>> {
        if let MergingIteratorState::Initializing { ref mut sources } = self.state {
            trace!(sources = sources.len(), "Initializing merging iterator");
            let mut i = 0;
            while i < sources.len() {
                match sources[i].iter.poll_next(cx) {
                    Poll::Ready(Ok(Some(()))) => {
                        trace!("Source ready");
                        // Got more data, move to heap
                        let entry = sources.swap_remove(i);
                        self.heap.push(entry);
                    }
                    Poll::Ready(Ok(None)) => {
                        trace!("Source empty");
                        // Source is empty, discard it
                        sources.swap_remove(i);
                    }
                    Poll::Pending => {
                        trace!("Source still pending");
                        // Source is still pending, skip for now
                        i += 1;
                    }
                    Poll::Ready(Err(err)) => return Poll::Ready(Err(err)),
                }
            }

            if sources.is_empty() {
                trace!("Finished initializing merging iterator");
                self.state = MergingIteratorState::Active;
                if self.heap.is_empty() {
                    return Poll::Ready(Ok(None));
                }
            } else {
                trace!("Initializing finished, but still incomplete");
                return Poll::Pending;
            }
        }

        // If we already have a current value, the user is done with it and we must advance
        // our top iterator that provided the current value, before finding the next one.
        if self.current.is_some() {
            trace!("Polling sources");
            let mut top = self
                .heap
                .pop()
                .expect("Heap cannot be empty if current is not");
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
                    .expect("Iterators on heap must not be exhausted")
                    .clone(),
                top.iter
                    .value()
                    .expect("Iterators on heap must not be exhausted")
                    .clone(),
            ));
            trace!(current = ?self.current, "Got current value");
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

#[cfg(test)]
mod tests {
    use crate::base::DefaultComparer;
    use crate::tests::setup_tracing;

    use super::*;
    use std::sync::Arc;
    use std::task::{Context, Wake};

    // Helper to get a dummy context
    fn dummy_cx() -> Context<'static> {
        struct NoopWake;
        impl Wake for NoopWake {
            fn wake(self: Arc<Self>) {}
        }
        let waker: std::task::Waker = Arc::new(NoopWake).into();
        // mem transmute the arc to avoid lifetime issues
        unsafe { Context::from_waker(std::mem::transmute(&waker)) }
    }

    // A simple mock iterator for testing
    struct MockIterator<C: Comparer> {
        data: Vec<(InternalKey<C>, Bytes)>,
        pos: usize,
        pending_once: bool,
    }

    impl<C: Comparer> TempestIterator<C> for MockIterator<C> {
        fn poll_next(&mut self, _cx: &mut Context<'_>) -> Poll<TempestResult<Option<()>>> {
            if self.pending_once {
                self.pending_once = false;
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

    #[test]
    fn test_merging_interleave() {
        setup_tracing();

        let mut sources = Vec::new();
        // Source 1: IDs are 1 and 3
        sources.push(MergingIteratorHeapEntry {
            source_id: 1,
            iter: Box::new(MockIterator {
                data: vec![
                    (InternalKey::test(1), Bytes::from("a")),
                    (InternalKey::test(3), Bytes::from("c")),
                ],
                pos: 0,
                pending_once: false,
            }),
        });

        // Source 2: IDs are 2 and 4
        sources.push(MergingIteratorHeapEntry {
            source_id: 2,
            iter: Box::new(MockIterator {
                data: vec![
                    (InternalKey::test(2), Bytes::from("b")),
                    (InternalKey::test(4), Bytes::from("d")),
                ],
                pos: 0,
                pending_once: false,
            }),
        });

        let mut merger = MergingIterator::<DefaultComparer>::new(sources);
        let mut cx = dummy_cx();

        let mut results = Vec::new();
        while let Poll::Ready(Ok(Some(()))) = merger.poll_next(&mut cx) {
            results.push(merger.key().unwrap().user_key_as_u64());
        }

        assert_eq!(results, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_merging_source_priority() {
        setup_tracing();

        let mut sources = Vec::new();
        // Older source (e.g. SST)
        sources.push(MergingIteratorHeapEntry {
            source_id: 10,
            iter: Box::new(MockIterator {
                data: vec![(InternalKey::test(1), Bytes::from("old"))],
                pos: 0,
                pending_once: false,
            }),
        });
        // Newer source (e.g. MemTable)
        sources.push(MergingIteratorHeapEntry {
            source_id: 100,
            iter: Box::new(MockIterator {
                data: vec![(InternalKey::test(1), Bytes::from("new"))],
                pos: 0,
                pending_once: false,
            }),
        });

        let mut merger = MergingIterator::<DefaultComparer>::new(sources);
        let mut cx = dummy_cx();

        // First poll: should be the one with source_id 100
        assert!(merger.poll_next(&mut cx).is_ready());
        assert_eq!(merger.value().unwrap(), &Bytes::from("new"));

        // Second poll: should be the one with source_id 10
        assert!(merger.poll_next(&mut cx).is_ready());
        assert_eq!(merger.value().unwrap(), &Bytes::from("old"));
    }

    #[test]
    fn test_merging_pending_propagation() {
        setup_tracing();

        let mut heap = Vec::new();
        heap.push(MergingIteratorHeapEntry {
            source_id: 1,
            iter: Box::new(MockIterator {
                data: vec![(InternalKey::test(1), Bytes::from("val"))],
                pos: 0,
                pending_once: true, // Will return Pending on first call
            }),
        });

        let mut merger = MergingIterator::<DefaultComparer>::new(heap);
        let mut cx = dummy_cx();

        // First call: Should be Pending
        assert!(merger.poll_next(&mut cx).is_pending());

        // Second call: Mock is set to yield data now
        match merger.poll_next(&mut cx) {
            Poll::Ready(Ok(Some(()))) => assert_eq!(merger.key().unwrap().user_key_as_u64(), 1),
            _ => panic!("Expected Ready"),
        }
    }
}
