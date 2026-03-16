use std::{
    cmp::Ordering,
    collections::BinaryHeap,
    task::{Context, Poll},
};

use bytes::Bytes;

use crate::{
    base::{Comparer, InternalKey, StorageResult},
    iterator::StorageIterator,
};

pub struct MergingIteratorHeapEntry<'i, C: Comparer> {
    /// The internal iterator implementation.
    pub iter: Box<dyn StorageIterator<'i, C> + 'i>,

    /// Higher ID = newer source. The active memtable has the highest priority, so u64::MAX.
    /// The first immutable memtable gets `u64::MAX-1`, then `-2`, and so on.
    /// The SST iterators are assigned their file id for newer to older ordering.
    pub source_id: u64,
}

impl<'i, C: Comparer> MergingIteratorHeapEntry<'i, C> {
    pub fn new<I: StorageIterator<'i, C> + 'i>(iter: I, source_id: u64) -> Self {
        Self {
            iter: Box::new(iter),
            source_id,
        }
    }
}

impl<'i, C: Comparer> PartialEq for MergingIteratorHeapEntry<'i, C> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl<'i, C: Comparer> Eq for MergingIteratorHeapEntry<'i, C> {}

impl<'i, C: Comparer> PartialOrd for MergingIteratorHeapEntry<'i, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// NB: When implementing ordering of max-heap entries, greater values will bubble up,
// therefore, when a is some and b is none, a > b.
impl<'i, C: Comparer> Ord for MergingIteratorHeapEntry<'i, C> {
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

enum MergingIteratorState<'i, C: Comparer> {
    // The merging iterator still has to poll some source iterators.
    Initializing {
        sources: Vec<MergingIteratorHeapEntry<'i, C>>,
    },
    // The merging iterator has been initialized
    Active,
}

pub struct MergingIterator<'i, C: Comparer> {
    state: MergingIteratorState<'i, C>,
    heap: BinaryHeap<MergingIteratorHeapEntry<'i, C>>,
    current: Option<(InternalKey<C>, Bytes)>,
}

impl<'i, C: Comparer> MergingIterator<'i, C> {
    pub fn new(sources: Vec<MergingIteratorHeapEntry<'i, C>>) -> Self {
        Self {
            state: MergingIteratorState::Initializing { sources },
            heap: Default::default(),
            current: None,
        }
    }
}

impl<'i, C: Comparer> StorageIterator<'i, C> for MergingIterator<'i, C> {
    fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<StorageResult<Option<()>>> {
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

    fn poll_seek(&mut self, key: &[u8], cx: &mut Context<'_>) -> Poll<StorageResult<()>> {
        // seek all sources in the heap
        let mut entries: Vec<_> = self.heap.drain().collect();

        // also seek any still-initializing sources
        if let MergingIteratorState::Initializing { ref mut sources } = self.state {
            entries.append(sources);
            self.state = MergingIteratorState::Active;
        }

        let mut i = 0;
        while i < entries.len() {
            match entries[i].iter.poll_seek(key, cx) {
                Poll::Ready(Ok(())) => {
                    if entries[i].iter.key().is_some() {
                        i += 1;
                    } else {
                        // seeked past end, discard
                        entries.swap_remove(i);
                    }
                }
                Poll::Pending => return Poll::Pending,
                Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
            }
        }

        // rebuild heap from seeked sources, with the new ordering intact
        self.current = None;
        self.heap = entries.into_iter().collect();

        Poll::Ready(Ok(()))
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.current.as_ref().map(|(k, _v)| k)
    }

    fn value(&self) -> Option<&Bytes> {
        self.current.as_ref().map(|(_k, v)| v)
    }
}
