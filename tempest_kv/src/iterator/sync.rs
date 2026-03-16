use std::task::{Context, Poll};

use bytes::Bytes;

use crate::{
    base::{Comparer, InternalKey, StorageResult},
    iterator::StorageIterator,
};

/// A [`StorageIterator`] adapter for synchronous, in-memory [`Iterator`]s.
///
/// Many data sources in Tempest (e.g. [`MemTable`], [`BlockIterator`]) are inherently
/// synchronous and never need to return [`Poll::Pending`]. This wrapper allows any
/// [`Iterator`] over `(InternalKey<C>, Bytes)` pairs to be used wherever a
/// [`StorageIterator`] is expected, by always returning [`Poll::Ready`].
///
/// The current item is stored internally after each [`Iterator::next`] call and
/// exposed via the [`StorageIterator::key`] and [`StorageIterator::value`] methods.
///
/// [`MemTable`]: crate::memtable::MemTable
/// [`BlockIterator`]: crate::sst::block::BlockIterator
pub struct SyncIterator<C, I>
where
    C: Comparer,
    I: Iterator<Item = (InternalKey<C>, Bytes)>,
{
    /// The underlying synchronous iterator being wrapped.
    inner: I,
    /// The most recently yielded key-value pair, accessible via [`StorageIterator::key`]
    /// and [`StorageIterator::value`]. `None` if the iterator has not been polled yet
    /// or has been exhausted.
    current: Option<(InternalKey<C>, Bytes)>,
}

impl<C, I> SyncIterator<C, I>
where
    C: Comparer,
    I: Iterator<Item = (InternalKey<C>, Bytes)>,
{
    /// Creates a new instance that adapts to `inner` synchronously.
    pub(crate) fn new(inner: I) -> Self {
        Self {
            inner,
            current: None,
        }
    }
}

impl<C, I> Iterator for SyncIterator<C, I>
where
    C: Comparer,
    I: Iterator<Item = (InternalKey<C>, Bytes)>,
{
    type Item = (InternalKey<C>, Bytes);

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.inner.next()?;
        self.current = Some(item.clone());
        Some(item)
    }
}

impl<'i, C, I> StorageIterator<'i, C> for SyncIterator<C, I>
where
    C: Comparer,
    I: Iterator<Item = (InternalKey<C>, Bytes)>,
{
    fn poll_next(&mut self, _cx: &mut Context<'_>) -> Poll<StorageResult<Option<()>>> {
        if let Some((k, v)) = self.inner.next() {
            // cheap arc increments
            self.current = Some((k.clone(), v.clone()));
            Poll::Ready(Ok(Some(())))
        } else {
            self.current = None;
            Poll::Ready(Ok(None))
        }
    }

    fn poll_seek(&mut self, key: &[u8], _cx: &mut Context<'_>) -> Poll<StorageResult<()>> {
        loop {
            match self.inner.next() {
                Some((k, v)) => {
                    if C::compare_logical(k.key(), key).is_ge() {
                        self.current = Some((k, v));
                        return Poll::Ready(Ok(()));
                    }
                }
                None => {
                    self.current = None;
                    return Poll::Ready(Ok(()));
                }
            }
        }
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.current.as_ref().map(|(k, _v)| k)
    }

    fn value(&self) -> Option<&Bytes> {
        self.current.as_ref().map(|(_k, v)| v)
    }
}
