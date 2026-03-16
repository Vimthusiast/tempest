use std::{
    marker::PhantomData,
    task::{Context, Poll},
};

use bytes::Bytes;

use crate::{
    base::{Comparer, InternalKey, StorageResult},
    iterator::StorageIterator,
};

pub struct DeduplicatingIterator<'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    inner: I,
    last_key: Option<Bytes>,
    _marker: PhantomData<(&'i (), C)>,
}

impl<'i, I, C> DeduplicatingIterator<'i, I, C>
where
    I: StorageIterator<'i, C>,
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
/// A [`StorageIterator`] adapter that collapses multiple versions of the same
/// logical key into one, emitting only the first (newest) version seen.
///
/// Two keys are considered the same logical entry if [`C::compare_logical`]
/// returns [`Ordering::Equal`] - that is, their prefixes are equal regardless
/// of their suffix. This means that for a comparer with a version suffix (e.g.
/// an HLC timestamp), all versions of the same row are collapsed to the newest,
/// since physical ordering guarantees the newest suffix sorts first.
///
/// For [`DefaultComparer`], which has no suffix, this degenerates to simple
/// exact-key deduplication.
///
/// # Usage
///
/// Wrap a [`MergingIterator`] with this to deduplicate during compaction, or
/// sit it on top of a [`SuffixBoundIterator`] on the read path to collapse
/// the remaining visible versions of each row to one.
///
/// [`C::compare_logical`]: Comparer::compare_logical
/// [`Ordering::Equal`]: std::cmp::Ordering::Equal
impl<'i, I, C> StorageIterator<'i, C> for DeduplicatingIterator<'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<StorageResult<Option<()>>> {
        loop {
            match self.inner.poll_next(cx) {
                Poll::Ready(Ok(Some(()))) => {
                    let new_key = self.inner.key().expect("just polled the iterator");
                    let last_key = self.last_key.as_ref();

                    // if we have had a key already and the new one is logically equal
                    if let Some(last_key) = last_key
                        && C::compare_logical(new_key.key(), last_key).is_eq()
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

    fn poll_seek(&mut self, key: &[u8], cx: &mut Context<'_>) -> Poll<StorageResult<()>> {
        loop {
            match self.inner.poll_next(cx) {
                Poll::Ready(Ok(Some(()))) => {
                    let new_key = self.inner.key().expect("just polled the iterator");
                    // seek until we find the first key in range
                    if C::compare_logical(new_key.key(), key).is_lt() {
                        continue;
                    }

                    let last_key = self.last_key.as_ref();

                    // if we have had a key already and the new one is logically equal
                    if let Some(last_key) = last_key
                        && C::compare_logical(new_key.key(), last_key).is_eq()
                    {
                        // skip this key
                        continue;
                    }
                    self.last_key = Some(new_key.key().clone());
                    return Poll::Ready(Ok(()));
                }
                other => return other.map(|r| r.map(|_| ())),
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
