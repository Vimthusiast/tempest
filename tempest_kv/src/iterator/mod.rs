use std::{
    marker::PhantomData,
    pin::Pin,
    task::{Context, Poll},
};

use bytes::Bytes;

use crate::base::{Comparer, InternalKey, SeqNum, StorageResult};

pub mod dedup;
pub mod merging;
pub mod snapshot;
pub mod sync;

pub use dedup::*;
pub use merging::*;
pub use snapshot::*;
pub use sync::*;

#[cfg(test)]
mod tests;

pub trait StorageIterator<'i, C: Comparer> {
    /// Tries to poll the next key-value pair into this iterator.
    /// They can be accessed through the [`key`] and [`value`] methods.
    ///
    /// [`key`]: StorageIterator::key
    /// [`value`]: StorageIterator::value
    fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<StorageResult<Option<()>>>;

    /// Tries to advance this iterator to the first key greater than or equal to `key`,
    /// determined by [logical not physical ordering](Comparer).
    /// After a successful poll, [`key`] and [`value`] will reflect the seeked-to entry,
    /// or `None` if no such entry exists.
    ///
    /// [`key`]: StorageIterator::key
    /// [`value`]: StorageIterator::value
    fn poll_seek(&mut self, key: &[u8], cx: &mut Context<'_>) -> Poll<StorageResult<()>>;

    /// Returns the last key that was polled.
    fn key(&self) -> Option<&InternalKey<C>>;
    /// Returns the last value that was polled.
    fn value(&self) -> Option<&Bytes>;

    /// Returns a future that resolves on the next element.
    fn next(&mut self) -> Next<'_, 'i, Self, C>
    where
        Self: Sized,
    {
        Next {
            iter: self,
            _marker: PhantomData,
        }
    }

    /// Returns a future that advances this iterator to the first key greater than or
    /// equal to `key`. Equivalent to calling [`poll_seek`] until it returns [`Poll::Ready`].
    ///
    /// [`poll_seek`]: StorageIterator::poll_seek
    fn seek<'a>(&'a mut self, key: &'a [u8]) -> Seek<'a, 'i, Self, C>
    where
        Self: Sized,
    {
        Seek {
            iter: self,
            key,
            _marker: PhantomData,
        }
    }
}

#[must_use = "futures do nothing unless awaited"]
pub struct Next<'a, 'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    iter: &'a mut I,
    _marker: PhantomData<&'i C>,
}

impl<'a, 'i, I, C> Future for Next<'a, 'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    type Output = StorageResult<Option<()>>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.iter.poll_next(cx)
    }
}

#[must_use = "futures do nothing unless awaited"]
pub struct Seek<'a, 'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    iter: &'a mut I,
    key: &'a [u8],
    _marker: PhantomData<&'i C>,
}

impl<'a, 'i, I, C> Future for Seek<'a, 'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    type Output = StorageResult<()>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: we do not move out of self
        let this = unsafe { self.get_unchecked_mut() };
        this.iter.poll_seek(this.key, cx)
    }
}
