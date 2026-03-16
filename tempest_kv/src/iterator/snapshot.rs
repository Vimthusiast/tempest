use std::{
    marker::PhantomData,
    task::{Context, Poll},
};

use bytes::Bytes;

use crate::{
    base::{Comparer, InternalKey, SeqNum, StorageResult},
    iterator::StorageIterator,
};

pub struct SnapshotIterator<'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    inner: I,
    snapshot: SeqNum,
    _marker: PhantomData<&'i C>,
}

impl<'i, I, C> SnapshotIterator<'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    pub fn new(inner: I, snapshot: SeqNum) -> Self {
        Self {
            inner,
            snapshot,
            _marker: PhantomData,
        }
    }
}

impl<'i, I, C> StorageIterator<'i, C> for SnapshotIterator<'i, I, C>
where
    I: StorageIterator<'i, C>,
    C: Comparer,
{
    fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<StorageResult<Option<()>>> {
        loop {
            match self.inner.poll_next(cx) {
                Poll::Ready(Ok(Some(()))) => {
                    let key = self.inner.key().unwrap();
                    if key.trailer().seqnum() <= self.snapshot {
                        return Poll::Ready(Ok(Some(())));
                    }
                    // seqnum too high, skip and keep polling
                }
                other => return other,
            }
        }
    }

    fn poll_seek(&mut self, key: &[u8], cx: &mut Context<'_>) -> Poll<StorageResult<()>> {
        self.inner.poll_seek(key, cx)
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.inner.key()
    }

    fn value(&self) -> Option<&Bytes> {
        self.inner.value()
    }
}
