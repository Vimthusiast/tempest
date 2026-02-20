use std::io;

use crate::fio::FioFS;

mod sst;

#[derive(Debug, Display, From, Error)]
pub(crate) enum KvStoreError {
    IoError(io::Error),
}

pub(crate) type KvStoreResult<T> = Result<T, KvStoreError>;

pub(crate) struct WriteBatch {
    data: (),
}

#[derive(Debug)]
pub(crate) struct KvStore<F: FioFS> {
    fs: F,
}

impl<F: FioFS> KvStore<F> {
    pub(crate) fn get(&self, key: &[u8]) -> KvStoreResult<Option<Vec<u8>>> {
        todo!()
    }

    pub(crate) fn write(&self, batch: WriteBatch) -> KvStoreResult<()> {
        todo!()
    }
}
