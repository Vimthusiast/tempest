use std::{path::PathBuf, sync::Arc};

use crate::{
    base::{
        Comparer, DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum, TempestError,
        TempestResult,
    },
    fio::FioFS,
    silo::{batch::WriteBatch, manifest::SiloManifest, memtable::MemTable},
};

use bytes::{Buf, Bytes};
use integer_encoding::VarInt;
use tracing::instrument;

mod batch;
mod manifest;
mod memtable;

#[derive(Debug)]
pub(crate) struct Silo<F: FioFS, C: Comparer = DefaultComparer> {
    /// The ID of this silo.
    id: u16,
    /// The root directory for this silo.
    root_dir: PathBuf,

    /// The manifest that manages state of this silo.
    manifest: SiloManifest<F>,

    /// The currently active memtable.
    active: MemTable<C>,
    /// The immutable memtables.
    immutables: Vec<Arc<MemTable<C>>>,

    /// This is `true`, when [`shutdown`] has been called.
    ///
    /// [`shutdown`]: Self::shutdown
    is_shutdown: bool,
}

fn read_varint(src: &[u8]) -> Option<(usize, usize)> {
    usize::decode_var(src)
}

impl<F: FioFS, C: Comparer> Silo<F, C> {
    pub(crate) async fn init(id: u16, fs: F, root_dir: impl Into<PathBuf>) -> TempestResult<Self> {
        info!("Initializing silo");
        let root_dir = root_dir.into();

        // initialize manifest
        let manifest = SiloManifest::init(fs, root_dir.clone()).await?;

        // initialize memtables
        let active = MemTable::new();
        let immutables = Vec::new();

        Ok(Self {
            id,
            root_dir,

            manifest,

            active,
            immutables,

            is_shutdown: false,
        })
    }

    async fn get_seqnum(&mut self) -> TempestResult<SeqNum> {
        let range = self.manifest.get_seqnums(1).await?;
        Ok(range.start)
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn write(&mut self, mut batch: WriteBatch) -> TempestResult<()> {
        trace!("Writing batch: {:?}", batch);
        let seqnum = self.get_seqnum().await?;
        batch.commit(seqnum);
        trace!(seqnum = seqnum.get(), "Batch stamped with seqnum");

        let mut body = batch.take_buf().freeze();
        let header = body.split_to(12);

        let seqnum_raw = u64::from_le_bytes(header[0..8].try_into().unwrap());
        assert_eq!(seqnum_raw, seqnum.get());

        let count = u32::from_le_bytes(header[8..12].try_into().unwrap());

        // TODO: verify remaining length along the way, to prevent panics if batch is malformed
        let mut pairs: Vec<(KeyKind, Bytes, Bytes)> = Vec::new();
        for idx in 0..count {
            trace!("Reading entry #{}", idx);

            // get kind
            let kind_byte = body.split_to(1)[0];
            let kind: KeyKind = kind_byte.try_into()?;

            // get key length varint
            let (key_len, varint_bytes_read) =
                read_varint(&body[..]).ok_or(TempestError::InvalidVarint)?;
            body.advance(varint_bytes_read);

            // get key
            let key = body.split_to(key_len);
            trace!(?kind, key_len, ?key, idx, "Got key");

            match kind {
                KeyKind::Delete => {
                    pairs.push((kind, key, Bytes::new()));
                }
                KeyKind::Put => {
                    // get value length varint
                    let (value_len, varint_bytes_read) =
                        read_varint(&body[..]).ok_or(TempestError::InvalidVarint)?;
                    body.advance(varint_bytes_read);

                    // get value
                    let value = body.split_to(value_len);
                    trace!(value_len, ?value, idx, "Got value");

                    pairs.push((kind, key, value));
                }
            }
        }

        for (kind, key, value) in pairs {
            let trailer = KeyTrailer::new(seqnum, kind);
            let key = InternalKey::new(key, trailer);
            self.active.insert(key, value);
        }

        // TODO: persist with WAL
        Ok(())
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn get(&self, key: Bytes, snapshot: SeqNum) -> TempestResult<Option<Bytes>> {
        if let Some(active_result) = self.active.get(key, snapshot) {
            return Ok(Some(active_result));
        }

        Ok(None)
    }

    pub(crate) const fn highest_seqnum(&self) -> SeqNum {
        // SAFETY:`manifest.seqnum_current()` returns a value between SeqNum::START..=SEQNUM::MAX.
        // This means, that subtracting `1` will at most end up at SeqNum::MIN (START-1)
        unsafe { SeqNum::new_unchecked(self.manifest.seqnum_current().get() - 1) }
    }

    pub async fn shutdown(&mut self) -> TempestResult<()> {
        assert!(!self.is_shutdown);

        // shutdown manifest, to free unused seqnums
        self.manifest.shutdown().await?;

        self.is_shutdown = true;
        Ok(())
    }
}

impl<F: FioFS, C: Comparer> Drop for Silo<F, C> {
    fn drop(&mut self) {
        assert!(
            self.is_shutdown,
            "Silo #{} was not shut down correctly!",
            self.id
        );
    }
}

#[cfg(test)]
mod tests {
    use bytes::BytesMut;
    use tracing::Level;

    use crate::{fio::VirtualFileSystem, tests::setup_tracing};

    use super::*;

    #[test]
    fn test_silo() {
        setup_tracing();
        if let Err(err) = tokio_uring::start(async {
            let id = 0;
            let silo_dir = "silo-0";
            let fs = VirtualFileSystem::new();

            let kvs = {
                let mut res = vec![
                    (b"key0".as_ref(), b"value0".as_ref()),
                    (b"key1".as_ref(), b"value1".as_ref()),
                    (b"key2".as_ref(), b"value2".as_ref()),
                    (b"key3".as_ref(), b"value3".as_ref()),
                    (b"key4".as_ref(), b"value4".as_ref()),
                    (b"key5".as_ref(), b"value5".as_ref()),
                ];
                res.sort_by_key(|&(k, _v)| k);
                res
            };

            // enter span
            let silo_span = span!(Level::INFO, "silo", id);
            let _enter = silo_span.enter();

            {
                // initialize silo
                let mut silo: Silo<_, DefaultComparer> =
                    Silo::init(id, fs.clone(), silo_dir).await?;

                // create batched insert
                let mut batch = WriteBatch::new_in(BytesMut::with_capacity(4096));
                for (k, v) in &kvs {
                    batch.put(k, v);
                }

                // write batch
                silo.write(batch).await?;

                // shut down silo
                silo.shutdown().await?;
                info!("First silo after shutdown: {:#?}", silo);
            }

            {
                // initialize silo
                let mut silo: Silo<_, DefaultComparer> =
                    Silo::init(id, fs.clone(), silo_dir).await?;

                // create batched insert
                let mut batch = WriteBatch::new_in(BytesMut::with_capacity(4096));

                // delete every second kv pair
                for (i, &(k, _v)) in kvs.iter().enumerate() {
                    if i % 2 == 0 {
                        batch.delete(k);
                    };
                }

                // write batch
                silo.write(batch).await?;

                // check that delete was successful
                for (i, &(k, _v)) in kvs.iter().enumerate() {
                    if i % 2 == 0 {
                        // TODO: use silo interface instead of accessing memtable
                        let found_value = silo.get(k.into(), silo.highest_seqnum()).await?;
                        assert!(found_value.is_none());
                    }
                }

                // shut down silo
                silo.shutdown().await?;
                info!("Second silo after shutdown: {:#?}", silo);
            }

            Ok::<(), TempestError>(())
        }) {
            error!("Silo test failed: {}", err);
            panic!("{}", err);
        }
    }
}
