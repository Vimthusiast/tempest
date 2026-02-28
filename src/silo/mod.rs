//! # Silo Module
//!
//! This module contains the code for our **storage silos**.
//!
//! ## What are silos
//!
//! Tempest is designed with the shared-nothing approach, where we try to avoid having any
//! resources requiring multi-thread synchronization primitives. This improves overall
//! **performance** and allows us to utilize certain Linux kernel features, such as **io_uring**,
//! which is bound to be used on one thread by implementation, i.e. most types are !Send.

use std::{path::PathBuf, sync::Arc, thread};

use crate::{
    base::{
        Comparer, DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum, TempestError,
        TempestResult,
    },
    fio::FioFS,
    silo::{
        batch::WriteBatch,
        iterator::{DeduplicatingIterator, MergingIterator, MergingIteratorHeapEntry},
        manifest::SiloManifest,
        memtable::MemTable,
        wal::{SiloWal, WalStatus},
    },
};

use bytes::{Buf, Bytes};
use integer_encoding::VarInt;
use tokio::sync::{mpsc, oneshot};
use tracing::{Level, instrument};

pub mod batch;
pub mod iterator;
pub mod manifest;
pub mod memtable;
pub mod sst;
pub mod wal;

#[derive(Debug)]
pub(crate) struct Silo<F: FioFS, C: Comparer = DefaultComparer> {
    /// The ID of this silo.
    id: u64,
    /// The root directory for this silo.
    root_dir: PathBuf,

    /// The manifest that manages state of this silo.
    manifest: SiloManifest<F>,

    /// The write-ahead log that ensure durability of writes to this silo.
    wal: SiloWal<F>,

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
    pub(crate) async fn init(id: u64, fs: F, root_dir: impl Into<PathBuf>) -> TempestResult<Self> {
        info!("initializing silo");
        let root_dir = root_dir.into();

        // initialize manifest
        let mut manifest = SiloManifest::init(fs.clone(), root_dir.clone()).await?;

        // allocate filenums for other components
        let filenum_range = manifest.get_filenums(1).await?;
        let mut filenums = filenum_range.into_iter();

        // initialize wal
        let (wal, mut recovery_reader) =
            SiloWal::init(fs, root_dir.clone(), filenums.next().unwrap()).await?;

        // initialize memtables
        let active = MemTable::new();
        let immutables = Vec::new();

        let mut silo = Self {
            id,
            root_dir,

            // -- manager components --
            manifest,
            wal,

            active,
            immutables,

            is_shutdown: false,
        };

        while let Some(res) = recovery_reader.next().await {
            // skip over errors
            let data = match res {
                Ok(d) => d,
                Err(e) => {
                    warn!("could not recover record from wal: {}, skipping", e);
                    continue;
                }
            };
            if let Err(e) = silo.apply_batch_to_memtable(data.freeze()) {
                warn!("failed to apply batch to memtable: {}, skipping", e);
            }
        }

        info!("finished initializing silo");
        Ok(silo)
    }

    async fn get_seqnum(&mut self) -> TempestResult<SeqNum> {
        let range = self.manifest.get_seqnums(1).await?;
        Ok(range.start)
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn write(&mut self, mut batch: WriteBatch) -> TempestResult<()> {
        trace!("writing batch: {:?}", batch);
        let seqnum = self.get_seqnum().await?;
        batch.commit(seqnum);
        trace!(?seqnum, "batch stamped with seqnum");

        let body = batch.take_buf().freeze();

        // -- persist in wal --
        trace!("persisting batch in wal");
        let flush_required = self.wal.append(body.clone()).await?;
        let wal_status = self.wal.flush(flush_required).await?;

        // -- commit to memtable --
        // TODO: unwrap here? check validity first? maybe this is fine
        self.apply_batch_to_memtable(body)?;

        // TODO: Implement wal rotation
        //
        //match wal_status {
        //    WalStatus::Ok => {},
        //    WalStatus::NeedsRotation => self.wal.rotate(),
        //}

        Ok(())
    }

    fn apply_batch_to_memtable(&mut self, mut body: Bytes) -> TempestResult<()> {
        let header = body.split_to(12);

        let seqnum_raw = u64::from_le_bytes(header[0..8].try_into().unwrap());
        let seqnum = seqnum_raw.try_into()?;

        let count = u32::from_le_bytes(header[8..12].try_into().unwrap());

        // TODO: verify remaining length along the way, to prevent panics if batch is malformed
        let mut pairs: Vec<(KeyKind, Bytes, Bytes)> = Vec::new();
        for idx in 0..count {
            trace!(idx, "reading entry");

            // get kind
            let kind_byte = body.split_to(1)[0];
            let kind: KeyKind = kind_byte.try_into()?;

            // get key length varint
            let (key_len, varint_bytes_read) =
                read_varint(&body[..]).ok_or(TempestError::InvalidVarint)?;
            body.advance(varint_bytes_read);

            // get key
            let key = body.split_to(key_len);
            trace!(?kind, key_len, ?key, idx, "got key");

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
                    trace!(value_len, ?value, idx, "got value");

                    pairs.push((kind, key, value));
                }
            }
        }

        for (kind, key, value) in pairs {
            let trailer = KeyTrailer::new(seqnum, kind);
            let key = InternalKey::new(key, trailer);
            self.active.insert(key, value);
        }

        Ok(())
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn get(&self, key: Bytes, snapshot: SeqNum) -> TempestResult<Option<Bytes>> {
        if let Some(active_result) = self.active.get(&key, snapshot) {
            return Ok(Some(active_result));
        }

        for imm in &self.immutables {
            if let Some(imm_result) = imm.get(&key, snapshot) {
                return Ok(Some(imm_result));
            }
        }

        Ok(None)
    }

    #[instrument(skip_all, level = "debug")]
    pub(crate) fn scan(&self) -> DeduplicatingIterator<'_, MergingIterator<'_, C>, C> {
        let mut sources = Vec::new();
        sources.push(MergingIteratorHeapEntry::new(self.active.iter(), u64::MAX));

        for (idx, imm) in self.immutables.iter().enumerate() {
            sources.push(MergingIteratorHeapEntry::new(
                imm.iter(),
                u64::MAX - (idx as u64 + 1),
            ));
        }

        DeduplicatingIterator::new(MergingIterator::new(sources))
    }

    pub(crate) const fn highest_seqnum(&self) -> SeqNum {
        // SAFETY:`manifest.seqnum_current()` returns a value between SeqNum::START..=SEQNUM::MAX.
        // This means, that subtracting `1` will at most end up at SeqNum::MIN (START-1)
        unsafe { SeqNum::new_unchecked(self.manifest.seqnum_current().get() - 1) }
    }

    #[instrument(skip_all)]
    pub async fn shutdown(&mut self) -> TempestResult<()> {
        assert!(!self.is_shutdown);
        // NB: Set this to true, even if this function may return an error,
        // since we may shut down partially, which means we don't want to call shutdown again,
        // even though it did not complete the process
        self.is_shutdown = true;

        // shutdown manifest, to free unused seqnums
        self.manifest.shutdown().await?;
        info!("shut down manifest");

        Ok(())
    }
}

impl<F: FioFS, C: Comparer> Drop for Silo<F, C> {
    fn drop(&mut self) {
        if !self.is_shutdown {
            error!(id = self.id, "silo was not shut down correctly!");
        }
    }
}

pub struct SiloHandle {
    sender: mpsc::Sender<SiloCommand>,
}

impl SiloHandle {
    pub async fn write(&self, batch: WriteBatch) -> TempestResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(SiloCommand::Write {
                batch,
                respond_to: tx,
            })
            .await?;
        rx.await?
    }

    pub(crate) async fn shutdown(&self) -> TempestResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(SiloCommand::Shutdown { respond_to: tx })
            .await?;
        rx.await?
    }
}

#[derive(Debug)]
pub enum SiloCommand {
    Write {
        batch: WriteBatch,
        respond_to: oneshot::Sender<TempestResult<()>>,
    },
    Scan {},
    Shutdown {
        respond_to: oneshot::Sender<TempestResult<()>>,
    },
}

#[derive(Debug)]
pub enum CommandControlFlow {
    Continue,
    Shutdown {
        respond_to: oneshot::Sender<TempestResult<()>>,
    },
}

/// A background worker that can be controlled through channel commands and manages a [`Silo`].
pub struct SiloWorker<F: FioFS, C: Comparer> {
    silo: Silo<F, C>,
    receiver: mpsc::Receiver<SiloCommand>,
}

impl<F: FioFS, C: Comparer> SiloWorker<F, C> {
    /// Creates a silo worker that initializes and manages a [`Silo`] within the `root_dir`.
    pub fn spawn_worker(id: u64, fs: F, root_dir: impl Into<PathBuf>) -> SiloHandle {
        let root_dir = root_dir.into();
        let silo_dir = root_dir.join(format!("silo-{}", id));
        let (sender, receiver) = mpsc::channel(1024);

        thread::spawn(move || {
            let _worker_entered = span!(Level::INFO, "silo-worker", id).entered();
            info!(id, ?root_dir, "spawning silo worker");
            // Specify core affinity for this worker
            core_affinity::set_for_current(core_affinity::CoreId { id: id as usize });

            let result = tokio_uring::start(async move {
                info!(id, "initialized tokio-uring runtime");
                let silo = Silo::<F, C>::init(id, fs, silo_dir).await?;
                let mut worker = SiloWorker { silo, receiver };
                worker.start().await;

                Ok::<_, TempestError>(())
            });
            if let Err(err) = result {
                error!("silo worker crashed: {}", err);
            }
        });

        SiloHandle { sender }
    }

    async fn start(&mut self) {
        info!("starting silo worker");
        let respond_to = loop {
            let control_flow = match self.receiver.recv().await {
                Some(cmd) => match self.handle_command(cmd).await {
                    Ok(cf) => cf,
                    Err(err) => {
                        error!("could not handle command: {}", err);
                        break None;
                    }
                },
                None => {
                    info!("channel closed. exiting");
                    break None;
                }
            };

            match control_flow {
                CommandControlFlow::Continue => continue,
                CommandControlFlow::Shutdown { respond_to } => {
                    info!("shutdown has been requested");
                    break Some(respond_to);
                }
            }
        };

        let result = self.silo.shutdown().await;
        if let Some(tx) = respond_to {
            if let Err(_) = tx.send(result) {
                error!("could not send shutdown confirmation: channel closed");
            }
        } else {
            match result {
                Ok(()) => info!("successfully shut down."),
                Err(err) => error!("could not shut down correctly: {}", err),
            }
        }
    }

    #[instrument(skip_all)]
    async fn handle_command(&mut self, cmd: SiloCommand) -> TempestResult<CommandControlFlow> {
        match cmd {
            SiloCommand::Write { batch, respond_to } => {
                let result = self.silo.write(batch).await;
                if let Err(e) = result.as_ref() {
                    error!("failed to execute write command: {}", e);
                }
                if let Err(_) = respond_to.send(result) {
                    error!("could not respond to write command: channel closed");
                }
                Ok(CommandControlFlow::Continue)
            }
            SiloCommand::Scan {} => todo!(),
            SiloCommand::Shutdown { respond_to } => Ok(CommandControlFlow::Shutdown { respond_to }),
        }
    }
}

#[cfg(test)]
mod tests {
    use tracing::{Instrument, Level};

    use crate::{fio::VirtualFileSystem, silo::iterator::TempestIterator, tests::setup_tracing};

    use super::*;

    #[test]
    fn test_silo_basic() {
        setup_tracing();

        let id = 0;
        let silo_span = span!(Level::INFO, "silo", id);
        let silo_dir = "silo-0";
        let fs = VirtualFileSystem::new();
        if let Err(err) = tokio_uring::start(
            async {
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

                {
                    // initialize silo
                    let mut silo: Silo<_, DefaultComparer> =
                        Silo::init(id, fs.clone(), silo_dir).await?;

                    // create batched insert
                    let mut batch = WriteBatch::new();
                    for (k, v) in &kvs {
                        batch.put(k, v);
                    }

                    // write batch
                    silo.write(batch).await?;

                    // shut down silo
                    silo.shutdown().await?;
                    info!("first silo after shutdown: {:#?}", silo);
                }

                {
                    // initialize silo
                    let mut silo: Silo<_, DefaultComparer> =
                        Silo::init(id, fs.clone(), silo_dir).await?;

                    // verify that all values were persisted
                    for &(k, v) in &kvs {
                        let found = silo.get(k.into(), silo.highest_seqnum()).await?;
                        assert_eq!(
                            found.as_deref(),
                            Some(v),
                            "expected {:?} to be {:?} after restart",
                            k,
                            v
                        );
                    }

                    // create batched insert
                    let mut batch = WriteBatch::new();

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
                    info!("second silo after shutdown: {:#?}", silo);
                }

                Ok::<(), TempestError>(())
            }
            .instrument(silo_span),
        ) {
            error!("silo test failed: {}", err);
            panic!("{}", err);
        }
    }

    #[test]
    fn test_silo_scan_interleaving_and_deduplication() {
        setup_tracing();

        let id = 1;
        let silo_dir = "silo-scan-test";
        let fs = VirtualFileSystem::new();

        let silo_span = span!(Level::INFO, "silo", id);
        tokio_uring::start(
            async {
                {
                    let mut silo: Silo<_, DefaultComparer> =
                        Silo::init(id, fs.clone(), silo_dir).await.unwrap();

                    // 1. Write initial data and move to immutables
                    let mut batch1 = WriteBatch::new();
                    batch1.put(b"key_a", b"value_old");
                    silo.write(batch1).await.unwrap();

                    // Simulate flush freeze
                    let old_mem = std::mem::replace(&mut silo.active, MemTable::new());
                    silo.immutables.push(Arc::new(old_mem));

                    // 2. Write an update to "key_a" and a new "key_b"
                    let mut batch2 = WriteBatch::new();
                    batch2.put(b"key_a", b"value_new");
                    batch2.put(b"key_b", b"value_b");
                    silo.write(batch2).await.unwrap();

                    let mid_mem = std::mem::replace(&mut silo.active, MemTable::new());
                    silo.immutables.push(Arc::new(mid_mem));

                    // 3. Delete "key_b" in the currently active memtable
                    let mut batch3 = WriteBatch::new();
                    batch3.delete(b"key_b");
                    silo.write(batch3).await.unwrap();

                    // --- Perform the Scan using the Beautiful Interface ---
                    let mut scanner = silo.scan();
                    let mut results = Vec::new();

                    // Clean async loop - no more manual Context or Poll matching!
                    while let Ok(Some(())) = scanner.next().await {
                        let internal_key = scanner.key().unwrap();
                        results.push((
                            internal_key.key().clone(),
                            scanner.value().unwrap().clone(),
                            internal_key.trailer().kind(),
                        ));
                    }
                    drop(scanner);

                    // --- Assertions ---
                    assert_eq!(results.len(), 2, "should have 2 unique logical keys");

                    // key_a: versioned by seqnum, highest (newest) should win
                    assert_eq!(results[0].0, "key_a");
                    assert_eq!(results[0].1, "value_new");
                    assert_eq!(results[0].2, KeyKind::Put);

                    // key_b: delete marker should shadow the put
                    assert_eq!(results[1].0, "key_b");
                    assert_eq!(results[1].2, KeyKind::Delete);

                    silo.shutdown().await.unwrap();
                }

                {
                    // re-open and verify the same scan results hold after recovery
                    let mut silo: Silo<_, DefaultComparer> =
                        Silo::init(id, fs.clone(), silo_dir).await.unwrap();

                    let mut scanner = silo.scan();
                    let mut results = Vec::new();
                    while let Ok(Some(())) = scanner.next().await {
                        let internal_key = scanner.key().unwrap();
                        results.push((
                            internal_key.key().clone(),
                            scanner.value().unwrap().clone(),
                            internal_key.trailer().kind(),
                        ));
                    }
                    drop(scanner);

                    assert_eq!(
                        results.len(),
                        2,
                        "should have 2 unique logical keys after recovery"
                    );
                    assert_eq!(results[0].0, "key_a");
                    assert_eq!(results[0].1, "value_new");
                    assert_eq!(results[0].2, KeyKind::Put);
                    assert_eq!(results[1].0, "key_b");
                    assert_eq!(results[1].2, KeyKind::Delete);

                    silo.shutdown().await.unwrap();
                }
            }
            .instrument(silo_span),
        );
    }
}
