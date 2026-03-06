use tempest_core::{fio::VirtualFileSystem, test_utils::setup_tracing};
use tracing::{Instrument, Level};

use crate::iterator::StorageIterator;

use super::*;

use crate::base::SeqNum;

pub(crate) fn filenum_gen() -> impl FnMut() -> u64 {
    let mut filenum_range = 0..;
    move || filenum_range.next().unwrap()
}

#[test]
fn test_filenum_gen() {
    let mut fgen = filenum_gen();
    let mut old = fgen();
    for _ in 0..100 {
        let new = fgen();
        assert!(new > old);
        old = new;
    }
}

pub(crate) fn seqnum_gen() -> impl FnMut() -> SeqNum {
    let mut next_seqnum = SeqNum::START;
    move || {
        let seqnum = next_seqnum;
        next_seqnum = (seqnum.get() + 1).try_into().unwrap();
        seqnum
    }
}

#[test]
fn test_seqnum_gen() {
    let mut sgen = seqnum_gen();
    let mut old = sgen();
    for _ in 0..100 {
        let new = sgen();
        assert!(new > old);
        old = new;
    }
}

#[test]
fn test_silo_basic() {
    setup_tracing();

    let id = 0;
    let silo_span = span!(Level::INFO, "silo", id);
    let silo_dir = "silo-0";
    let fs = VirtualFileSystem::new();
    let config = SiloConfig::for_testing();
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
                    Silo::init(id, fs.clone(), silo_dir, config.clone()).await?;

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
                    Silo::init(id, fs.clone(), silo_dir, config.clone()).await?;

                // verify that all values were persisted
                for &(k, v) in &kvs {
                    let found = silo.get(&k.into(), silo.highest_seqnum()).await?;
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
                        let found_value = silo.get(&k.into(), silo.highest_seqnum()).await?;
                        assert!(found_value.is_none());
                    }
                }

                // shut down silo
                silo.shutdown().await?;
                info!("second silo after shutdown: {:#?}", silo);
            }

            Ok::<(), StorageError>(())
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
    let config = SiloConfig::for_testing();
    tokio_uring::start(
        async {
            info!("starting first silo");
            {
                let mut silo: Silo<_> =
                    Silo::init(id, fs.clone(), silo_dir, config.clone()).await?;

                // 1. Write initial data and move to immutables
                let mut batch1 = WriteBatch::new();
                batch1.put(b"key_a", b"value_old");
                silo.write(batch1).await?;

                // Force a flush
                silo.test_force_freeze();

                // 2. Write an update to "key_a" and a new "key_b"
                let mut batch2 = WriteBatch::new();
                batch2.put(b"key_a", b"value_new");
                batch2.put(b"key_b", b"value_b");
                silo.write(batch2).await?;

                // Force a flush
                silo.test_force_freeze();

                // 3. Delete "key_b" in the currently active memtable
                let mut batch3 = WriteBatch::new();
                batch3.delete(b"key_b");
                silo.write(batch3).await?;

                // --- Perform the Scan using the Beautiful Interface ---
                let mut scanner = silo.scan().await?;
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

            info!("starting second silo");
            {
                // re-open and verify the same scan results hold after recovery
                let mut silo: Silo<_> =
                    Silo::init(id, fs.clone(), silo_dir, config.clone()).await?;

                let mut scanner = silo.scan().await?;
                let mut results = Vec::new();
                while let Some(()) = scanner.next().await? {
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

            Ok::<_, StorageError>(())
        }
        .instrument(silo_span),
    )
    .unwrap();

    fs.debug();
}

#[test]
fn test_silo_load() {
    setup_tracing();

    let id = 1;
    let silo_dir = "silo-load-test";
    let fs = VirtualFileSystem::new();

    let silo_span = span!(Level::INFO, "silo", id);
    let config = SiloConfig::for_testing();
    tokio_uring::start(
        async {
            let mut restart_counter = 0;
            let mut override_counter = 0;

            // every write is at least 2 bytes, resulting in a flush (thresh * 1/2)
            let batch_count = config.memtable.size_threshold / 2;
            let override_wrap = batch_count / 8;
            let restart_interval = batch_count / 16;
            let mut silo =
                Silo::<_, DefaultComparer>::init(id, fs.clone(), silo_dir, config.clone()).await?;
            for i in 0..batch_count {
                info!(i, "writing new batch");
                let is_first_or_last = i == 0 || i == batch_count;

                let mut batch = WriteBatch::new();
                let key_a = format!("keyA:{}", i % override_wrap);
                let value_a = format!("valueA:{}", i);
                batch.put(key_a.as_ref(), value_a.as_ref());

                let key_b = format!("keyB:{}", i % override_wrap);
                let value_b = format!("valueB:{}", i);
                batch.put(key_b.as_ref(), value_b.as_ref());

                if i % override_wrap == 0 && !is_first_or_last {
                    override_counter += 1;
                    batch.delete(key_a.as_ref());
                }

                silo.write(batch).await?;

                if i % restart_interval == 0 && !is_first_or_last {
                    restart_counter += 1;
                    silo.shutdown().await?;
                    silo =
                        Silo::<_, DefaultComparer>::init(id, fs.clone(), silo_dir, config.clone())
                            .await?;
                }
                if i % override_wrap == 0 {
                    info!("progress {:.2}%", (i as f64 / batch_count as f64) * 100.0)
                }
            }
            silo.shutdown().await?;
            info!(restart_counter, override_counter, "finished write loop");

            // reopen and verify final state
            let mut silo =
                Silo::<_, DefaultComparer>::init(id, fs.clone(), silo_dir, config.clone()).await?;
            let snapshot = silo.highest_seqnum();

            for i in 0..batch_count {
                let key_b = format!("keyB:{}", i % override_wrap);
                let found = silo.get(&Bytes::from(key_b), snapshot).await?;
                assert!(found.is_some(), "keyB:{} should exist", i % override_wrap);

                // keyA:0 gets deleted when i % override_wrap == 0 (and i != 0)
                // since batch_count < override_wrap, only keyA:0 at i=0 was written, never deleted
                // so all keyA entries should exist too in this test size
                let key_a = format!("keyA:{}", i % override_wrap);
                let found_a = silo.get(&Bytes::from(key_a), snapshot).await?;
                assert!(found_a.is_some(), "keyA:{} should exist", i % override_wrap);
            }
            silo.shutdown().await?;

            Ok::<_, StorageError>(())
        }
        .instrument(silo_span),
    )
    .unwrap();
}

#[test]
fn test_recovery_seqnum_visibility() {
    // Regression test: after recovery, entries replayed from WAL must be visible
    // via highest_seqnum(). The bug was that highest_seqnum() returned the
    // manifest's persisted seqnum_current, which was lower than the seqnums
    // of WAL-replayed entries, causing them to be shadowed.
    setup_tracing();
    let id = 2;
    let silo_dir = "silo-seqnum-visibility";
    let fs = VirtualFileSystem::new();
    let silo_span = span!(Level::INFO, "silo", id);
    let mut config = SiloConfig::for_testing();
    config.memtable.size_threshold = 64;

    tokio_uring::start(
        async {
            // -- Phase 1: write enough to trigger at least one flush --
            {
                let mut silo =
                    Silo::<_, DefaultComparer>::init(id, fs.clone(), silo_dir, config.clone())
                        .await?;

                // force a flush by exceeding the memtable threshold
                let flush_batch_count = config.memtable.size_threshold;
                for i in 0..flush_batch_count {
                    let mut batch = WriteBatch::new();
                    batch.put(format!("f:{}", i).as_ref(), b"v");
                    silo.write(batch).await?;
                }

                // -- Phase 2: write a few more entries that stay in WAL only --
                // these are the ones that must survive recovery and be visible
                let unflushed_keys = ["after:0", "after:1", "after:2"];
                for key in &unflushed_keys {
                    let mut batch = WriteBatch::new();
                    batch.put(key.as_ref(), b"present");
                    silo.write(batch).await?;
                }

                silo.shutdown().await?;
            }

            // -- Phase 3: reopen and verify the unflushed entries are visible --
            {
                let mut silo =
                    Silo::<_, DefaultComparer>::init(id, fs.clone(), silo_dir, config.clone())
                        .await?;
                println!("{:#?}", silo);

                // This snapshot must be high enough to include the WAL-recovered entries.
                // Before the fix, highest_seqnum() returned the pre-recovery manifest value,
                // which was below the seqnums assigned to after:0/1/2.
                let snapshot = silo.highest_seqnum();

                for key in &["after:0", "after:1", "after:2"] {
                    let found = silo.get(&Bytes::from(key.to_string()), snapshot).await?;
                    assert!(
                        found.is_some(),
                        "key '{}' was written before shutdown but invisible after recovery \
                         (highest_seqnum={:?}) - seqnum not advanced past WAL replay",
                        key,
                        snapshot,
                    );
                }

                silo.shutdown().await?;
            }

            Ok::<_, StorageError>(())
        }
        .instrument(silo_span),
    )
    .unwrap();
}
