use tempest_core::fio::FioFS;

use crate::{
    Storage,
    base::{Comparer, StorageResult},
    iterator::{DeduplicatingIterator, MergingIterator, MergingIteratorHeapEntry},
    manifest::{ManifestRequest, SstDeletion, SstMetadata},
    sst::{get_sst_path, reader::SstReader, writer::SstWriter},
};

impl<F: FioFS, C: Comparer> Storage<F, C> {
    #[instrument(skip_all, level = "debug")]
    pub(crate) async fn maybe_compact(&mut self) -> StorageResult<()> {
        if self.manifest.ssts().len() >= self.config.compaction.l0_file_threshold {
            debug!("compaction triggered");
            self.compact_l0().await?;
        }
        Ok(())
    }

    #[instrument(skip_all, level = "debug")]
    async fn compact_l0(&mut self) -> StorageResult<()> {
        // -- source the currently existing (l0) ssts --
        // TODO: overestimation of the entries is fine for now, but bloats the bloom filter a bit
        let entry_count: u64 = self
            .manifest
            .ssts()
            .iter()
            .map(|sst| sst.stats.entry_count)
            .sum();
        let num_ssts = self.manifest.ssts().len();
        let mut ssts_to_remove = Vec::with_capacity(num_ssts);
        let mut sources = Vec::with_capacity(num_ssts);
        for sst in self.manifest.ssts() {
            // open file
            let sst_path = get_sst_path(&self.root_dir, sst.filenum);
            let file = self.fs.opts().read(true).open(sst_path).await?;
            let reader = SstReader::<_, C>::open(file).await?;
            sources.push(MergingIteratorHeapEntry::new(reader.iter(), sst.filenum));

            ssts_to_remove.push(sst.filenum);
        }
        let compaction_sources = DeduplicatingIterator::new(MergingIterator::new(sources));

        // open new writer
        let filenum = self.manifest.get_filenums(1).await?.start;
        let sst_path = get_sst_path(&self.root_dir, filenum);
        let file = self
            .fs
            .opts()
            .write(true)
            .create(true)
            .truncate(true)
            .open(sst_path)
            .await?;
        let mut writer =
            SstWriter::<_, C>::new(file, entry_count as usize, self.config.sst.clone());

        // write all the old sst entries
        writer.extend_from_stream(compaction_sources).await?;
        let stats = writer.finalize().await?;

        let sst_metadata = SstMetadata {
            filenum,
            level: 0,
            stats,
        };

        let orphans = ssts_to_remove
            .iter()
            .map(|filenum| get_sst_path(&self.root_dir, *filenum))
            .collect();

        // write down that there is a new sst and the other ssts are no longer valid
        self.manifest
            .handle_request(
                ManifestRequest::new()
                    .with_ssts_added([sst_metadata])
                    .with_ssts_removed(ssts_to_remove.into_iter().map(SstDeletion::new)),
            )
            .await?;

        // remove the old ssts
        self.spawn_file_gc(orphans);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use bytes::Bytes;
    use tempest_core::{fio::VirtualFileSystem, test_utils::setup_tracing};

    use crate::{
        Storage, StorageConfig, WriteBatch,
        base::{DefaultComparer, StorageError},
        config::{CompactionConfig, MemTableConfig},
    };

    /// A config that triggers flushes and compaction aggressively for testing.
    /// - memtable flushes after ~2 small entries
    /// - compaction triggers after 2 SSTs
    fn compaction_test_config() -> StorageConfig {
        StorageConfig {
            memtable: MemTableConfig {
                size_threshold: 64,
                max_immutable_count: 2,
            },
            compaction: CompactionConfig {
                l0_file_threshold: 2,
            },
            ..Default::default()
        }
    }

    fn put(key: &str, value: &str) -> WriteBatch {
        let mut batch = WriteBatch::new();
        batch.put(key.as_bytes(), value.as_bytes());
        batch
    }

    fn delete(key: &str) -> WriteBatch {
        let mut batch = WriteBatch::new();
        batch.delete(key.as_bytes());
        batch
    }

    /// Write enough batches to guarantee at least `n` SST flushes have occurred.
    async fn force_flushes(
        storage: &mut Storage<VirtualFileSystem, DefaultComparer>,
        n: usize,
    ) -> Result<(), StorageError> {
        // Each write is ~64 bytes which exceeds the 64B memtable threshold,
        // guaranteeing a flush per write.
        for i in 0..n {
            let mut batch = WriteBatch::new();
            let key = format!("flush-trigger:{:04}", i);
            let value = format!("value:{:04}", i);
            batch.put(key.as_bytes(), value.as_bytes());
            storage.write(batch).await?;
        }
        Ok(())
    }

    // -- correctness --

    #[test]
    fn test_compaction_preserves_data() {
        setup_tracing();
        let fs = VirtualFileSystem::new();
        let config = compaction_test_config();

        tokio_uring::start(async {
            let kvs: Vec<(&str, &str)> = vec![
                ("alpha", "1"),
                ("beta", "2"),
                ("gamma", "3"),
                ("delta", "4"),
                ("epsilon", "5"),
            ];

            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await
                        .unwrap();

                for &(k, v) in &kvs {
                    storage.write(put(k, v)).await.unwrap();
                }

                // force enough flushes to trigger compaction
                force_flushes(&mut storage, 4).await.unwrap();

                storage.shutdown().await.unwrap();
            }

            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await
                        .unwrap();
                let snapshot = storage.highest_seqnum();

                for &(k, v) in &kvs {
                    let found = storage.get(&Bytes::from(k), snapshot).await.unwrap();
                    assert_eq!(
                        found.as_deref(),
                        Some(v.as_bytes()),
                        "key '{}' should be '{}' after compaction",
                        k,
                        v
                    );
                }

                storage.shutdown().await.unwrap();
            }
        });
    }

    // -- deduplication --

    #[test]
    fn test_compaction_deduplicates_versions() {
        setup_tracing();
        let fs = VirtualFileSystem::new();
        let config = compaction_test_config();

        tokio_uring::start(async {
            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await?;

                // write v1 and flush it to an SST
                storage.write(put("key", "v1")).await?;
                force_flushes(&mut storage, 2).await?;

                // write v2 and flush it to another SST - triggers compaction
                storage.write(put("key", "v2")).await?;
                force_flushes(&mut storage, 2).await?;

                let snapshot = storage.highest_seqnum();
                let found = storage.get(&Bytes::from("key"), snapshot).await?;
                assert_eq!(
                    found.as_deref(),
                    Some(b"v2".as_ref()),
                    "newest version must win after compaction"
                );

                // verify we compacted down to 1 SST
                assert_eq!(
                    storage.manifest.ssts().len(),
                    1,
                    "should have exactly 1 SST after full L0 compaction"
                );

                storage.shutdown().await?;
            }

            Ok::<_, StorageError>(())
        })
        .unwrap();
    }

    // -- tombstone preservation --

    #[test]
    fn test_compaction_preserves_tombstones() {
        setup_tracing();
        let fs = VirtualFileSystem::new();
        let config = compaction_test_config();

        tokio_uring::start(async {
            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await?;

                // write the key and flush it
                storage.write(put("doomed", "value")).await?;
                force_flushes(&mut storage, 2).await?;

                // delete the key and flush it - triggers compaction
                storage.write(delete("doomed")).await?;
                force_flushes(&mut storage, 2).await?;

                let snapshot = storage.highest_seqnum();
                let found = storage.get(&Bytes::from("doomed"), snapshot).await?;
                assert!(
                    found.is_none(),
                    "deleted key must remain absent after compaction"
                );

                storage.shutdown().await?;
            }

            Ok::<_, StorageError>(())
        })
        .unwrap();
    }

    // -- sst count reduction --

    #[test]
    fn test_compaction_reduces_sst_count() {
        setup_tracing();
        let fs = VirtualFileSystem::new();
        let config = compaction_test_config();
        let threshold = config.compaction.l0_file_threshold;

        tokio_uring::start(async {
            let mut storage =
                Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone()).await?;

            // force enough flushes to exceed the threshold
            force_flushes(&mut storage, threshold + 2).await?;

            assert_eq!(
                storage.manifest.ssts().len(),
                1,
                "SST count must be 1 after compaction (was above threshold {})",
                threshold
            );

            storage.shutdown().await?;
            Ok::<_, StorageError>(())
        })
        .unwrap();
    }

    // -- recovery after compaction --

    #[test]
    fn test_compaction_survives_restart() {
        setup_tracing();
        let fs = VirtualFileSystem::new();
        let config = compaction_test_config();

        tokio_uring::start(async {
            let kvs: Vec<(&str, &str)> = vec![("x", "1"), ("y", "2"), ("z", "3")];

            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await?;

                for &(k, v) in &kvs {
                    storage.write(put(k, v)).await?;
                }

                // trigger compaction
                force_flushes(&mut storage, 4).await?;

                assert_eq!(
                    storage.manifest.ssts().len(),
                    1,
                    "should have compacted before shutdown"
                );

                storage.shutdown().await?;
            }

            // reopen and verify compacted state is intact
            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await?;
                let snapshot = storage.highest_seqnum();

                assert_eq!(
                    storage.manifest.ssts().len(),
                    1,
                    "compacted SST count must survive restart"
                );

                for &(k, v) in &kvs {
                    let found = storage.get(&Bytes::from(k), snapshot).await?;
                    assert_eq!(
                        found.as_deref(),
                        Some(v.as_bytes()),
                        "key '{}' must survive compaction + restart",
                        k
                    );
                }

                storage.shutdown().await?;
            }

            Ok::<_, StorageError>(())
        })
        .unwrap();
    }

    // -- interleaved versions across ssts --

    #[test]
    fn test_compaction_interleaved_versions_across_ssts() {
        // regression guard: keys from different SSTs that interleave in sort order
        // must be merged and deduplicated correctly
        setup_tracing();
        let fs = VirtualFileSystem::new();
        let config = compaction_test_config();

        tokio_uring::start(async {
            {
                let mut storage =
                    Storage::<_, DefaultComparer>::init(0, fs.clone(), "/data", config.clone())
                        .await?;

                // SST 1: a=1, c=1
                let mut batch = WriteBatch::new();
                batch.put(b"a", b"1");
                batch.put(b"c", b"1");
                storage.write(batch).await?;
                force_flushes(&mut storage, 2).await?;

                // SST 2: a=2, b=1 - triggers compaction
                let mut batch = WriteBatch::new();
                batch.put(b"a", b"2");
                batch.put(b"b", b"1");
                storage.write(batch).await?;
                force_flushes(&mut storage, 2).await?;

                let snapshot = storage.highest_seqnum();

                // a must be v2 (newest), b and c must exist
                assert_eq!(
                    storage.get(&Bytes::from("a"), snapshot).await?.as_deref(),
                    Some(b"2".as_ref()),
                    "a must be newest version"
                );
                assert_eq!(
                    storage.get(&Bytes::from("b"), snapshot).await?.as_deref(),
                    Some(b"1".as_ref()),
                    "b must exist"
                );
                assert_eq!(
                    storage.get(&Bytes::from("c"), snapshot).await?.as_deref(),
                    Some(b"1".as_ref()),
                    "c must exist"
                );

                storage.shutdown().await?;
            }

            Ok::<_, StorageError>(())
        })
        .unwrap();
    }
}
