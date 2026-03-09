use bytes::Bytes;
use tempest_core::{fio::VirtualFileSystem, test_utils::setup_tracing};
use tracing::Level;

use crate::config::SiloConfig;

use super::*;

#[test]
fn test_manifest() {
    setup_tracing();
    tokio_uring::start(async {
        let silo_span = span!(Level::INFO, "silo", id = 0);
        let _enter = silo_span.enter();

        let fs = VirtualFileSystem::new();
        let silo_root = PathBuf::from("silo-0");

        let first_seqnum_range;
        let second_seqnum_range;

        let config = SiloConfig::for_testing().manifest;

        {
            let mut manifest =
                StorageManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            let seqnums_needed = 10;
            let response = manifest
                .handle_request(ManifestRequest::default().with_seqnums_needed(seqnums_needed))
                .await?;
            first_seqnum_range = response.seqnum_range;
            manifest.shutdown().await?;
            info!("first manifest final state: {:#?}", manifest);
            let range_size = first_seqnum_range.end.get() - first_seqnum_range.start.get();
            assert_eq!(
                range_size, seqnums_needed,
                "requested {} seqnums, but got {}",
                seqnums_needed, range_size,
            );
        }

        {
            let mut manifest =
                StorageManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            // simulate big seqnum request (about 1.5x the limit step)
            let seqnums_needed = config.seqnum_limit_step * 3 / 2 + 10;
            let resp = manifest
                .handle_request(ManifestRequest::default().with_seqnums_needed(seqnums_needed))
                .await?;
            second_seqnum_range = resp.seqnum_range;
            manifest.shutdown().await?;
            info!("second manifest final state: {:#?}", manifest);
            let range_size = second_seqnum_range.end.get() - second_seqnum_range.start.get();
            assert_eq!(
                range_size, seqnums_needed,
                "requested {} seqnums, but got {}",
                seqnums_needed, range_size,
            );
        }

        assert_eq!(
            first_seqnum_range.end, second_seqnum_range.start,
            "seqnum ranges should be continuous, got {:?} and {:?}",
            first_seqnum_range, second_seqnum_range,
        );

        Ok::<(), StorageError>(())
    })
    .unwrap();
}

#[test]
fn test_sst_and_wal_in_same_edit() {
    // Simulates what flush_oldest_immutable will do: atomically register an SST
    // and remove the WAL files it covers in a single manifest edit.
    setup_tracing();
    tokio_uring::start(async {
        let fs = VirtualFileSystem::new();
        let silo_root = PathBuf::from("silo-atomic-flush");
        let config = SiloConfig::for_testing().manifest;

        {
            let mut manifest =
                StorageManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;

            // pre-register a WAL file
            manifest
                .handle_request(ManifestRequest::new().with_wal_filenums_added([5u64]))
                .await?;

            // atomic flush edit: new SST in, WAL file out
            let sst = SstMetadata {
                filenum: 100,
                file_size: 1024,
                level: 0,
                min_key: Bytes::from("a"),
                max_key: Bytes::from("z"),
                min_seqnum: SeqNum::START,
                max_seqnum: SeqNum::START,
            };
            manifest
                .handle_request(
                    ManifestRequest::new()
                        .with_ssts_added([sst])
                        .with_wal_filenums_removed([5u64]),
                )
                .await?;

            assert_eq!(manifest.ssts().len(), 1);
            assert!(manifest.wal_filenums().is_empty());
            manifest.shutdown().await?;
        }

        {
            let mut manifest = StorageManifest::init(fs.clone(), silo_root.clone(), config).await?;
            assert_eq!(manifest.ssts().len(), 1, "sst must persist");
            assert!(
                manifest.wal_filenums().is_empty(),
                "wal filenum must be gone after flush"
            );
            manifest.shutdown().await?;
        }

        Ok::<(), StorageError>(())
    })
    .unwrap();
}
