use bytes::Bytes;
use tracing::Level;

use crate::{fio::VirtualFileSystem, silo::config::SiloConfig, tests::setup_tracing};

use super::*;

#[test]
fn test_header_encode_decode() {
    let filenum = 42;
    let header = SiloManifestHeader::new(filenum);
    let encoded = header.encode();
    assert_eq!(encoded.len(), SILO_MANIFEST_HEADER_SIZE);
    let decoded = SiloManifestHeader::decode(&encoded).unwrap();
    assert_eq!(decoded.filenum, filenum);
}

#[test]
fn test_record_prefix_encode_decode() {
    let data = b"some-garbage-data".as_ref();
    let record = SiloManifestRecordPrefix::new(data);
    let encoded = record.encode();
    assert_eq!(encoded.len(), SILO_MANIFEST_RECORD_PREFIX_SIZE);
    let decoded = SiloManifestRecordPrefix::decode(&encoded);
    assert!(decoded.is_valid_record(data));
}

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
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
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
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
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

        Ok::<(), TempestError>(())
    })
    .unwrap();
}

#[test]
fn test_wal_filenum_tracking_persists_across_restart() {
    setup_tracing();
    tokio_uring::start(async {
        let fs = VirtualFileSystem::new();
        let silo_root = PathBuf::from("silo-wal-track");
        let config = SiloConfig::for_testing().manifest;

        let wal_filenums = vec![10u64, 11, 12];

        {
            let mut manifest =
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            manifest
                .handle_request(
                    ManifestRequest::new().with_wal_filenums_added(wal_filenums.clone()),
                )
                .await?;
            assert_eq!(manifest.wal_filenums(), &wal_filenums);
            manifest.shutdown().await?;
        }

        {
            let mut manifest =
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            assert_eq!(
                manifest.wal_filenums(),
                &wal_filenums,
                "wal filenums should survive restart"
            );
            manifest.shutdown().await?;
        }

        Ok::<(), TempestError>(())
    })
    .unwrap();
}

#[test]
fn test_wal_filenum_removal_persists_across_restart() {
    setup_tracing();
    tokio_uring::start(async {
        let fs = VirtualFileSystem::new();
        let silo_root = PathBuf::from("silo-wal-remove");
        let config = SiloConfig::for_testing().manifest;

        {
            let mut manifest =
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            // register three WAL files
            manifest
                .handle_request(ManifestRequest::new().with_wal_filenums_added([10u64, 11, 12]))
                .await?;
            // remove the first two (simulating a flush that covered them)
            manifest
                .handle_request(ManifestRequest::new().with_wal_filenums_removed([10u64, 11]))
                .await?;
            assert_eq!(manifest.wal_filenums(), &[12u64]);
            manifest.shutdown().await?;
        }

        {
            let mut manifest =
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            assert_eq!(
                manifest.wal_filenums(),
                &[12u64],
                "only filenum 12 should remain after restart"
            );
            manifest.shutdown().await?;
        }

        Ok::<(), TempestError>(())
    })
    .unwrap();
}

#[test]
fn test_manifest_rotation_preserves_wal_filenums() {
    // Verifies that write_to_new_file snapshots wal_filenums correctly
    setup_tracing();
    tokio_uring::start(async {
        let fs = VirtualFileSystem::new();
        let silo_root = PathBuf::from("silo-wal-rotate");
        // tiny baseline so rotation triggers almost immediately
        let config = ManifestConfig {
            growth_baseline: 0,
            growth_factor: 1,
            ..SiloConfig::for_testing().manifest
        };

        let wal_filenums = vec![42u64, 43];

        {
            let mut manifest =
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            manifest
                .handle_request(
                    ManifestRequest::new().with_wal_filenums_added(wal_filenums.clone()),
                )
                .await?;

            // spam enough writes to trigger rotation
            for _ in 0..20 {
                manifest
                    .handle_request(ManifestRequest::new().with_seqnums_needed(1))
                    .await?;
            }
            manifest.shutdown().await?;
        }

        {
            let mut manifest =
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;
            assert_eq!(
                manifest.wal_filenums(),
                &wal_filenums,
                "wal filenums must survive manifest file rotation"
            );
            manifest.shutdown().await?;
        }

        Ok::<(), TempestError>(())
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
                SiloManifest::init(fs.clone(), silo_root.clone(), config.clone()).await?;

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
            let mut manifest = SiloManifest::init(fs.clone(), silo_root.clone(), config).await?;
            assert_eq!(manifest.ssts().len(), 1, "sst must persist");
            assert!(
                manifest.wal_filenums().is_empty(),
                "wal filenum must be gone after flush"
            );
            manifest.shutdown().await?;
        }

        Ok::<(), TempestError>(())
    })
    .unwrap();
}
