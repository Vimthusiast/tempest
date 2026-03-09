use bytes::Bytes;
use tempest_core::fio::VirtualFileSystem;

use crate::config::StorageConfig;

use super::*;

async fn make_manifest(config: ManifestConfig) -> StorageManifest<VirtualFileSystem> {
    let fs = VirtualFileSystem::new();
    let root = PathBuf::from("test-manifest");
    StorageManifest::init(fs, root, config).await.unwrap()
}

// -- seqnum range tests --

#[tokio::test]
async fn test_seqnum_range_basic() {
    let mut m = make_manifest(StorageConfig::for_testing().manifest).await;
    let start = m.seqnum_current();

    let range = m.get_seqnums(5).await.unwrap();

    assert_eq!(range.start, start);
    assert_eq!(range.end.get() - range.start.get(), 5);
    assert_eq!(m.seqnum_current(), range.end);

    m.shutdown().await.unwrap();
}

#[tokio::test]
async fn test_seqnum_ranges_are_contiguous() {
    let mut m = make_manifest(StorageConfig::for_testing().manifest).await;

    let r1 = m.get_seqnums(10).await.unwrap();
    let r2 = m.get_seqnums(10).await.unwrap();
    let r3 = m.get_seqnums(10).await.unwrap();

    assert_eq!(r1.end, r2.start, "r1 and r2 must be contiguous");
    assert_eq!(r2.end, r3.start, "r2 and r3 must be contiguous");

    m.shutdown().await.unwrap();
}

#[tokio::test]
async fn test_seqnum_exceeding_limit_expands_it() {
    let config = StorageConfig::for_testing().manifest;
    let mut m = make_manifest(config).await;

    let initial_limit = m.journal.seqnum_limit;

    // First request always forces limit expansion
    m.get_seqnums(20).await.unwrap();

    assert!(
        m.journal.seqnum_limit > initial_limit,
        "limit must have expanded"
    );

    m.shutdown().await.unwrap();
}

#[tokio::test]
async fn test_seqnum_large_request_gets_exact_range() {
    let config = ManifestConfig {
        seqnum_limit_step: 10,
        ..StorageConfig::for_testing().manifest
    };
    let mut m = make_manifest(config).await;

    // Request 1.5x the limit step
    let needed = 15u64;
    let range = m.get_seqnums(needed).await.unwrap();

    assert_eq!(
        range.end.get() - range.start.get(),
        needed,
        "must get exactly the requested number of seqnums"
    );

    m.shutdown().await.unwrap();
}

// -- filenum range tests --

#[tokio::test]
async fn test_filenum_range_basic() {
    let mut m = make_manifest(StorageConfig::for_testing().manifest).await;
    let start = m.filenum_current();

    let range = m.get_filenums(3).await.unwrap();

    assert_eq!(range.start, start);
    assert_eq!(range.end - range.start, 3);
    assert_eq!(m.filenum_current(), range.end);

    m.shutdown().await.unwrap();
}

#[tokio::test]
async fn test_filenum_ranges_are_contiguous() {
    let mut m = make_manifest(StorageConfig::for_testing().manifest).await;

    let r1 = m.get_filenums(5).await.unwrap();
    let r2 = m.get_filenums(5).await.unwrap();

    assert_eq!(r1.end, r2.start, "filenum ranges must be contiguous");

    m.shutdown().await.unwrap();
}

// -- overflow tests --

#[tokio::test]
async fn test_seqnum_overflow_is_detected() {
    let mut m = make_manifest(StorageConfig::for_testing().manifest).await;

    // Directly push seqnum_current near the maximum
    // We do this by requesting nearly the entire range in one shot.
    // Since SeqNum::MAX is (1 << 56) - 1, we can't actually do this
    // without making the test take forever, so instead we test that
    // checked_add overflow is handled by passing u64::MAX as the count.
    let result = m.get_seqnums(u64::MAX).await;
    assert!(
        matches!(result, Err(StorageError::SeqNumOverflow(_))),
        "expected SeqNumOverflow, got {:?}",
        result
    );

    m.shutdown().await.unwrap();
}

#[tokio::test]
async fn test_filenum_overflow_is_detected() {
    let mut m = make_manifest(StorageConfig::for_testing().manifest).await;

    // go to the u64 overflow boundary
    m.get_filenums(u64::MAX).await.unwrap();

    // get one more filenum (overflows)
    let result = m.get_filenums(1).await;
    assert!(
        matches!(result, Err(StorageError::FileNumOverflow)),
        "expected FileNumOverflow, got {:?}",
        result
    );

    m.shutdown().await.unwrap();
}

#[test]
fn test_sst_and_wal_in_same_edit() {
    let mut state = ManifestState::default();

    // pre-register a WAL file
    state.apply(ManifestEdit::V1(ManifestEditV1 {
        wal_filenums_added: Some(vec![5u64]),
        ..Default::default()
    }));
    assert_eq!(state.wal_filenums, &[5u64]);

    // atomic flush edit: new SST in, WAL file out
    let sst = SstMetadata {
        filenum: 100,
        level: 0,
        stats: SstWriterStats {
            file_size: 1024,
            min_key: Bytes::from("a"),
            max_key: Bytes::from("z"),
            min_seqnum: SeqNum::START,
            max_seqnum: SeqNum::START,
            entry_count: 32,
        },
    };
    state.apply(ManifestEdit::V1(ManifestEditV1 {
        ssts_added: Some(vec![sst]),
        wal_filenums_removed: Some(vec![5u64]),
        ..Default::default()
    }));

    assert_eq!(state.ssts.len(), 1);
    assert!(state.wal_filenums.is_empty());
}
