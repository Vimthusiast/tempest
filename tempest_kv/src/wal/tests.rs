use itertools::Itertools;
use tempest_core::{fio::VirtualFileSystem, test_utils::setup_tracing};

use super::*;
use crate::config::StorageConfig;

#[tokio::test]
async fn test_silo_wal() -> Result<(), Box<dyn std::error::Error>> {
    setup_tracing();

    let fs = VirtualFileSystem::new();
    let storage_dir = PathBuf::from("/data/silo0");
    let data = Bytes::from_static(b"some-test-data");

    const NUM_FILENUMS: u64 = 16;
    let filenums: [u64; NUM_FILENUMS as usize] =
        (0..NUM_FILENUMS).into_iter().collect_array().unwrap();

    let config = StorageConfig::for_testing().wal;
    {
        let (mut wal, mut recovery_reader) = Wal::init(
            fs.clone(),
            storage_dir.clone(),
            filenums[0],
            &[],
            config.clone(),
        )
        .await?;
        let _ = wal.append(data.clone()).await?;
        assert!(recovery_reader.next().await.is_none());
    }

    {
        let (mut wal, mut recovery_reader) = Wal::init(
            fs.clone(),
            storage_dir.clone(),
            filenums[1],
            &[filenums[0]],
            config.clone(),
        )
        .await?;
        assert_eq!(recovery_reader.next().await.unwrap()?, data);
        assert!(recovery_reader.next().await.is_none());
        // rotate wal and push data again
        wal.rotate(filenums[2]).await?;
        let _ = wal.append(data.clone()).await?;
        let _ = wal.append(data.clone()).await?;
    }

    {
        let (_, mut recovery_reader) = Wal::init(
            fs.clone(),
            storage_dir.clone(),
            filenums[3],
            // just use last wal, dropping [0] and [1]
            &[filenums[2]],
            config.clone(),
        )
        .await?;
        assert_eq!(recovery_reader.next().await.unwrap()?, data);
        assert_eq!(recovery_reader.next().await.unwrap()?, data);
        assert!(recovery_reader.next().await.is_none());
    }

    Ok(())
}
