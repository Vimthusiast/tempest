use tempest_core::fio::VirtualFileSystem;

use super::*;
use crate::{
    silo::config::SiloConfig,
    tests::{filenum_gen, setup_tracing},
};

#[tokio::test]
async fn test_silo_wal() -> Result<(), Box<dyn std::error::Error>> {
    setup_tracing();

    let fs = VirtualFileSystem::new();
    let silo_dir = PathBuf::from("data/silo0");
    let mut next_filenum = filenum_gen();
    let data = Bytes::from_static(b"some-test-data");

    let first_filenum = next_filenum();
    let second_filenum = next_filenum();

    let config = SiloConfig::for_testing().wal;
    {
        let (mut wal, mut recovery_reader) = SiloWal::init(
            fs.clone(),
            silo_dir.clone(),
            first_filenum,
            &[],
            config.clone(),
        )
        .await?;
        let _ = wal.append(data.clone()).await?;
        assert!(recovery_reader.next().await.is_none());
    }

    {
        let (_, mut recovery_reader) = SiloWal::init(
            fs.clone(),
            silo_dir.clone(),
            second_filenum,
            &[first_filenum],
            config.clone(),
        )
        .await?;
        assert_eq!(recovery_reader.next().await.unwrap().unwrap(), data);
        assert!(recovery_reader.next().await.is_none());
    }

    Ok(())
}
