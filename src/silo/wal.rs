use std::path::PathBuf;

use crate::fio::FioFS;

#[repr(C, packed)]
pub struct WalHeader {
    checksum: u64,
    length: u32,
}

#[derive(Debug)]
pub struct SiloWal<F: FioFS> {
    silo_dir: PathBuf,
    wal_dir: PathBuf,

    fs: F,
}

const WAL_DIR_NAME: &str = "wal";

impl<F: FioFS> SiloWal<F> {
    pub(crate) fn new(fs: F, silo_dir: PathBuf) -> Self {
        let wal_dir = silo_dir.join(WAL_DIR_NAME);
        info!("initializing silo write-ahead log at {:?}", wal_dir);
        Self {
            silo_dir,
            wal_dir,
            fs,
        }
    }
}
