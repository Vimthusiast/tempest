use std::{collections::HashSet, io, path::PathBuf};

use futures::TryStreamExt;
use tempest_core::fio::FioFS;

use crate::{
    Storage,
    base::{Comparer, StorageResult},
    sst::{SST_DIR, get_sst_path},
    wal::{format::WAL_DIR, wal_file_path},
};

impl<F: FioFS, C: Comparer> Storage<F, C> {
    #[instrument(skip(self), level = "debug")]
    pub(crate) fn spawn_file_gc(&self, orphans: Vec<PathBuf>) {
        if orphans.is_empty() {
            return;
        }
        let fs = self.fs.clone();
        tokio_uring::spawn(async move {
            for path in orphans {
                match fs.remove_file(&path).await {
                    Ok(()) => debug!(?path, "gc: removed orphaned file"),
                    Err(e) if e.kind() == io::ErrorKind::NotFound => {
                        debug!(?path, "gc: orphaned file already gone, skipping");
                    }
                    Err(e) => warn!(?path, "gc: failed to remove orphaned file: {}", e),
                }
            }
        });
    }

    #[instrument(skip(self), level = "debug")]
    pub(crate) async fn collect_wal_orphans(&self) -> StorageResult<Vec<PathBuf>> {
        let known: HashSet<PathBuf> = self
            .manifest
            .wal_filenums()
            .iter()
            .map(|filenum| wal_file_path(&self.root_dir.join(WAL_DIR), *filenum))
            .collect();
        debug!(?known, "constructed list of known wal files");

        let wal_dir = self.root_dir.join(WAL_DIR);
        let mut orphans = Vec::new();
        let mut entries = self.fs.read_dir(&wal_dir).await?;
        while let Some(entry) = entries.try_next().await? {
            if entry.is_dir() {
                continue;
            }
            if !known.contains(entry.path()) {
                orphans.push(entry.path);
            }
        }

        Ok(orphans)
    }

    #[instrument(skip(self), level = "debug")]
    pub(crate) async fn collect_sst_orphans(&self) -> StorageResult<Vec<PathBuf>> {
        // NB: path comparison is lexicographic, not filesystem-level.
        // This is safe because all paths are constructed via get_sst_path(&self.root_dir, ...),
        // guaranteeing a consistent prefix. Canonicalization would be needed if root_dir
        // could be expressed differently across calls. root_dir must be absolute.
        let known: HashSet<PathBuf> = self
            .manifest
            .ssts()
            .iter()
            .map(|s| get_sst_path(&self.root_dir, s.filenum))
            .collect();
        debug!(?known, "constructed list of known sst files");

        let sst_dir = self.root_dir.join(SST_DIR);
        let mut orphans = Vec::new();
        let mut entries = self.fs.read_dir(&sst_dir).await?;
        while let Some(entry) = entries.try_next().await? {
            if entry.is_dir() {
                continue;
            }
            if !known.contains(entry.path()) {
                orphans.push(entry.path);
            }
        }

        Ok(orphans)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use tempest_core::{
        fio::{FioFS, VirtualFileSystem},
        test_utils::setup_tracing,
    };

    use crate::{
        Storage, StorageConfig, base::DefaultComparer, sst::get_sst_path, wal::wal_file_path,
    };

    /// Injects fake SST files directly into the sst directory,
    /// bypassing the manifest so they appear as orphans.
    async fn inject_fake_ssts(fs: &VirtualFileSystem, filenums: &[u64]) {
        for &filenum in filenums {
            let path = get_sst_path("/data", filenum);
            fs.create_dir_all(path.parent().unwrap()).await.unwrap();
            let file = fs
                .opts()
                .write(true)
                .create(true)
                .open(&path)
                .await
                .unwrap();
            drop(file);
        }
    }

    #[test]
    fn test_no_orphans_when_sst_dir_empty() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            let orphans = storage.collect_sst_orphans().await.unwrap_or_default();
            assert!(orphans.is_empty());

            storage.shutdown().await.unwrap();
        });
    }

    #[test]
    fn test_single_orphan_detected() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            inject_fake_ssts(&fs, &[9999]).await;

            let orphans = storage.collect_sst_orphans().await.unwrap();
            assert_eq!(orphans.len(), 1);
            assert_eq!(orphans[0], get_sst_path("/data", 9999));

            storage.shutdown().await.unwrap();
        });
    }

    #[test]
    fn test_multiple_orphans_detected() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            inject_fake_ssts(&fs, &[100, 200, 300]).await;

            let mut orphans = storage.collect_sst_orphans().await.unwrap();
            orphans.sort();

            assert_eq!(orphans.len(), 3);
            assert_eq!(orphans[0], get_sst_path("/data", 100));
            assert_eq!(orphans[1], get_sst_path("/data", 200));
            assert_eq!(orphans[2], get_sst_path("/data", 300));

            storage.shutdown().await.unwrap();
        });
    }

    #[test]
    fn test_known_ssts_not_reported_as_orphans() {
        // manifest has known filenums plus one unknown injected file -
        // only the unknown one should surface
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            // create real files for every SST the manifest knows about
            for sst in storage.manifest.ssts() {
                let path = get_sst_path("/data", sst.filenum);
                fs.create_dir_all(path.parent().unwrap()).await.unwrap();
                let file = fs
                    .opts()
                    .write(true)
                    .create(true)
                    .open(&path)
                    .await
                    .unwrap();
                drop(file);
            }

            // inject one orphan the manifest does not know about
            inject_fake_ssts(&fs, &[9999]).await;

            let orphans = storage.collect_sst_orphans().await.unwrap();
            assert_eq!(orphans.len(), 1, "only the injected orphan should surface");
            assert_eq!(orphans[0], get_sst_path("/data", 9999));

            storage.shutdown().await.unwrap();
        });
    }

    async fn inject_fake_wals(fs: &VirtualFileSystem, filenums: &[u64]) {
        for &filenum in filenums {
            let path = wal_file_path(&PathBuf::from("/data/wal"), filenum);
            fs.create_dir_all(path.parent().unwrap()).await.unwrap();
            let file = fs
                .opts()
                .write(true)
                .create(true)
                .open(&path)
                .await
                .unwrap();
            drop(file);
        }
    }

    #[test]
    fn test_no_orphans_when_wal_dir_empty() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            let orphans = storage.collect_wal_orphans().await.unwrap_or_default();
            // the current WAL is registered in the manifest, so nothing is orphaned
            assert!(orphans.is_empty());

            storage.shutdown().await.unwrap();
        });
    }

    #[test]
    fn test_single_wal_orphan_detected() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            inject_fake_wals(&fs, &[9999]).await;

            let orphans = storage.collect_wal_orphans().await.unwrap();
            assert_eq!(orphans.len(), 1);
            assert_eq!(orphans[0], wal_file_path(&PathBuf::from("/data/wal"), 9999));

            storage.shutdown().await.unwrap();
        });
    }

    #[test]
    fn test_multiple_wal_orphans_detected() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            inject_fake_wals(&fs, &[100, 200, 300]).await;

            let mut orphans = storage.collect_wal_orphans().await.unwrap();
            orphans.sort();

            assert_eq!(orphans.len(), 3);
            assert_eq!(orphans[0], wal_file_path(&PathBuf::from("/data/wal"), 100));
            assert_eq!(orphans[1], wal_file_path(&PathBuf::from("/data/wal"), 200));
            assert_eq!(orphans[2], wal_file_path(&PathBuf::from("/data/wal"), 300));

            storage.shutdown().await.unwrap();
        });
    }

    #[test]
    fn test_known_wals_not_reported_as_orphans() {
        setup_tracing();
        tokio_uring::start(async {
            let fs = VirtualFileSystem::new();
            let mut storage = Storage::<_, DefaultComparer>::init(
                0,
                fs.clone(),
                "/data",
                StorageConfig::for_testing(),
            )
            .await
            .unwrap();

            // inject one orphan the manifest does not know about
            inject_fake_wals(&fs, &[9999]).await;

            let orphans = storage.collect_wal_orphans().await.unwrap();
            assert_eq!(orphans.len(), 1, "only the injected orphan should surface");
            assert_eq!(orphans[0], wal_file_path(&PathBuf::from("/data/wal"), 9999));

            storage.shutdown().await.unwrap();
        });
    }
}
