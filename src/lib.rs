use std::path::PathBuf;

use futures::FutureExt;

use crate::{
    base::{DefaultComparer, TempestResult},
    fio::FioFS,
    silo::{SiloHandle, SiloWorker, batch::WriteBatch},
};

#[macro_use]
extern crate derive_more;

#[macro_use]
extern crate tracing;

pub mod base;
pub mod fio;
pub mod silo;

pub struct Tempest<F: FioFS> {
    silo_handles: Vec<(u64, SiloHandle)>,

    root_dir: PathBuf,
    fs: F,
}

impl<F: FioFS> Tempest<F> {
    pub fn new(fs: F, root_dir: impl Into<PathBuf>) -> Self {
        let root_dir = root_dir.into();

        info!("creating new tempest instance");
        Self {
            silo_handles: Vec::new(),

            root_dir: root_dir.into(),
            fs,
        }
    }

    pub async fn start(mut self) -> TempestResult<()> {
        //let num_cpus = num_cpus::get() as u64;
        let num_workers = 1;
        info!(num_workers, "starting Tempest");

        for id in 0..num_workers {
            let handle =
                SiloWorker::<F, DefaultComparer>::spawn_worker(id, self.fs.clone(), &self.root_dir);
            self.silo_handles.push((id, handle));
        }

        let mut write_futures = Vec::new();
        for (_id, handle) in &self.silo_handles {
            let mut batch = WriteBatch::new();
            batch.put(b"key1", b"value1");
            batch.put(b"key2", b"value2");
            write_futures.push(handle.write(batch));
        }
        let write_results = futures::future::join_all(write_futures).await;
        for (i, res) in write_results.into_iter().enumerate() {
            if let Err(err) = res {
                error!("could not write to silo {}: {}", i, err)
            }
        }

        let mut shutdown_futures = Vec::new();
        for (id, handle) in &self.silo_handles {
            shutdown_futures.push(handle.shutdown().map(|res| (*id, res)));
        }
        let shutdown_results = futures::future::join_all(shutdown_futures).await;
        for (id, result) in shutdown_results {
            if let Err(e) = result {
                warn!(id, "failed to shut down silo: {}", e);
            } else {
                info!(id, "shutdown of silo completed");
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use tracing_subscriber::EnvFilter;

    pub(crate) fn setup_tracing() {
        let _ = tracing_subscriber::fmt()
            .with_env_filter(EnvFilter::from_default_env())
            .try_init();
    }
}
