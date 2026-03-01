use std::path::PathBuf;

use futures::FutureExt;

use crate::{
    base::{DefaultComparer, TempestResult},
    fio::FioFS,
    silo::{SiloHandle, SiloWorker, batch::WriteBatch, config::SiloConfig},
};

#[macro_use]
extern crate derive_more;

#[macro_use]
extern crate tracing;

pub mod base;
pub mod ctrl;
pub mod fio;
pub mod silo;

pub struct Tempest<F: FioFS> {
    silo_handles: Vec<(u64, SiloHandle)>,
    silo_config: SiloConfig,

    root_dir: PathBuf,
    fs: F,
}

impl<F: FioFS> Tempest<F> {
    pub fn new(fs: F, root_dir: impl Into<PathBuf>, silo_config: SiloConfig) -> Self {
        let root_dir = root_dir.into();

        info!("creating new tempest instance");
        Self {
            silo_handles: Vec::new(),
            silo_config,

            root_dir: root_dir.into(),
            fs,
        }
    }

    pub async fn start(mut self) -> TempestResult<()> {
        //let num_cpus = num_cpus::get() as u64;
        let num_workers = 1;
        info!(num_workers, "starting Tempest");

        for id in 0..num_workers {
            let handle = SiloWorker::<F, DefaultComparer>::spawn_worker(
                id,
                self.fs.clone(),
                &self.root_dir,
                self.silo_config.clone(),
            );
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

    use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};
    use tracing_tree::HierarchicalLayer;

    use crate::base::SeqNum;

    pub(crate) fn setup_tracing() {
        let layer = HierarchicalLayer::default()
            .with_indent_lines(true)
            .with_bracketed_fields(true);

        let _ = tracing_subscriber::registry()
            .with(layer)
            .with(EnvFilter::from_default_env())
            .try_init();
    }

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
}
