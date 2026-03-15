use std::{path::PathBuf, thread};

use bytes::Bytes;
use tempest_core::fio::FioFS;
use tokio::sync::{mpsc, oneshot};
use tracing::Level;

use crate::{
    Storage,
    base::{Comparer, StorageError, StorageResult},
    batch::WriteBatch,
    config::StorageConfig,
    iterator::StorageIterator,
};

#[derive(Debug)]
pub enum StorageCommand {
    Write {
        batch: WriteBatch,
        respond_to: oneshot::Sender<StorageResult<()>>,
    },
    Scan {
        // TODO: implement scan via channel + snapshotting
        seek_prefix: Bytes,
        respond_to: oneshot::Sender<StorageResult<mpsc::Receiver<StorageResult<(Bytes, Bytes)>>>>,
    },
    Shutdown {
        respond_to: oneshot::Sender<StorageResult<()>>,
    },
}

pub struct StorageHandle {
    sender: mpsc::Sender<StorageCommand>,
}

impl StorageHandle {
    pub async fn write(&self, batch: WriteBatch) -> StorageResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(StorageCommand::Write {
                batch,
                respond_to: tx,
            })
            .await?;
        rx.await?
    }

    pub async fn scan(
        &self,
        seek_prefix: Bytes,
    ) -> StorageResult<mpsc::Receiver<StorageResult<(Bytes, Bytes)>>> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(StorageCommand::Scan {
                seek_prefix,
                respond_to: tx,
            })
            .await?;
        rx.await?
    }

    pub async fn shutdown(&self) -> StorageResult<()> {
        let (tx, rx) = oneshot::channel();
        self.sender
            .send(StorageCommand::Shutdown { respond_to: tx })
            .await?;
        rx.await?
    }
}

#[derive(Debug)]
pub enum CommandControlFlow {
    Continue,
    Shutdown {
        respond_to: oneshot::Sender<StorageResult<()>>,
    },
}

/// A background worker that can be controlled through channel commands and manages a [`Storage`].
pub struct StorageWorker<F: FioFS, C: Comparer> {
    storage: Storage<F, C>,
    receiver: mpsc::Receiver<StorageCommand>,
}

impl<F: FioFS, C: Comparer> StorageWorker<F, C> {
    /// Creates a storage worker that initializes and manages a [`Storage`] within the `root_dir`.
    pub fn spawn_worker(
        id: u64,
        fs: F,
        root_dir: impl Into<PathBuf>,
        config: StorageConfig,
    ) -> StorageHandle {
        let root_dir = root_dir.into();
        let storage_dir = root_dir.join(format!("storage-{}", id));
        let (sender, receiver) = mpsc::channel(1024);

        thread::spawn(move || {
            let _worker_entered = span!(Level::INFO, "storage-worker", id).entered();
            info!(id, ?root_dir, "spawning storage worker");
            // Specify core affinity for this worker
            core_affinity::set_for_current(core_affinity::CoreId { id: id as usize });

            let result = tokio_uring::start(async move {
                info!(id, "initialized tokio-uring runtime");
                let storage = Storage::<F, C>::init(id, fs, storage_dir, config).await?;
                let mut worker = StorageWorker { storage, receiver };
                worker.start().await;

                Ok::<_, StorageError>(())
            });
            if let Err(err) = result {
                error!("storage worker crashed: {}", err);
            }
        });

        StorageHandle { sender }
    }

    async fn start(&mut self) {
        info!("starting storage worker");
        let respond_to = loop {
            let control_flow = match self.receiver.recv().await {
                Some(cmd) => match self.handle_command(cmd).await {
                    Ok(cf) => cf,
                    Err(err) => {
                        error!("could not handle command: {}", err);
                        break None;
                    }
                },
                None => {
                    info!("channel closed. exiting");
                    break None;
                }
            };

            match control_flow {
                CommandControlFlow::Continue => continue,
                CommandControlFlow::Shutdown { respond_to } => {
                    info!("shutdown has been requested");
                    break Some(respond_to);
                }
            }
        };

        let result = self.storage.shutdown().await;
        if let Some(tx) = respond_to {
            if let Err(_) = tx.send(result) {
                error!("could not send shutdown confirmation: channel closed");
            }
        } else {
            match result {
                Ok(()) => info!("successfully shut down."),
                Err(err) => error!("could not shut down correctly: {}", err),
            }
        }
    }

    #[instrument(skip_all)]
    async fn handle_command(&mut self, cmd: StorageCommand) -> StorageResult<CommandControlFlow> {
        match cmd {
            StorageCommand::Write { batch, respond_to } => {
                let result = self.storage.write(batch).await;
                if let Err(e) = result.as_ref() {
                    error!("failed to execute write command: {}", e);
                }
                if let Err(_) = respond_to.send(result) {
                    error!("could not respond to write command: channel closed");
                }
                Ok(CommandControlFlow::Continue)
            }
            StorageCommand::Scan {
                seek_prefix,
                respond_to,
            } => {
                let (tx, rx) = mpsc::channel(64);
                let _ = respond_to.send(Ok(rx));

                let snapshot = self.storage.highest_seqnum();
                let mut iter = self.storage.scan(snapshot).await?;
                iter.seek(&seek_prefix).await?;

                // read the first entry directly after seek without advancing
                loop {
                    match (iter.key(), iter.value()) {
                        (Some(key), Some(value)) => {
                            let key = key.key().clone();
                            if !key.starts_with(&seek_prefix[..5]) {
                                break;
                            }
                            let value = value.clone();
                            if tx.send(Ok((key, value))).await.is_err() {
                                break;
                            }
                            // now advance
                            match iter.next().await {
                                Ok(Some(())) => continue,
                                Ok(None) => break,
                                Err(e) => {
                                    let _ = tx.send(Err(e)).await;
                                    break;
                                }
                            }
                        }
                        _ => break,
                    }
                }

                Ok(CommandControlFlow::Continue)
            }
            StorageCommand::Shutdown { respond_to } => {
                Ok(CommandControlFlow::Shutdown { respond_to })
            }
        }
    }
}
