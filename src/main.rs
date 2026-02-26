#[macro_use]
extern crate tracing;

use tempest::{Tempest, base::TempestResult, fio::UringFileSystem};

use tracing_subscriber::EnvFilter;

#[tokio::main]
async fn main() -> TempestResult<()> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();
    info!("all your storage are belong to us!");

    let fs = UringFileSystem;
    let root_dir = "./data";

    Tempest::new(fs, root_dir).start().await?;

    info!("exited");
    tokio::signal::ctrl_c().await?;
    Ok(())
}
