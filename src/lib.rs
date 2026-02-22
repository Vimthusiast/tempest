#[macro_use]
extern crate derive_more;

#[macro_use]
extern crate tracing;

pub mod base;
pub mod fio;
pub mod silo;

pub struct Tempest;

#[cfg(test)]
mod tests {
    use tracing_subscriber::EnvFilter;

    pub(crate) fn setup_tracing() {
        let _ = tracing_subscriber::fmt()
            .with_env_filter(EnvFilter::from_default_env())
            .try_init();
    }
}
