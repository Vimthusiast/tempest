use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};
use tracing_tree::HierarchicalLayer;

pub fn setup_tracing() {
    let layer = HierarchicalLayer::default()
        .with_indent_lines(true)
        .with_bracketed_fields(true);

    let _ = tracing_subscriber::registry()
        .with(layer)
        .with(EnvFilter::from_default_env())
        .try_init();
}
