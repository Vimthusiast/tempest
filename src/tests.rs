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
