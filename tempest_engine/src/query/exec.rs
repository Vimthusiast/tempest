use tempest_core::fio::FioFS;

use crate::{Engine, query::plan::PlanNode};

impl<F: FioFS> Engine<F> {
    pub(crate) fn build_executor(&self, plan: PlanNode) -> Result<(), ()> {
        Ok(())
    }
}
