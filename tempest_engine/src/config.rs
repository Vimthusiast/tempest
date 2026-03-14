use tempest_core::journal::JournalConfig;

#[derive(Debug, Clone)]
pub struct CatalogConfig {
    // ..other options later

    // -- journal config options, flattened --
    pub growth_factor: f64,
    pub growth_baseline: u64,
}

impl CatalogConfig {
    pub fn journal_config(&self) -> JournalConfig {
        JournalConfig {
            growth_factor: self.growth_factor,
            growth_baseline: self.growth_baseline,
        }
    }
}

impl Default for CatalogConfig {
    fn default() -> Self {
        Self {
            growth_factor: 1.5,
            growth_baseline: 8 * 1024 * 1024, // 8 MiB
        }
    }
}

#[derive(Default, Clone)]
pub struct EngineConfig {
    pub catalog: CatalogConfig
}
