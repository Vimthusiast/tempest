use tempest_core::journal::JournalConfig;

#[derive(Debug, Clone)]
pub struct MemTableConfig {
    /// Approximate byte size before the active memtable is frozen.
    pub size_threshold: usize,
    /// Max number of immutable memtables before writes stall.
    pub max_immutable_count: usize,
}

impl Default for MemTableConfig {
    fn default() -> Self {
        Self {
            size_threshold: 64 * 1024 * 1024, // 64 MiB
            max_immutable_count: 4,
        }
    }
}

#[derive(Debug, Clone)]
pub struct WalConfig {
    pub rotate_file_size_threshold: u64,
    pub rotate_record_count_threshold: u32,
}

impl Default for WalConfig {
    fn default() -> Self {
        Self {
            rotate_file_size_threshold: 2 * 1024 * 1024 * 1024, // 2 GiB
            rotate_record_count_threshold: 10_000,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ManifestConfig {
    pub seqnum_limit_step: u64,
    pub filenum_limit_step: u64,
    /// File grows beyond `initial_size * growth_factor` before rotation.
    pub growth_factor: f64,
    /// Minimum file size before the growth factor kicks in.
    pub growth_baseline: u64,
}

impl ManifestConfig {
    pub fn journal_config(&self) -> JournalConfig {
        JournalConfig {
            growth_factor: self.growth_factor,
            growth_baseline: self.growth_baseline,
        }
    }
}

impl Default for ManifestConfig {
    fn default() -> Self {
        Self {
            seqnum_limit_step: 1_000,
            filenum_limit_step: 100,
            growth_factor: 1.5,
            growth_baseline: 8 * 1024 * 1024, // 8 MiB
        }
    }
}

#[derive(Debug, Clone)]
pub struct SstConfig {
    pub block_target_size: usize,
    pub block_restart_interval: u32,
    pub bloom_false_positive_rate: f64,
}

impl Default for SstConfig {
    fn default() -> Self {
        Self {
            block_target_size: 4096,
            block_restart_interval: 16,
            bloom_false_positive_rate: 0.01,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CompactionConfig {
    /// The number of SST files that may accumulate before a compaction is triggered.
    pub l0_file_threshold: usize,
}

impl Default for CompactionConfig {
    fn default() -> Self {
        Self {
            l0_file_threshold: 4,
        }
    }
}

/// Configuration for this storage and all its sub-components.
#[derive(Debug, Clone, Default)]
pub struct StorageConfig {
    pub memtable: MemTableConfig,
    pub wal: WalConfig,
    pub manifest: ManifestConfig,
    pub sst: SstConfig,
    pub compaction: CompactionConfig,
}

impl StorageConfig {
    /// A config tuned for fast testing.
    ///
    /// - **memtable:** Tiny thresholds force frequent flushes/compactions.
    #[cfg(test)]
    pub fn for_testing() -> Self {
        Self {
            memtable: MemTableConfig {
                size_threshold: 512,
                max_immutable_count: 2,
            },
            ..Default::default()
        }
    }
}
