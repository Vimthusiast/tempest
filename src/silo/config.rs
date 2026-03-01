
#[derive(Debug, Clone)]
pub struct MemTableConfig {
    /// Approximate byte size before the active memtable is frozen.
    pub size_threshold: usize,
    /// Max number of immutable memtables before writes stall.
    pub max_immutable_count: usize,
}

#[derive(Debug, Clone)]
pub struct WalConfig {
    pub rotate_file_size_threshold: u64,
    pub rotate_record_count_threshold: u32,
}

#[derive(Debug, Clone)]
pub struct ManifestConfig {
    pub seqnum_limit_step: u64,
    pub filenum_limit_step: u64,
    /// File grows beyond `initial_size * growth_factor` before rotation.
    pub growth_factor: u64,
    /// Minimum file size before the growth factor kicks in.
    pub growth_baseline: u64,
}

#[derive(Debug, Clone)]
pub struct SstConfig {
    pub block_target_size: usize,
    pub block_restart_interval: u32,
    pub bloom_false_positive_rate: f64,
}

/// Configuration for a storage silo and all its sub-components.
#[derive(Debug, Clone)]
pub struct SiloConfig {
    pub memtable: MemTableConfig,
    pub wal: WalConfig,
    pub manifest: ManifestConfig,
    pub sst: SstConfig,
}

impl Default for SiloConfig {
    fn default() -> Self {
        Self {
            memtable: MemTableConfig {
                size_threshold: 64 * 1024 * 1024, // 64 MiB
                max_immutable_count: 4,
            },
            wal: WalConfig {
                rotate_file_size_threshold: 2 * 1024 * 1024 * 1024, // 2 GiB
                rotate_record_count_threshold: 10_000,
            },
            manifest: ManifestConfig {
                seqnum_limit_step: 1_000,
                filenum_limit_step: 100,
                growth_factor: 2,
                growth_baseline: 8 * 1024 * 1024, // 8 MiB
            },
            sst: SstConfig {
                block_target_size: 4096,
                block_restart_interval: 16,
                bloom_false_positive_rate: 0.01,
            },
        }
    }
}

impl SiloConfig {
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
