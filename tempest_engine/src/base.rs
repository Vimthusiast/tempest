use tempest_core::utils::PrettyBytes;
use tempest_kv::base::Comparer;

use crate::ctrl::hlc::HlcTimestamp;

/// The length of the key-suffix for Tempest's internal key format.
pub const KEY_SUFFIX_SIZE: usize = std::mem::size_of::<HlcTimestamp>();

/// The comparer used for all engine-managed storage silos.
/// The suffix is for the HLC timestamp encoded as a big-endian u64.
#[derive(Default, Clone)]
pub struct EngineComparer;

impl Comparer for EngineComparer {
    fn split(key: &[u8]) -> usize {
        key.len() - KEY_SUFFIX_SIZE
    }

    fn compare_prefix(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
        a.cmp(b)
    }

    fn compare_suffix(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
        // NB: the hlc suffix sorts descending
        b.cmp(a)
    }

    fn format(key: &[u8]) -> String {
        let (prefix, suffix) = Self::split_up(key);
        let hlc = HlcTimestamp::from_u64(u64::from_be_bytes(suffix.try_into().unwrap()));
        format!("{:?}@{:?}", PrettyBytes(prefix), hlc)
    }
}

#[repr(u8)]
pub enum KeySpace {
    TableRow = 0x01,
}

#[cfg(test)]
mod tests {
    use crate::base::KEY_SUFFIX_SIZE;

    #[test]
    fn test_key_suffix_size_stays_consistent() {
        // NB: A change of this would require a version bump, and therefore a migration!
        assert_eq!(KEY_SUFFIX_SIZE, 8);
    }
}
