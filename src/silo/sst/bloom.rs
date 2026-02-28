use bytes::{Bytes, BytesMut};
use xxhash_rust::xxh3::xxh3_64_with_seed;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, LittleEndian, U64};

#[derive(Debug, IntoBytes, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct BloomFilterFooter {
    k: U64<LittleEndian>,
    m: U64<LittleEndian>,
}

impl BloomFilterFooter {
    fn new(k: impl Into<U64<LittleEndian>>, m: impl Into<U64<LittleEndian>>) -> Self {
        let k = k.into();
        let m = m.into();
        Self { k, m }
    }
}

pub struct BloomFilter {
    bits: Bytes,
    k: u64,
    m: u64,
}

impl BloomFilter {
    pub fn maybe_contains(&self, key: &[u8]) -> bool {
        for i in 0..self.k {
            let bit = xxh3_64_with_seed(key, i) % self.m;
            if self.bits[(bit / 8) as usize] & (1 << (bit % 8)) == 0 {
                return false;
            }
        }
        true
    }

    pub fn footer(&self) -> BloomFilterFooter {
        BloomFilterFooter::new(self.k, self.m)
    }
}

pub struct BloomFilterBuilder {
    bits: BytesMut,
    /// Number of hash functions
    k: u64,
    /// Total number of bits.
    m: u64,
}

impl BloomFilterBuilder {
    pub fn new(n: usize, false_positive_rate: f64) -> Self {
        // optimal bit array size and number of hash functions
        let m = (-(n as f64) * false_positive_rate.ln() / 2_f64.ln().powi(2)).ceil() as u64;
        let k = ((m as f64 / n as f64) * 2_f64.ln()).ceil() as u64;
        Self {
            bits: BytesMut::zeroed((m as usize).div_ceil(8)),
            k,
            m,
        }
    }

    pub fn insert(&mut self, key: &[u8]) {
        for i in 0..self.k {
            let bit = xxh3_64_with_seed(key, i) % self.m;
            self.bits[(bit / 8) as usize] |= 1 << (bit % 8);
        }
    }

    pub fn finalize(self) -> BloomFilter {
        BloomFilter {
            bits: self.bits.freeze(),
            k: self.k,
            m: self.m,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_filter(keys: &[&[u8]]) -> BloomFilter {
        let mut builder = BloomFilterBuilder::new(keys.len(), 0.01);
        for key in keys {
            builder.insert(key);
        }
        builder.finalize()
    }

    #[test]
    fn test_inserted_keys_always_found() {
        let keys: &[&[u8]] = &[b"apple", b"banana", b"cherry", b"date", b"elderberry"];
        let filter = build_filter(keys);
        for key in keys {
            assert!(
                filter.maybe_contains(key),
                "inserted key {:?} not found",
                key
            );
        }
    }

    #[test]
    fn test_missing_key_usually_not_found() {
        // with 1% false positive rate and a small filter, missing keys should almost never match
        let keys: &[&[u8]] = &[b"apple", b"banana", b"cherry"];
        let filter = build_filter(keys);

        let queries: &[&[u8]] = &[
            b"dog",
            b"elephant",
            b"frog",
            b"giraffe",
            b"hippo",
            b"iguana",
            b"jaguar",
            b"koala",
            b"lemur",
            b"mango",
        ];
        let false_positives = queries.iter().filter(|k| filter.maybe_contains(k)).count();
        // with 1% fpr and 10 queries we expect 0-1 false positives
        assert!(
            false_positives <= 2,
            "too many false positives: {}",
            false_positives
        );
    }

    #[test]
    fn test_empty_filter() {
        let builder = BloomFilterBuilder::new(10, 0.01);
        let filter = builder.finalize();
        // nothing inserted, should never match
        assert!(!filter.maybe_contains(b"anything"));
    }

    #[test]
    fn test_footer_roundtrip() {
        let filter = build_filter(&[b"key1", b"key2"]);
        let footer = filter.footer();
        assert_eq!(footer.k.get(), filter.k);
        assert_eq!(footer.m.get(), filter.m);
    }

    #[test]
    fn test_large_number_of_keys() {
        let keys: Vec<Vec<u8>> = (0..1000u32).map(|i| i.to_le_bytes().to_vec()).collect();
        let mut builder = BloomFilterBuilder::new(keys.len(), 0.01);
        for key in &keys {
            builder.insert(key);
        }
        let filter = builder.finalize();
        // all inserted keys must be found - no false negatives ever
        for key in &keys {
            assert!(filter.maybe_contains(key));
        }
    }

    #[test]
    fn test_finalize_is_frozen_bytes() {
        // just verify finalize produces a valid BloomFilter with non-empty bits
        let mut builder = BloomFilterBuilder::new(5, 0.01);
        builder.insert(b"key");
        let filter = builder.finalize();
        assert!(!filter.bits.is_empty());
    }
}
