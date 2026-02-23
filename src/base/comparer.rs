//! This module contains the trait abstraction for key comparison within Tempests storage layer.

use std::cmp;

pub trait Comparer: Default + Clone + 'static {
    /// Returns the index where the version suffix starts.
    /// If there is no suffix, returns the length of the slice.
    fn split(&self, key: &[u8]) -> usize;

    /// Compares the prefix part of two keys.
    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

    /// Compares the suffix part of two keys.
    fn compare_suffix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering;

    /// Compares the logical part (user facing) of a key.
    /// Usually, this just compares the key prefix, but you may choose yourself.
    fn compare_logical(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        let anon = self.split(a);
        let bnon = self.split(b);
        self.compare_prefix(&a[..anon], &b[..bnon])
    }

    /// Full comparison of two different keys, for physically ordering them in SSTs/MemTables.
    /// It first compares them ascending by the prefix, and then ascending by the suffix.
    fn compare_physical(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        let anon = self.split(a);
        let bnon = self.split(b);

        match self.compare_prefix(&a[..anon], &b[..bnon]) {
            cmp::Ordering::Equal => self.compare_suffix(&a[anon..], &b[bnon..]),
            ord => ord,
        }
    }
}

#[derive(Default, Clone)]
pub struct DefaultComparer;

impl Comparer for DefaultComparer {
    fn split(&self, key: &[u8]) -> usize {
        key.len()
    }

    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }

    fn compare_suffix(&self, _a: &[u8], _b: &[u8]) -> cmp::Ordering {
        cmp::Ordering::Equal
    }
}

#[derive(Default, Clone)]
pub struct AssertComparer<C: Comparer>(C);

impl<C: Comparer> Comparer for AssertComparer<C> {
    fn split(&self, key: &[u8]) -> usize {
        self.0.split(key)
    }

    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        self.0.compare_prefix(a, b)
    }

    fn compare_suffix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        self.0.compare_suffix(a, b)
    }

    fn compare_physical(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        // compare the two keys completely (prefix and suffix)
        let res = self.0.compare_physical(a, b);

        // check for anti-symmetry:
        // `a == b` implies `b == a`
        // `a > b` implies `b < a`
        // `a < b` implies `b > a`
        debug_assert_eq!(
            res,
            self.0.compare_physical(b, a).reverse(),
            "Anti-symmetry violation: compare(a,b) != reverse(compare(b,a))"
        );

        // check for consistency with prefix:
        // if a < b, then prefix(a) must be <= prefix(b)
        let split_a = self.0.split(a);
        let split_b = self.0.split(b);
        let prefix_cmp = a[..split_a].cmp(&b[..split_b]);

        match prefix_cmp {
            cmp::Ordering::Less => {
                debug_assert_eq!(
                    res,
                    cmp::Ordering::Less,
                    "Consistency violation: prefix(a) < prefix(b) but a >= b"
                )
            }
            cmp::Ordering::Greater => {
                debug_assert_eq!(
                    res,
                    cmp::Ordering::Greater,
                    "Consistency violation: prefix(a) > prefix(b) but a <= b"
                )
            }
            cmp::Ordering::Equal => {
                // only suffix comparison matters here
            }
        }

        res
    }
}

#[derive(Default, Clone)]
pub struct FixedSuffixComparer<const N: usize>;

impl<const N: usize> Comparer for FixedSuffixComparer<N> {
    fn split(&self, key: &[u8]) -> usize {
        key.len().saturating_sub(N)
    }

    fn compare_prefix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }

    fn compare_suffix(&self, a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;
    use crate::base::InternalKey;

    #[test]
    fn test_assert_comparer() {
        type C = AssertComparer<DefaultComparer>;
        let keys: &[InternalKey<C>] = &[
            InternalKey::test(1),
            InternalKey::test(2),
            InternalKey::test(3),
            InternalKey::test(4),
            InternalKey::test(5),
        ];

        for (a, b) in keys.iter().tuple_windows() {
            assert!(b > a);
        }
    }
}
