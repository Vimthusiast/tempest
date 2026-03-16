//! This module contains the trait abstraction for key comparison within Tempests storage layer.

use std::cmp;

use tempest_core::utils::PrettyBytes;

/// Defines how keys are split, compared, and ordered within the storage layer.
///
/// Every key in Tempest's LSM storage consists of two parts: a **prefix** that
/// identifies the logical entry (e.g. a row), and an optional **suffix** that
/// encodes a version (e.g. an HLC timestamp). The `Comparer` trait abstracts
/// over both, allowing the engine to attach arbitrary versioning semantics to
/// keys without the KV layer needing to understand them.
///
/// # Prefix and Suffix
///
/// [`split`] determines where the prefix ends and the suffix begins. If a key
/// has no suffix, [`split`] returns the full key length, and [`compare_suffix`]
/// is never meaningfully called.
///
/// # Physical vs. Logical Ordering
///
/// Two distinct orderings are derived from the prefix/suffix split:
///
/// - **Physical** ([`compare_physical`]): the on-disk sort order. Keys are
///   ordered ascending by prefix, then by suffix. This is what SSTs and
///   MemTables use to store and seek entries.
///
/// - **Logical** ([`compare_logical`]): the identity used for deduplication.
///   Two keys with equal prefixes are considered the *same row*, regardless of
///   their suffix. This is what compaction and MVCC iterators use to collapse
///   multiple versions of a row down to one.
///
/// # Suffix Ordering Convention
///
/// The direction of [`compare_suffix`] has semantic consequences for any
/// iterator that relies on forward scanning. If the suffix sorts **descending**
/// (i.e. `compare_suffix` returns `b.cmp(a)`), the newest version of a row
/// appears first in a forward scan, which is required for correct behavior of
/// both prefix deduplication (keep the first = newest) and suffix-bound
/// filtering (skip entries newer than the read timestamp).
///
/// Implementors that do not need versioning (like [`DefaultComparer`]) can
/// return [`Ordering::Equal`] from [`compare_suffix`], which makes all
/// iterators behave as if there is only ever one version per key.
///
/// [`split`]: Comparer::split
/// [`compare_suffix`]: Comparer::compare_suffix
/// [`compare_physical`]: Comparer::compare_physical
/// [`compare_logical`]: Comparer::compare_logical
/// [`Ordering::Equal`]: std::cmp::Ordering::Equal
pub trait Comparer: Default + Clone + 'static {
    /// Returns the index where the version suffix starts.
    /// If there is no suffix, returns the length of the slice.
    fn split(key: &[u8]) -> usize;

    /// Compares the prefix part of two keys.
    fn compare_prefix(a: &[u8], b: &[u8]) -> cmp::Ordering;

    /// Compares the suffix part of two keys.
    fn compare_suffix(a: &[u8], b: &[u8]) -> cmp::Ordering;

    /// Splits the key and returns the prefix and suffix part.
    fn split_up<'a>(key: &'a [u8]) -> (&'a [u8], &'a [u8]) {
        let knon = Self::split(key);
        key.split_at(knon)
    }

    /// Compares only the prefix (logical identity) of two keys, ignoring the suffix.
    ///
    /// Two keys are logically equal if their prefixes compare equal, regardless of
    /// their suffix. This is the identity used for deduplication - the suffix
    /// encodes a version of the row, not a distinct row.
    fn compare_logical(a: &[u8], b: &[u8]) -> cmp::Ordering {
        let anon = Self::split(a);
        let bnon = Self::split(b);
        Self::compare_prefix(&a[..anon], &b[..bnon])
    }

    /// Compares two keys by their full physical ordering: ascending by prefix,
    /// then ascending by suffix.
    ///
    /// This is the sort order used on-disk in SSTs and MemTables. For a comparer
    /// with a descending suffix (e.g. HLC timestamps stored as `b.cmp(a)`), keys
    /// with the same prefix will sort with the newest version first, which is
    /// required for correct behavior of forward-scanning iterators.
    fn compare_physical(a: &[u8], b: &[u8]) -> cmp::Ordering {
        let anon = Self::split(a);
        let bnon = Self::split(b);

        match Self::compare_prefix(&a[..anon], &b[..bnon]) {
            cmp::Ordering::Equal => Self::compare_suffix(&a[anon..], &b[bnon..]),
            ord => ord,
        }
    }

    /// Format a key as a String.
    fn format(key: &[u8]) -> String;
}

#[derive(Default, Clone)]
pub struct DefaultComparer;

impl Comparer for DefaultComparer {
    fn split(key: &[u8]) -> usize {
        key.len()
    }

    fn compare_prefix(a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }

    fn compare_suffix(_a: &[u8], _b: &[u8]) -> cmp::Ordering {
        cmp::Ordering::Equal
    }

    fn format(key: &[u8]) -> String {
        format!("{:?}", PrettyBytes(key))
    }
}

#[derive(Default, Clone)]
pub struct AssertComparer<C: Comparer>(C);

impl<C: Comparer> Comparer for AssertComparer<C> {
    fn split(key: &[u8]) -> usize {
        C::split(key)
    }

    fn compare_prefix(a: &[u8], b: &[u8]) -> cmp::Ordering {
        C::compare_prefix(a, b)
    }

    fn compare_suffix(a: &[u8], b: &[u8]) -> cmp::Ordering {
        C::compare_suffix(a, b)
    }

    fn compare_physical(a: &[u8], b: &[u8]) -> cmp::Ordering {
        // compare the two keys completely (prefix and suffix)
        let res = C::compare_physical(a, b);

        // check for anti-symmetry:
        // `a == b` implies `b == a`
        // `a > b` implies `b < a`
        // `a < b` implies `b > a`
        debug_assert_eq!(
            res,
            C::compare_physical(b, a).reverse(),
            "anti-symmetry violation: compare(a,b) != reverse(compare(b,a))"
        );

        // check for consistency with prefix:
        // if a < b, then prefix(a) must be <= prefix(b)
        let split_a = C::split(a);
        let split_b = C::split(b);
        let prefix_cmp = C::compare_prefix(&a[..split_a], &b[..split_b]);

        match prefix_cmp {
            cmp::Ordering::Less => {
                debug_assert_eq!(
                    res,
                    cmp::Ordering::Less,
                    "consistency violation: prefix(a) < prefix(b) but a >= b"
                )
            }
            cmp::Ordering::Greater => {
                debug_assert_eq!(
                    res,
                    cmp::Ordering::Greater,
                    "consistency violation: prefix(a) > prefix(b) but a <= b"
                )
            }
            cmp::Ordering::Equal => {
                // only suffix comparison matters here
            }
        }

        // NB: without state, we cannot check for transitivity, but we don't really need to here,
        // but should do it in unit tests instead.

        res
    }

    fn format(key: &[u8]) -> String {
        C::format(key)
    }
}

/// A [`Comparer`] that treats the last `N` bytes of a key as a fixed-size suffix,
/// comparing both prefix and suffix lexicographically (byte-wise).
///
/// The interpretation of the suffix bytes is left entirely to the caller. For numeric
/// values, big-endian encoding is recommended, as it preserves natural ordering under
/// byte-wise comparison.
#[derive(Default, Clone)]
pub struct FixedSuffixComparer<const N: usize>;

impl<const N: usize> Comparer for FixedSuffixComparer<N> {
    fn split(key: &[u8]) -> usize {
        key.len().saturating_sub(N)
    }

    fn compare_prefix(a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }

    fn compare_suffix(a: &[u8], b: &[u8]) -> cmp::Ordering {
        a.cmp(b)
    }

    fn format(key: &[u8]) -> String {
        let (prefix, suffix) = Self::split_up(key);
        format!("{:?} | {:?}", PrettyBytes(prefix), PrettyBytes(suffix))
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
