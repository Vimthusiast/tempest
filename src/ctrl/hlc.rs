//! # Hybrid Logical Clock
//!
//! This module contains the logic for generating and encoding [`HlcTimestamp`]s, through the
//! [`HlcGenerator`] implementation. Clock skew across restarts is a possibility, that the user
//! has to account for, depending on the users clock implementation for retrieving milliseconds.

// => We could try persisting the timestamp every so often to avoid going back in time, like with
// the sequence numbers in the [`SiloManifest`] implementation (range allocations).

/// # Hybrid Logical Clock Timestamp
///
/// Tempest uses these to order data within different silos, using a custom [`Comparer`]
/// implementation.
///
/// [`Comparer`]: crate::base::comparer::Comparer
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct HlcTimestamp(
    /// Packs the millis in the upper 48 bits and the counter in the lower 16 bits.
    u64,
);

impl HlcTimestamp {
    #[inline]
    pub const fn new(millis: u64, counter: u16) -> Self {
        Self((millis << 16) | (counter as u64))
    }

    #[inline]
    pub const fn millis(&self) -> u64 {
        self.0 >> 16
    }

    #[inline]
    pub const fn counter(&self) -> u16 {
        (self.0 & 0xFFFF) as u16
    }
}

/// Generates unique [`HlcTimestamp`]s through the [`generate`] method.
pub struct HlcGenerator {
    last_timestamp: HlcTimestamp,
}

impl HlcGenerator {
    pub fn new() -> Self {
        Self {
            last_timestamp: HlcTimestamp(0),
        }
    }

    pub fn generate(&mut self, now_ms: u64) -> HlcTimestamp {
        let last_ms = self.last_timestamp.millis();

        if now_ms > last_ms {
            // Start fresh HLC stamp from current ms, with counter reset to zero.
            self.last_timestamp = HlcTimestamp::new(now_ms, 0);
        } else {
            // Increment counter, potentially jumping physical clock, if counter is exhausted.
            // This will eventually recover, once we get back ahead of time.
            // In practice, this will rarely overflow the counter, unless we really need more than
            // `2^16-1 = 65535` stamps **every millisecond**.
            self.last_timestamp.0 += 1;
        }

        self.last_timestamp
    }
}
