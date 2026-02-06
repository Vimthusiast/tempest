/// A constant u64 that has the upper most bit set.
const UPPER_U64_BIT: u64 = 0x8000_0000_0000_0000;

pub(crate) fn encode_i64_sortable(val: i64) -> [u8; 8] {
    let unsigned = (val as u64) ^ UPPER_U64_BIT;
    unsigned.to_be_bytes()
}

pub(crate) fn decode_i64_sortable(bytes: [u8; 8]) -> i64 {
    let unsigned = u64::from_be_bytes(bytes);
    (unsigned ^ UPPER_U64_BIT) as i64
}

pub(crate) fn encode_f64_sortable(val: f64) -> [u8; 8] {
    let mut bits = val.to_bits();

    if (bits & UPPER_U64_BIT) == 0 {
        // positive: flip only upper bit to make positive > negative
        bits ^= UPPER_U64_BIT;
    } else {
        // negative: flip every single bit
        bits ^= u64::MAX;
    }

    bits.to_be_bytes()
}

pub(crate) fn decode_f64_sortable(bytes: [u8; 8]) -> f64 {
    let mut bits = u64::from_be_bytes(bytes);

    if (bits & UPPER_U64_BIT) != 0 {
        // was positive: reverse upper bit flip
        bits ^= UPPER_U64_BIT;
    } else {
        // was negative: flip every single bit
        bits ^= u64::MAX;
    }

    f64::from_bits(bits)
}
