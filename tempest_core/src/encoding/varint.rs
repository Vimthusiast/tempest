use bytes::{BufMut, BytesMut};
use integer_encoding::VarInt;

/// Encodes `i` as a variable-length integer, writing it into `buf`.
pub fn encode_varint(buf: &mut BytesMut, i: usize) {
    // reserve space
    let varint_size = i.required_space();
    buf.put_bytes(0, varint_size);
    // encode varint
    let buflen = buf.len();
    let written = i.encode_var(&mut buf[buflen - varint_size..]);
    debug_assert_eq!(written, varint_size);
}

/// Decodes a variable-length integer from `src`.
///
/// # Returns
///
/// - `Some((varint, bytes_read))`, if successfully decoding the varint.
/// - `None`, if all bytes has MSB set.
pub fn decode_varint(src: &[u8]) -> Option<(usize, usize)> {
    usize::decode_var(src)
}

#[cfg(test)]
mod tests {
    use bytes::BytesMut;

    use super::*;

    fn roundtrip(i: usize) -> (usize, usize) {
        let mut buf = BytesMut::new();
        encode_varint(&mut buf, i);
        let (val, bytes_read) = decode_varint(&buf).expect("decode failed");
        assert_eq!(val, i, "roundtrip failed for {}", i);
        (val, bytes_read)
    }

    // -- roundtrip --

    #[test]
    fn test_roundtrip_zero() {
        roundtrip(0);
    }

    #[test]
    fn test_roundtrip_one() {
        roundtrip(1);
    }

    #[test]
    fn test_roundtrip_max_one_byte() {
        roundtrip(127); // largest value that fits in 1 byte
    }

    #[test]
    fn test_roundtrip_min_two_bytes() {
        roundtrip(128); // smallest value requiring 2 bytes
    }

    #[test]
    fn test_roundtrip_large_values() {
        for val in [255, 256, 1024, 65535, 65536, 1 << 20, 1 << 28] {
            roundtrip(val);
        }
    }

    #[test]
    fn test_roundtrip_usize_max() {
        roundtrip(usize::MAX);
    }

    // -- encoding size --

    #[test]
    fn test_single_byte_encoding() {
        let mut buf = BytesMut::new();
        encode_varint(&mut buf, 127);
        assert_eq!(buf.len(), 1, "127 should encode to 1 byte");
    }

    #[test]
    fn test_two_byte_encoding() {
        let mut buf = BytesMut::new();
        encode_varint(&mut buf, 128);
        assert_eq!(buf.len(), 2, "128 should encode to 2 bytes");
    }

    #[test]
    fn test_zero_encodes_to_one_byte() {
        let mut buf = BytesMut::new();
        encode_varint(&mut buf, 0);
        assert_eq!(buf.len(), 1);
    }

    // -- decode --

    #[test]
    fn test_decode_returns_correct_bytes_read() {
        let mut buf = BytesMut::new();
        encode_varint(&mut buf, 128);
        let (_, bytes_read) = decode_varint(&buf).unwrap();
        assert_eq!(bytes_read, 2);
    }

    #[test]
    fn test_decode_none_on_all_msb_set() {
        // all bytes have MSB set - no terminating byte, decode should return None
        let buf = &[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
        assert!(decode_varint(buf).is_none());
    }

    #[test]
    fn test_decode_ignores_trailing_bytes() {
        // decode should stop at the varint boundary, not consume trailing data
        let mut buf = BytesMut::new();
        encode_varint(&mut buf, 42);
        buf.extend_from_slice(&[0xAB, 0xCD]); // trailing garbage
        let (val, bytes_read) = decode_varint(&buf).unwrap();
        assert_eq!(val, 42);
        assert!(bytes_read < buf.len(), "should not consume trailing bytes");
    }

    // -- sequential encoding --

    #[test]
    fn test_multiple_varints_sequential() {
        // encode several varints back to back, decode them in order
        let values = [0usize, 1, 127, 128, 300, 100_000];
        let mut buf = BytesMut::new();
        for &v in &values {
            encode_varint(&mut buf, v);
        }

        let mut slice = &buf[..];
        for &expected in &values {
            let (val, bytes_read) = decode_varint(slice).unwrap();
            assert_eq!(val, expected);
            slice = &slice[bytes_read..];
        }
        assert!(slice.is_empty(), "buffer should be fully consumed");
    }
}
