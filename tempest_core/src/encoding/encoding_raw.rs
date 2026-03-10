use std::string::FromUtf8Error;

use bytes::{Buf, BufMut, Bytes, BytesMut};

use crate::encoding::varint::{decode_varint, encode_varint};

pub trait BufPutRawExt {
    fn put_i64_raw(&mut self, i: i64);
    fn put_bool_raw(&mut self, b: bool);
    fn put_str_raw(&mut self, s: &str);
}

impl BufPutRawExt for BytesMut {
    fn put_i64_raw(&mut self, i: i64) {
        self.put_i64(i);
    }

    fn put_bool_raw(&mut self, b: bool) {
        self.put_u8(b as u8);
    }

    fn put_str_raw(&mut self, s: &str) {
        encode_varint(self, s.len());
        self.put_slice(s.as_bytes());
    }
}

#[derive(Debug, Display, Error, From)]
pub enum DecodeError {
    UnexpectedEof,
    DecodeVarintError,
    FromUtf8Error(FromUtf8Error),
}

pub trait BufGetRawExt {
    fn get_i64_raw(&mut self) -> Result<i64, DecodeError>;
    fn get_bool_raw(&mut self) -> Result<bool, DecodeError>;
    fn get_str_raw(&mut self) -> Result<String, DecodeError>;
}

impl BufGetRawExt for Bytes {
    fn get_i64_raw(&mut self) -> Result<i64, DecodeError> {
        if self.len() < 8 {
            return Err(DecodeError::UnexpectedEof);
        }
        Ok(self.get_i64())
    }

    fn get_bool_raw(&mut self) -> Result<bool, DecodeError> {
        if self.is_empty() {
            return Err(DecodeError::UnexpectedEof);
        }
        Ok(self.get_u8() != 0)
    }

    fn get_str_raw(&mut self) -> Result<String, DecodeError> {
        let (len, bytes_read) =
            decode_varint(self).ok_or_else(|| DecodeError::DecodeVarintError)?;
        self.advance(bytes_read);
        if self.len() < len {
            return Err(DecodeError::UnexpectedEof);
        }
        let bytes = self.split_to(len);

        String::from_utf8(bytes.to_vec()).map_err(DecodeError::FromUtf8Error)
    }
}

#[cfg(test)]
mod tests {
    use bytes::{Bytes, BytesMut};

    use super::*;

    // -- helpers --

    fn encode_i64(i: i64) -> Bytes {
        let mut buf = BytesMut::new();
        buf.put_i64_raw(i);
        buf.freeze()
    }

    fn encode_bool(b: bool) -> Bytes {
        let mut buf = BytesMut::new();
        buf.put_bool_raw(b);
        buf.freeze()
    }

    fn encode_str(s: &str) -> Bytes {
        let mut buf = BytesMut::new();
        buf.put_str_raw(s);
        buf.freeze()
    }

    // -- i64 roundtrip --

    #[test]
    fn test_i64_roundtrip() {
        for val in [0i64, 1, -1, i64::MIN, i64::MAX, -1000, 1000, 42] {
            let mut bytes = encode_i64(val);
            assert_eq!(
                bytes.get_i64_raw().unwrap(),
                val,
                "roundtrip failed for {}",
                val
            );
        }
    }

    #[test]
    fn test_i64_eof() {
        let mut bytes = Bytes::from_static(&[0x00, 0x00]); // only 2 bytes, need 8
        assert!(matches!(
            bytes.get_i64_raw(),
            Err(DecodeError::UnexpectedEof)
        ));
    }

    #[test]
    fn test_i64_exact_size() {
        let mut bytes = encode_i64(42);
        assert_eq!(bytes.len(), 8);
        bytes.get_i64_raw().unwrap();
        assert!(bytes.is_empty());
    }

    // -- bool roundtrip --

    #[test]
    fn test_bool_roundtrip() {
        for val in [true, false] {
            let mut bytes = encode_bool(val);
            assert_eq!(bytes.get_bool_raw().unwrap(), val);
        }
    }

    #[test]
    fn test_bool_eof() {
        let mut bytes = Bytes::new();
        assert!(matches!(
            bytes.get_bool_raw(),
            Err(DecodeError::UnexpectedEof)
        ));
    }

    #[test]
    fn test_bool_exact_size() {
        let mut bytes = encode_bool(true);
        assert_eq!(bytes.len(), 1);
        bytes.get_bool_raw().unwrap();
        assert!(bytes.is_empty());
    }

    // -- string roundtrip --

    #[test]
    fn test_str_roundtrip() {
        for val in ["", "hello", "hello world", "unicode: ??"] {
            let mut bytes = encode_str(val);
            assert_eq!(
                bytes.get_str_raw().unwrap(),
                val,
                "roundtrip failed for {:?}",
                val
            );
        }
    }

    #[test]
    fn test_str_with_null_bytes() {
        // raw encoding is not null-escaped - null bytes are stored as-is
        let s = "hel\x00lo";
        let mut bytes = encode_str(s);
        assert_eq!(bytes.get_str_raw().unwrap(), s);
    }

    #[test]
    fn test_str_empty() {
        let mut bytes = encode_str("");
        assert_eq!(bytes.get_str_raw().unwrap(), "");
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_str_eof_in_length() {
        let mut bytes = Bytes::new();
        assert!(matches!(
            bytes.get_str_raw(),
            Err(DecodeError::DecodeVarintError)
        ));
    }

    #[test]
    fn test_str_eof_in_body() {
        // write a length varint claiming 100 bytes but provide none
        let mut buf = BytesMut::new();
        crate::encoding::varint::encode_varint(&mut buf, 100);
        // no actual string bytes follow
        let mut bytes = buf.freeze();
        assert!(matches!(
            bytes.get_str_raw(),
            Err(DecodeError::UnexpectedEof)
        ));
    }

    #[test]
    fn test_str_advances_cursor_correctly() {
        let mut buf = BytesMut::new();
        buf.put_str_raw("foo");
        buf.put_str_raw("bar");
        let mut bytes = buf.freeze();

        assert_eq!(bytes.get_str_raw().unwrap(), "foo");
        assert_eq!(bytes.get_str_raw().unwrap(), "bar");
        assert!(bytes.is_empty());
    }

    // -- note: raw i64 is NOT order-preserving --

    #[test]
    fn test_i64_raw_not_order_preserving() {
        // raw uses put_i64 (two's complement BE), NOT sign-bit-flipped
        // so -1 encodes as 0xFFFF... which sorts AFTER 0 - opposite of numeric order
        // this confirms raw != lexical
        assert!(encode_i64(-1) > encode_i64(0));
    }

    // -- mixed sequence --

    #[test]
    fn test_mixed_sequence() {
        let mut buf = BytesMut::new();
        buf.put_i64_raw(99);
        buf.put_bool_raw(false);
        buf.put_str_raw("tempest");
        buf.put_i64_raw(-1);
        buf.put_str_raw("");

        let mut bytes = buf.freeze();
        assert_eq!(bytes.get_i64_raw().unwrap(), 99);
        assert_eq!(bytes.get_bool_raw().unwrap(), false);
        assert_eq!(bytes.get_str_raw().unwrap(), "tempest");
        assert_eq!(bytes.get_i64_raw().unwrap(), -1);
        assert_eq!(bytes.get_str_raw().unwrap(), "");
        assert!(bytes.is_empty());
    }
}
