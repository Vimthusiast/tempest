use std::string::FromUtf8Error;

use bytes::{Buf, BufMut, Bytes, BytesMut};

pub trait BufPutLexicalExt {
    fn put_i64_lexical(&mut self, i: i64);
    fn put_bool_lexical(&mut self, b: bool);
    fn put_str_lexical(&mut self, s: &str);
}

impl BufPutLexicalExt for BytesMut {
    fn put_i64_lexical(&mut self, i: i64) {
        self.put_u64((i ^ i64::MIN) as u64);
    }

    fn put_bool_lexical(&mut self, b: bool) {
        self.put_u8(b as u8);
    }

    fn put_str_lexical(&mut self, s: &str) {
        for &c in s.as_bytes() {
            match c {
                0x00 => self.put_slice(&[0x00, 0xFF]),
                _ => self.put_u8(c),
            }
        }
        self.put_slice(&[0x00, 0x00]);
    }
}

#[derive(Debug, Display, Error, From)]
pub enum LexicalDecodeError {
    UnexpectedEof,
    FromUtf8Error(FromUtf8Error),
}

pub trait BufGetLexicalExt {
    fn get_i64_lexical(&mut self) -> Result<i64, LexicalDecodeError>;
    fn get_bool_lexical(&mut self) -> Result<bool, LexicalDecodeError>;
    fn get_str_lexical(&mut self) -> Result<String, LexicalDecodeError>;
}

impl BufGetLexicalExt for Bytes {
    fn get_i64_lexical(&mut self) -> Result<i64, LexicalDecodeError> {
        if self.len() < 8 {
            return Err(LexicalDecodeError::UnexpectedEof);
        }
        Ok((self.get_u64() as i64) ^ i64::MIN)
    }

    fn get_bool_lexical(&mut self) -> Result<bool, LexicalDecodeError> {
        if self.is_empty() {
            return Err(LexicalDecodeError::UnexpectedEof);
        }
        Ok(self.get_u8() != 0)
    }

    fn get_str_lexical(&mut self) -> Result<String, LexicalDecodeError> {
        let mut pos = 0;
        let mut result = Vec::with_capacity(64);
        while pos + 1 < self.len() {
            match (self[pos], self[pos + 1]) {
                (0x00, 0x00) => {
                    self.advance(pos + 2);
                    return String::from_utf8(result).map_err(LexicalDecodeError::FromUtf8Error);
                }
                (0x00, 0xFF) => {
                    result.push(0);
                    pos += 2;
                }
                (c, _) => {
                    // NB: silently recover orphan null bytes
                    result.push(c);
                    pos += 1;
                }
            }
        }
        Err(LexicalDecodeError::UnexpectedEof)
    }
}

#[cfg(test)]
mod tests {
    use bytes::{Bytes, BytesMut};

    use super::*;

    // -- helpers --

    fn encode_i64(i: i64) -> Bytes {
        let mut buf = BytesMut::new();
        buf.put_i64_lexical(i);
        buf.freeze()
    }

    fn encode_bool(b: bool) -> Bytes {
        let mut buf = BytesMut::new();
        buf.put_bool_lexical(b);
        buf.freeze()
    }

    fn encode_str(s: &str) -> Bytes {
        let mut buf = BytesMut::new();
        buf.put_str_lexical(s);
        buf.freeze()
    }

    // -- i64 round-trip --

    #[test]
    fn test_i64_roundtrip() {
        for val in [0i64, 1, -1, i64::MIN, i64::MAX, -1000, 1000, 42] {
            let mut bytes = encode_i64(val);
            assert_eq!(
                bytes.get_i64_lexical().unwrap(),
                val,
                "roundtrip failed for {}",
                val
            );
        }
    }

    #[test]
    fn test_i64_ordering() {
        let cases = [i64::MIN, -1000, -1, 0, 1, 1000, i64::MAX];
        for pair in cases.windows(2) {
            let (a, b) = (pair[0], pair[1]);
            assert!(
                encode_i64(a) < encode_i64(b),
                "{} should encode less than {}",
                a,
                b
            );
        }
    }

    #[test]
    fn test_i64_eof() {
        let mut bytes = Bytes::from_static(&[0x00, 0x00]); // only 2 bytes, need 8
        assert!(matches!(
            bytes.get_i64_lexical(),
            Err(LexicalDecodeError::UnexpectedEof)
        ));
    }

    // -- bool round-trip --

    #[test]
    fn test_bool_roundtrip() {
        for val in [true, false] {
            let mut bytes = encode_bool(val);
            assert_eq!(bytes.get_bool_lexical().unwrap(), val);
        }
    }

    #[test]
    fn test_bool_ordering() {
        assert!(encode_bool(false) < encode_bool(true));
    }

    #[test]
    fn test_bool_eof() {
        let mut bytes = Bytes::new();
        assert!(matches!(
            bytes.get_bool_lexical(),
            Err(LexicalDecodeError::UnexpectedEof)
        ));
    }

    // -- string round-trip --

    #[test]
    fn test_str_roundtrip() {
        for val in ["", "hello", "hello world", "unicode: ??"] {
            let mut bytes = encode_str(val);
            assert_eq!(
                bytes.get_str_lexical().unwrap(),
                val,
                "roundtrip failed for {:?}",
                val
            );
        }
    }

    #[test]
    fn test_str_with_null_bytes() {
        let s = "hel\x00lo";
        let mut bytes = encode_str(s);
        assert_eq!(bytes.get_str_lexical().unwrap(), s);
    }

    #[test]
    fn test_str_all_null_bytes() {
        let s = "\x00\x00\x00";
        let mut bytes = encode_str(s);
        assert_eq!(bytes.get_str_lexical().unwrap(), s);
    }

    #[test]
    fn test_str_ordering() {
        let cases = ["", "a", "aa", "ab", "b", "z"];
        for pair in cases.windows(2) {
            let (a, b) = (pair[0], pair[1]);
            assert!(
                encode_str(a) < encode_str(b),
                "{:?} should encode less than {:?}",
                a,
                b
            );
        }
    }

    #[test]
    fn test_str_null_byte_ordering() {
        // "\x00" < "a" lexicographically in the original string,
        // and must remain so after encoding
        assert!(encode_str("\x00") < encode_str("a"));
        assert!(encode_str("a\x00b") < encode_str("a\x01b"));
    }

    #[test]
    fn test_str_eof_no_terminator() {
        // raw bytes with no \x00\x00 terminator
        let mut bytes = Bytes::from_static(b"hello");
        assert!(matches!(
            bytes.get_str_lexical(),
            Err(LexicalDecodeError::UnexpectedEof)
        ));
    }

    #[test]
    fn test_str_advances_cursor_correctly() {
        // two strings back to back - cursor must land exactly after first terminator
        let mut buf = BytesMut::new();
        buf.put_str_lexical("foo");
        buf.put_str_lexical("bar");
        let mut bytes = buf.freeze();

        assert_eq!(bytes.get_str_lexical().unwrap(), "foo");
        assert_eq!(bytes.get_str_lexical().unwrap(), "bar");
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_mixed_sequence() {
        // encode a mix of types and decode them back in order
        let mut buf = BytesMut::new();
        buf.put_i64_lexical(-42);
        buf.put_bool_lexical(true);
        buf.put_str_lexical("tempest");
        buf.put_i64_lexical(i64::MAX);

        let mut bytes = buf.freeze();
        assert_eq!(bytes.get_i64_lexical().unwrap(), -42);
        assert_eq!(bytes.get_bool_lexical().unwrap(), true);
        assert_eq!(bytes.get_str_lexical().unwrap(), "tempest");
        assert_eq!(bytes.get_i64_lexical().unwrap(), i64::MAX);
        assert!(bytes.is_empty());
    }
}
