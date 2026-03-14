use std::borrow::Cow;

use bytes::{Bytes, BytesMut};
use serde::{Deserialize, Serialize};
use strum::{EnumDiscriminants, EnumString};
use tempest_core::encoding::{
    BufGetLexicalExt, BufGetRawExt, BufPutLexicalExt, BufPutRawExt, LexicalDecodeError,
    RawDecodeError,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, EnumDiscriminants)]
#[strum_discriminants(
    name(TempestType),
    derive(Serialize, Deserialize, EnumString),
    strum(serialize_all = "PascalCase")
)]
#[repr(u8)]
pub enum TempestValue<'a> {
    Int64(i64) = 0,
    Bool(bool) = 1,
    String(Cow<'a, str>) = 2,
}

impl<'a> TempestValue<'a> {
    pub fn ty(&self) -> TempestType {
        match self {
            TempestValue::Int64(_) => TempestType::Int64,
            TempestValue::Bool(_) => TempestType::Bool,
            TempestValue::String(_) => TempestType::String,
        }
    }

    pub fn encode(&self, buf: &mut BytesMut) {
        match self {
            &TempestValue::Int64(i) => buf.put_i64_raw(i),
            &TempestValue::Bool(b) => buf.put_bool_raw(b),
            TempestValue::String(s) => buf.put_str_raw(s),
        }
    }

    pub fn decode(
        buf: &mut Bytes,
        ty: TempestType,
    ) -> Result<TempestValue<'static>, RawDecodeError> {
        match ty {
            TempestType::Int64 => buf.get_i64_raw().map(TempestValue::Int64),
            TempestType::Bool => buf.get_bool_raw().map(TempestValue::Bool),
            TempestType::String => buf
                .get_str_raw()
                .map(|s| TempestValue::String(Cow::Owned(s))),
        }
    }

    pub fn encode_lexical(&self, buf: &mut BytesMut) {
        match self {
            &TempestValue::Int64(i) => buf.put_i64_lexical(i),
            &TempestValue::Bool(b) => buf.put_bool_lexical(b),
            TempestValue::String(s) => buf.put_str_lexical(s),
        }
    }

    pub fn decode_lexical(
        buf: &mut Bytes,
        ty: TempestType,
    ) -> Result<TempestValue<'static>, LexicalDecodeError> {
        match ty {
            TempestType::Int64 => buf.get_i64_lexical().map(TempestValue::Int64),
            TempestType::Bool => buf.get_bool_lexical().map(TempestValue::Bool),
            TempestType::String => buf
                .get_str_lexical()
                .map(|s| TempestValue::String(Cow::Owned(s))),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use bytes::{Bytes, BytesMut};

    use super::*;

    // -- helpers --

    fn roundtrip(val: TempestValue<'_>) -> TempestValue<'static> {
        let ty = val.ty();
        let mut buf = BytesMut::new();
        val.encode(&mut buf);
        TempestValue::decode(&mut buf.freeze(), ty).unwrap()
    }

    fn roundtrip_lexical(val: TempestValue<'_>) -> TempestValue<'static> {
        let ty = val.ty();
        let mut buf = BytesMut::new();
        val.encode_lexical(&mut buf);
        TempestValue::decode_lexical(&mut buf.freeze(), ty).unwrap()
    }

    fn encode_lexical_bytes(val: TempestValue<'_>) -> Bytes {
        let mut buf = BytesMut::new();
        val.encode_lexical(&mut buf);
        buf.freeze()
    }

    // -- raw roundtrip --

    #[test]
    fn test_int64_roundtrip() {
        for val in [0i64, 1, -1, i64::MIN, i64::MAX, 42, -1000] {
            let result = roundtrip(TempestValue::Int64(val));
            assert_eq!(result, TempestValue::Int64(val));
        }
    }

    #[test]
    fn test_bool_roundtrip() {
        for val in [true, false] {
            let result = roundtrip(TempestValue::Bool(val));
            assert_eq!(result, TempestValue::Bool(val));
        }
    }

    #[test]
    fn test_string_roundtrip() {
        for val in ["", "hello", "tempest", "unicode: ??", "hel\x00lo"] {
            let result = roundtrip(TempestValue::String(Cow::Borrowed(val)));
            assert_eq!(result, TempestValue::String(Cow::Borrowed(val)));
        }
    }

    #[test]
    fn test_decode_returns_owned_string() {
        let result = roundtrip(TempestValue::String(Cow::Borrowed("hello")));
        if let TempestValue::String(cow) = result {
            assert!(
                matches!(cow, Cow::Owned(_)),
                "decoded string should be Cow::Owned"
            );
        } else {
            panic!("expected String variant");
        }
    }

    // -- lexical roundtrip --

    #[test]
    fn test_int64_lexical_roundtrip() {
        for val in [0i64, 1, -1, i64::MIN, i64::MAX, 42, -1000] {
            let result = roundtrip_lexical(TempestValue::Int64(val));
            assert_eq!(result, TempestValue::Int64(val));
        }
    }

    #[test]
    fn test_bool_lexical_roundtrip() {
        for val in [true, false] {
            let result = roundtrip_lexical(TempestValue::Bool(val));
            assert_eq!(result, TempestValue::Bool(val));
        }
    }

    #[test]
    fn test_string_lexical_roundtrip() {
        for val in ["", "hello", "tempest", "hel\x00lo", "\x00\x00\x00"] {
            let result = roundtrip_lexical(TempestValue::String(Cow::Borrowed(val)));
            assert_eq!(result, TempestValue::String(Cow::Borrowed(val)));
        }
    }

    // -- lexical ordering --

    #[test]
    fn test_int64_lexical_ordering() {
        let cases = [i64::MIN, -1000, -1, 0, 1, 1000, i64::MAX];
        for pair in cases.windows(2) {
            let (a, b) = (pair[0], pair[1]);
            assert!(
                encode_lexical_bytes(TempestValue::Int64(a))
                    < encode_lexical_bytes(TempestValue::Int64(b)),
                "{} should encode less than {}",
                a,
                b
            );
        }
    }

    #[test]
    fn test_bool_lexical_ordering() {
        assert!(
            encode_lexical_bytes(TempestValue::Bool(false))
                < encode_lexical_bytes(TempestValue::Bool(true))
        );
    }

    #[test]
    fn test_string_lexical_ordering() {
        let cases = ["", "a", "aa", "ab", "b", "z"];
        for pair in cases.windows(2) {
            let (a, b) = (pair[0], pair[1]);
            assert!(
                encode_lexical_bytes(TempestValue::String(Cow::Borrowed(a)))
                    < encode_lexical_bytes(TempestValue::String(Cow::Borrowed(b))),
                "{:?} should encode less than {:?}",
                a,
                b
            );
        }
    }

    // -- ty() --

    #[test]
    fn test_ty_returns_correct_discriminant() {
        assert_eq!(
            TempestValue::Int64(Default::default()).ty(),
            TempestType::Int64
        );
        assert_eq!(
            TempestValue::Bool(Default::default()).ty(),
            TempestType::Bool
        );
        assert_eq!(
            TempestValue::String(Default::default()).ty(),
            TempestType::String
        );
    }

    // -- raw vs lexical differ for i64 --

    #[test]
    fn test_raw_and_lexical_differ_for_negative_i64() {
        let val = TempestValue::Int64(-1);
        let mut raw_buf = BytesMut::new();
        let mut lex_buf = BytesMut::new();
        val.encode(&mut raw_buf);
        val.encode_lexical(&mut lex_buf);
        assert_ne!(
            raw_buf, lex_buf,
            "raw and lexical encodings of -1 must differ"
        );
    }

    // -- cursor advancement --

    #[test]
    fn test_decode_advances_cursor() {
        let mut buf = BytesMut::new();
        TempestValue::Int64(42).encode(&mut buf);
        TempestValue::Bool(true).encode(&mut buf);
        TempestValue::String(Cow::Borrowed("hi")).encode(&mut buf);

        let mut bytes = buf.freeze();
        assert_eq!(
            TempestValue::decode(&mut bytes, TempestType::Int64).unwrap(),
            TempestValue::Int64(42)
        );
        assert_eq!(
            TempestValue::decode(&mut bytes, TempestType::Bool).unwrap(),
            TempestValue::Bool(true)
        );
        assert_eq!(
            TempestValue::decode(&mut bytes, TempestType::String).unwrap(),
            TempestValue::String(Cow::Borrowed("hi"))
        );
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_decode_lexical_advances_cursor() {
        let mut buf = BytesMut::new();
        TempestValue::Int64(-99).encode_lexical(&mut buf);
        TempestValue::String(Cow::Borrowed("foo")).encode_lexical(&mut buf);
        TempestValue::Bool(false).encode_lexical(&mut buf);

        let mut bytes = buf.freeze();
        assert_eq!(
            TempestValue::decode_lexical(&mut bytes, TempestType::Int64).unwrap(),
            TempestValue::Int64(-99)
        );
        assert_eq!(
            TempestValue::decode_lexical(&mut bytes, TempestType::String).unwrap(),
            TempestValue::String(Cow::Borrowed("foo"))
        );
        assert_eq!(
            TempestValue::decode_lexical(&mut bytes, TempestType::Bool).unwrap(),
            TempestValue::Bool(false)
        );
        assert!(bytes.is_empty());
    }
}
