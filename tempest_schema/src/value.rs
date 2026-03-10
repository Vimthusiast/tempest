use std::borrow::Cow;

use bytes::{Bytes, BytesMut};
use tempest_core::encoding::{
    BufGetLexicalExt, BufGetRawExt, BufPutLexicalExt, BufPutRawExt, DecodeError, LexicalDecodeError,
};

#[derive(Debug, strum::EnumDiscriminants)]
#[strum_discriminants(name(TempestType))]
#[repr(u8)]
pub enum TempestValue<'a> {
    Int64(i64) = 0,
    Bool(bool) = 1,
    String(Cow<'a, str>) = 2,
}

impl<'a> TempestValue<'a> {
    pub fn encode(&self, buf: &mut BytesMut) {
        match self {
            &TempestValue::Int64(i) => buf.put_i64_raw(i),
            &TempestValue::Bool(b) => buf.put_bool_raw(b),
            TempestValue::String(s) => buf.put_str_raw(s),
        }
    }

    pub fn decode(buf: &mut Bytes, ty: TempestType) -> Result<TempestValue<'static>, DecodeError> {
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
