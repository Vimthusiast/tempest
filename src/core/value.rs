use strum::EnumDiscriminants;

use crate::core::{DecodeError, TempestReader, TempestWriter};

#[derive(Debug, Clone, PartialEq, EnumDiscriminants)]
#[strum_discriminants(name(TempestType))]
#[repr(u8)]
pub(crate) enum TempestValue {
    Bool(bool) = 0,
    Int8(i64) = 1,
}

impl TempestValue {
    pub(crate) fn encode_lexic<W: TempestWriter>(&self, writer: &mut W) {
        match self {
            &TempestValue::Bool(b) => writer.write_bool(b),
            &TempestValue::Int8(i) => writer.write_i64_lexic(i),
        }
    }

    pub(crate) fn decode_lexic<'a, R: TempestReader<'a>>(
        reader: &mut R,
        expected: TempestType,
    ) -> Result<TempestValue, DecodeError> {
        match expected {
            TempestType::Bool => Ok(TempestValue::Bool(reader.read_bool()?)),
            TempestType::Int8 => Ok(TempestValue::Int8(reader.read_i64_lexic()?)),
        }
    }

    pub(crate) fn encode<W: TempestWriter>(&self, writer: &mut W) {
        match self {
            &TempestValue::Bool(b) => writer.write_bool(b),
            &TempestValue::Int8(i) => writer.write_bytes(&i.to_be_bytes()),
        }
    }

    pub(crate) fn decode<'a, R: TempestReader<'a>>(
        reader: &mut R,
        expected: TempestType,
    ) -> Result<TempestValue, DecodeError> {
        match expected {
            TempestType::Bool => Ok(TempestValue::Bool(reader.read_bool()?)),
            TempestType::Int8 => Ok(TempestValue::Int8(reader.read_i64()?)),
        }
    }
}
