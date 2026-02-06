use std::borrow::Cow;

use num_enum::TryFromPrimitive;

use crate::core::errors::TempestError;

/// Every Key will begin with a byte that declares a namespace.
#[derive(Debug, Clone, Copy, Display, TryFromPrimitive)]
#[repr(u8)]
pub enum NS {
    CATALOG = 0,
    DATA = 1,
}

/// A wrapper around the Rust strings that forces the string to not have any null-byte (`\0`).
#[derive(Debug, PartialEq, Eq, Deref)]
pub(crate) struct TempestStr<'a>(pub(in crate::core) Cow<'a, str>);

impl<'a> TempestStr<'a> {
    pub(crate) fn as_bytes(&'a self) -> &'a [u8] {
        self.0.as_bytes()
    }

    pub(crate) fn into_static(self) -> TempestStr<'static> {
        TempestStr(Cow::Owned(self.0.into_owned()))
    }
}

impl<'a> TryFrom<Cow<'a, str>> for TempestStr<'a> {
    type Error = TempestError;

    fn try_from(s: Cow<'a, str>) -> Result<Self, Self::Error> {
        if s.contains('\0') {
            return Err(TempestError::InvalidNullByte);
        }
        Ok(Self(s))
    }
}

impl<'a> Into<Cow<'a, str>> for TempestStr<'a> {
    fn into(self) -> Cow<'a, str> {
        self.0
    }
}

impl AsRef<[u8]> for TempestStr<'_> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<str> for TempestStr<'_> {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}
