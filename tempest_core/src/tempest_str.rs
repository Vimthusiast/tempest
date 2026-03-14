use std::borrow::Cow;

use serde::{Deserialize, Serialize};

use crate::utils::contains_null;

/// Error returned when constructing a [`TempestStr`] from invalid input.
#[derive(Debug, Display, Error)]
pub enum TempestStrError {
    /// The input string contains a null byte (`\x00`), which is reserved
    /// for use as a key component terminator in the lexical encoding scheme.
    InputContainsNullByte,
}

/// A validated, potentially borrowed string for use as a Tempest identifier
/// (database name, table name, etc.).
///
/// Null bytes are rejected at construction time, since they are reserved as
/// terminators in the lexical key encoding scheme. This keeps the encoding
/// layer simple - identifier components can be written as raw bytes with no
/// escaping required.
///
/// Borrows the input when possible (`Cow::Borrowed`) to avoid unnecessary
/// allocations. Use [`into_owned`] to promote to a `'static` lifetime.
///
/// [`into_owned`]: TempestStr::into_owned
#[derive(
    Debug, Display, Clone, Deref, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct TempestStr<'a>(Cow<'a, str>);

impl<'a> TempestStr<'a> {
    /// Constructs a [`TempestStr`] borrowing from `s`.
    ///
    /// # Errors
    ///
    /// Returns [`TempestStrError::InputContainsNullByte`] if `s` contains a null byte.
    pub fn from_borrowed(s: &'a str) -> Result<TempestStr<'a>, TempestStrError> {
        if contains_null(s) {
            return Err(TempestStrError::InputContainsNullByte);
        }
        Ok(TempestStr(s.into()))
    }

    /// Constructs a [`TempestStr`] borrowing from `s`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `s` does not contain any null byte.
    pub const unsafe fn from_borrowed_unchecked(s: &'a str) -> TempestStr<'a> {
        Self(Cow::Borrowed(s))
    }

    /// Constructs a [`TempestStr`] from an owned [`String`], yielding a `'static` lifetime.
    ///
    /// # Errors
    ///
    /// Returns [`TempestStrError::InputContainsNullByte`] if `s` contains a null byte.
    pub fn from_owned(s: String) -> Result<TempestStr<'static>, TempestStrError> {
        if contains_null(&s) {
            return Err(TempestStrError::InputContainsNullByte);
        }
        Ok(TempestStr(s.into()))
    }

    /// Converts this [`TempestStr`] into an owned `'static` version, allocating
    /// if the inner value is currently borrowed. No-op if it is already owned.
    pub fn into_owned(self) -> TempestStr<'static> {
        TempestStr(self.0.into_owned().into())
    }
}

impl TryFrom<String> for TempestStr<'static> {
    type Error = TempestStrError;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        TempestStr::from_owned(s)
    }
}

// NB: this is for test helpers and internal use where input is known-safe.
// it is okay to panic, since the transform is deterministic and would always fail,
// which is a logic error on the programmers side - my side :P
impl From<&'static str> for TempestStr<'static> {
    fn from(s: &'static str) -> Self {
        TempestStr::from_borrowed(s).expect("static str contained null byte")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_valid(s: &str) {
        let ts = match TempestStr::from_borrowed(s) {
            Ok(ts) => ts,
            Err(e) => panic!("{} should be valid, but got error: {}", s, e),
        };
        assert_eq!(s, *ts);
    }

    fn assert_invalid(s: &str) {
        assert!(
            TempestStr::from_borrowed(s).is_err(),
            "{} should not be valid",
            s
        );
        assert!(
            TempestStr::from_owned(s.to_owned()).is_err(),
            "{} should not be valid, when converting into owned",
            s
        );
    }

    #[test]
    fn test_tempest_str_valid() {
        [
            "sup",
            "world",
            "", // empty should also be valid
            "tempest",
            "juice",
            "eventual consistency",
        ]
        .into_iter()
        .for_each(assert_valid);
    }

    #[test]
    fn test_tempest_str_invalid() {
        [
            "\x00",
            "\x00hello",
            "hel\x00lo",
            "hello\x00",
            "\x00\x00\x00",
        ]
        .into_iter()
        .for_each(assert_invalid);
    }

    #[test]
    fn test_into_owned_produces_static_lifetime() {
        let s = String::from("hello");
        let ts: TempestStr<'static> = TempestStr::from_owned(s).unwrap().into_owned();
        assert_eq!(*ts, "hello");
    }
}
