use std::str::Utf8Error;

use num_enum::TryFromPrimitiveError;

use crate::core::primitives::NS;

#[derive(Debug, Display, Error, From)]
pub enum DecodeError {
    UnexpectedEof,
    Utf8Error(Utf8Error),
}

#[derive(Debug, Display, Error, From)]
pub enum TempestError {
    // -- Encoding/Decoding & Format Errors --
    #[display("Decode Error: {}", _0)]
    DecodeError(DecodeError),
    #[display("Invalid null-byte: Supplied string may not contain any null-bytes (\\0).")]
    InvalidNullByte,

    // -- Namespace Errors --
    #[display(
        "Invalid namespace: Expected to be within namespace {} ({}) but found namespace {} ({})",
        expected, *expected as u8, found, *found as u8,
    )]
    InvalidNamespace { expected: NS, found: NS },
    #[display("Unknown namespace: {}", _0.number)]
    UnknownNamespace(TryFromPrimitiveError<NS>),
}
