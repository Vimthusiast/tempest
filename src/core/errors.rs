use std::str::Utf8Error;

use num_enum::TryFromPrimitiveError;

use crate::core::{TempestStr, primitives::NS};

#[derive(Debug, Display, Error, From)]
pub enum DecodeError {
    #[display("Unexpected end of file.")]
    UnexpectedEof,
    /// `(bytes_left, decode_source)`
    /// Returned when `decode_source` should be exhausted, but still has `bytes_left` in it.
    #[display(
        "{} has {} bytes left after decoding, but should have been exhausted.",
        _1,
        _0
    )]
    RemainingBytes(
        #[error(not(source))] usize,
        #[error(not(source))] &'static str,
    ),
    #[display("UTF-8 Error: {}", _0)]
    Utf8Error(Utf8Error),
}

#[derive(Debug, Display, Error, From)]
pub enum TempestError {
    // -- Encoding/Decoding & Format Errors --
    #[display("Decode Error: {}", _0)]
    DecodeError(DecodeError),
    #[display("Invalid null-byte: Supplied string may not contain any null-bytes (\\0).")]
    InvalidNullByte,
    #[from(skip)]
    #[display("Invalid sequence number: {}", _0)]
    InvalidSeqNum(#[error(not(source))] u64),

    // -- Namespace Errors --
    #[display(
        "Invalid namespace: Expected to be within namespace {} ({}) but found namespace {} ({})",
        expected, *expected as u8, found, *found as u8,
    )]
    InvalidNamespace { expected: NS, found: NS },
    #[display("Unknown namespace: {}", _0.number)]
    UnknownNamespace(TryFromPrimitiveError<NS>),

    // -- I/O Errors --
    #[display("I/O Error: {}", _0)]
    IoError(std::io::Error),

    // -- Others (TODO) --
    #[from(skip)]
    #[display("A database with the name '{}' already exists.", _0)]
    DatabaseAlreadyExists(#[error(not(source))] TempestStr<'static>),
    #[from(skip)]
    #[display("A database with the name '{}' does not exist.", _0)]
    DatabaseNotFound(#[error(not(source))] TempestStr<'static>),
}
