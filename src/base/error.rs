use num_enum::TryFromPrimitiveError;

use crate::base::{KeyKind, SeqNum};

#[derive(Debug, Display, Error, From)]
pub enum TempestError {
    #[from(skip)]
    #[display("Sequence number overflow: {_0} exceeds maximum allowed ({}).", SeqNum::MAX.get())]
    SeqNumOverflow(#[error(not(source))] u64),

    #[display("File number hard limit of 2^64 reached")]
    FileNumOverflow,

    #[display("I/O error: {}", _0)]
    IoError(std::io::Error),

    #[display("Failed to encode: {}", _0)]
    BincodeError(bincode::Error),

    #[display("Tempest error: {}", _0)]
    Other(#[error(not(source))] &'static str),

    #[display("Invalid key kind: {}", _0.number)]
    InvalidKeyKind(TryFromPrimitiveError<KeyKind>),

    #[display("Invalid Varint: Failed to decode.")]
    InvalidVarint,
}

pub type TempestResult<T> = Result<T, TempestError>;
