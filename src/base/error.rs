use num_enum::TryFromPrimitiveError;
use tokio::sync::{mpsc, oneshot};

use crate::{
    base::{KeyKind, SeqNum},
    silo::SiloCommand,
};

#[derive(Debug, Display, Error, From)]
pub enum TempestError {
    #[from(skip)]
    #[display("sequence number overflow: {_0} exceeds maximum allowed ({}).", SeqNum::MAX.get())]
    SeqNumOverflow(#[error(not(source))] u64),

    #[display("file number hard limit of 2^64 reached")]
    FileNumOverflow,

    #[display("i/o error: {}", _0)]
    IoError(std::io::Error),

    #[display("failed to encode: {}", _0)]
    BincodeError(bincode::Error),

    #[display("{}", _0)]
    Other(#[error(not(source))] &'static str),

    #[display("invalid key kind: {}", _0.number)]
    InvalidKeyKind(TryFromPrimitiveError<KeyKind>),

    #[display("invalid Varint: failed to decode.")]
    InvalidVarint,

    #[display("could not send silo command: channel closed")]
    SiloCommandSendError(mpsc::error::SendError<SiloCommand>),

    #[display("could not receive from oneshot channel: channel closed")]
    OneshotChannelRecvError(oneshot::error::RecvError),
}

pub type TempestResult<T> = Result<T, TempestError>;
