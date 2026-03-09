use num_enum::TryFromPrimitiveError;
use tokio::sync::{mpsc, oneshot};

use crate::{
    StorageCommand,
    base::{KeyKind, SeqNum},
};

#[derive(Debug, Display, Error, From)]
pub enum StorageError {
    #[from(skip)]
    #[display("sequence number overflow: {_0} exceeds maximum allowed ({}).", SeqNum::MAX.get())]
    SeqNumOverflow(#[error(not(source))] u64),

    #[display("file number hard limit of 2^64 reached")]
    FileNumOverflow,

    #[display("i/o error: {}", _0)]
    IoError(std::io::Error),

    #[display("failed to encode: {}", _0)]
    BincodeError(bincode::Error),

    #[display("invalid key kind: {}", _0.number)]
    InvalidKeyKind(TryFromPrimitiveError<KeyKind>),

    #[display("invalid Varint: failed to decode.")]
    InvalidVarint,

    #[display("could not send storage command: channel closed")]
    StorageCommandSendError(mpsc::error::SendError<StorageCommand>),

    #[display("could not receive from oneshot channel: channel closed")]
    OneshotChannelRecvError(oneshot::error::RecvError),

    // TODO: specifically 'ManifestError'? -> only journal in this layer
    #[display("journal error: {}", _0)]
    JournalError(tempest_core::journal::JournalError),

    #[display("wal header corrupted: expected filenum {} but got {}", expected, got)]
    WalCorruption {
        expected: u64,
        got: u64
    },
}

pub type StorageResult<T> = Result<T, StorageError>;
