#[derive(Debug, Display, Error, From)]
pub enum TempestError {
    #[display("I/O error: {}", _0)]
    IoError(std::io::Error),

    #[display("Failed to encode: {}", _0)]
    BincodeError(bincode::Error),
}
