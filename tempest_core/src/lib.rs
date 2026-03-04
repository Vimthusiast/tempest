use bincode::Options as BincodeOptions;

#[macro_use]
extern crate tracing;

#[macro_use]
extern crate derive_more;

pub mod fio;
pub mod journal;
pub mod utils;

/// The project wide used [`bincode`] encoding options.
#[doc(hidden)]
pub fn bincode_options() -> impl BincodeOptions {
    bincode::options()
        // TODO: should we enfore this?
        .with_fixint_encoding() // no variable length ints, to ensure lower risk of errors
        .with_little_endian() // ensure consistency across platforms, enforcing little endian
        .allow_trailing_bytes() // important for decoding just parts of files, like in journals
}
