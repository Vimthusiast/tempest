use std::fmt;

/// Helper struct that wraps bytes and improves their [`std::fmt::Debug`] formatting.
/// Tries to print as many bytes as possible just like regular characters; others are escaped.
pub struct PrettyBytes<'a>(pub &'a [u8]);

impl fmt::Debug for PrettyBytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b\"")?;
        for &b in self.0 {
            match b {
                // human readable symbols, alphabet, etc
                b' '..b'~' => write!(f, "{}", b as char)?,
                // other bytes, like enter/backspace/newline
                _ => write!(f, "\\x{:02x}", b)?,
            }
        }
        write!(f, "\"")
    }
}

macro_rules! impl_hex {
    ($name:ident, $type:ty) => {
        impl_hex!($name, $type, $type);
    };
    ($name:ident, $type:ty, $unsigned:ty) => {
        pub struct $name(pub $type);

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    f,
                    "0x{:0>width$x}",
                    self.0 as $unsigned,
                    width = std::mem::size_of::<$type>() * 2
                )
            }
        }
    };
}

impl_hex!(HexU8, u8);
impl_hex!(HexU16, u16);
impl_hex!(HexU32, u32);
impl_hex!(HexU64, u64);
impl_hex!(HexI8, i8, u8);
impl_hex!(HexI16, i16, u16);
impl_hex!(HexI32, i32, u32);
impl_hex!(HexI64, i64, u64);
