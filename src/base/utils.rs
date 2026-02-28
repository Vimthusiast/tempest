use std::fmt;

/// Helper struct that wraps a byte count and improves its [`std::fmt::Debug`] formatting.
/// Formats the value as a human-readable size, automatically selecting the most appropriate
/// unit (B, KiB, MiB, GiB, TiB). Trailing fractional zeros are omitted, and exact multiples
/// of a unit are printed without a decimal point entirely.
///
/// # Examples
///
/// ```
/// # use tempest::base::ByteSize;
/// assert_eq!(format!("{:?}", ByteSize(484)),        "484B");
/// assert_eq!(format!("{:?}", ByteSize(1536)),       "1.5KiB");
/// assert_eq!(format!("{:?}", ByteSize(2147483648)), "2GiB");
/// assert_eq!(format!("{:?}", ByteSize(2684354560)), "2.5GiB");
/// ```
pub struct ByteSize(pub u64);

impl fmt::Debug for ByteSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const KIB: u64 = 1024;
        const MIB: u64 = 1024 * KIB;
        const GIB: u64 = 1024 * MIB;
        const TIB: u64 = 1024 * GIB;

        macro_rules! fmt_unit {
            ($val:expr, $unit:expr, $unit_str:expr) => {{
                let whole = $val / $unit;
                let rem = $val % $unit;
                if rem == 0 {
                    write!(f, "{}{}", whole, $unit_str)
                } else {
                    // two decimal places via integer arithmetic:
                    // multiply remainder by 100, divide by unit to get 0-99
                    let frac = rem * 100 / $unit;
                    if frac % 10 == 0 {
                        // e.g. 1.50 -> 1.5
                        write!(f, "{}.{}{}", whole, frac / 10, $unit_str)
                    } else {
                        write!(f, "{}.{:02}{}", whole, frac, $unit_str)
                    }
                }
            }};
        }

        match self.0 {
            b if b >= TIB => fmt_unit!(b, TIB, "TiB"),
            b if b >= GIB => fmt_unit!(b, GIB, "GiB"),
            b if b >= MIB => fmt_unit!(b, MIB, "MiB"),
            b if b >= KIB => fmt_unit!(b, KIB, "KiB"),
            b => write!(f, "{}B", b),
        }
    }
}

/// Helper struct that wraps a byte slice and improves its [`std::fmt::Debug`] formatting.
/// Printable ASCII characters are rendered as-is; non-printable bytes are escaped as `\xNN`.
/// Matches the formatting convention of the [`bytes::Bytes`] type for consistency across logs.
///
/// # Examples
///
/// ```
/// # use tempest::base::PrettyBytes;
/// assert_eq!(format!("{:?}", PrettyBytes(b"key1")), "b\"key1\"");
/// assert_eq!(format!("{:?}", PrettyBytes(b"\x00\xFF")), "b\"\\x00\\xff\"");
/// ```
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
        #[doc = concat!(
                    "Helper struct that wraps a [`",
                    stringify!($type),
                    "`] and improves its [`std::fmt::Debug`] formatting. ",
                    "Formats the value as a zero-padded hexadecimal number with a `0x` prefix, ",
                    "padded to the full bit-width of [`",
                    stringify!($type),
                    "`]. ",
                    "Signed types are cast to their unsigned counterpart before formatting, ",
                    "giving the two's complement representation without a sign prefix.",
                )]
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
