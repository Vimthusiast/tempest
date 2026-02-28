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
