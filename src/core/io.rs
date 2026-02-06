use std::borrow::Cow;

use crate::core::{
    encoding::{
        decode_f64_sortable, decode_i64_sortable, encode_f64_sortable, encode_i64_sortable,
    },
    errors::DecodeError,
    primitives::TempestStr,
};

/// The internal trait for any buffer that can be read from.
/// For an implementation, see [`SliceReader`].
///
/// [`SliceReader`]: crate::core::SliceReader
pub(crate) trait TempestReader<'a> {
    /// Returns the total length of the byte sequence from the reader.
    fn len(&self) -> usize;

    /// Returns the current position of the reader.
    fn position(&self) -> usize;

    /// Returns how many bytes the reader has left.
    fn bytes_left(&self) -> usize {
        self.len() - self.position()
    }

    /// Returns true, if the reader has reached the EOF.
    fn is_eof(&self) -> bool {
        self.bytes_left() == 0
    }

    /// Looks at the next byte without advancing the reader.
    fn peek(&self) -> Result<u8, DecodeError>;

    /// Return the remaining bytes without advancing the reader.
    fn remaining(&self) -> &'a [u8];

    /// Reads the remaining bytes and advances the reader.
    fn read_remaining(&mut self) -> &'a [u8];

    /// Advances the reader by `len` bytes.
    fn advance(&mut self, len: usize) -> Result<(), DecodeError>;

    /// Looks at the next byte and advances the reader.
    fn read_u8(&mut self) -> Result<u8, DecodeError>;

    /// Reads a specified length of `len` bytes, if the reader still has that many bytes left.
    fn read_slice(&mut self, len: usize) -> Result<&'a [u8], DecodeError> {
        self.read_slice_from(self.position(), len)
    }

    /// Reads a specified length of `len` bytes, starting from the byte position `start`.
    fn read_slice_from(&mut self, start: usize, len: usize) -> Result<&'a [u8], DecodeError>;

    /// Reads until the predicate `f` is met, returning the slice which was advanced over.
    /// This should error when encountering the EOF without stopping, so `f` has to check that too.
    fn read_while<F>(&mut self, mut f: F) -> Result<&'a [u8], DecodeError>
    where
        F: FnMut(u8) -> bool,
    {
        let start = self.position();
        while f(self.peek()?) {
            self.advance(1)?;
        }
        let len = self.position() - start;
        self.read_slice_from(start, len)
    }

    /// The closure receives the remaining buffer and returns `Some(bytes_to_consume)` to continue,
    /// or `None` to stop.
    fn read_window_while<F>(&mut self, mut f: F) -> Result<&'a [u8], DecodeError>
    where
        F: FnMut(&'a [u8]) -> Option<usize>,
    {
        let start = self.position();
        while let Some(consume_len) = f(self.remaining()) {
            self.advance(consume_len)?;
        }
        let total_len = self.position() - start;
        self.read_slice_from(start, total_len)
    }

    fn read_i64_sortable(&mut self) -> Result<i64, DecodeError> {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(self.read_slice(8)?);
        Ok(decode_i64_sortable(bytes))
    }

    fn read_f64_sortable(&mut self) -> Result<f64, DecodeError> {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(self.read_slice(8)?);
        Ok(decode_f64_sortable(bytes))
    }

    /// Reads a null-termianted string from a buffer, advancing the slice past it.
    fn read_string_null_terminated(&mut self) -> Result<TempestStr<'a>, DecodeError> {
        let bytes = self.read_while(|b| b != 0)?;
        let null_term = self.read_u8()?;
        debug_assert_eq!(null_term, 0);
        let s = str::from_utf8(bytes)?;
        Ok(TempestStr(Cow::Borrowed(s)))
    }

    /// Decodes a null-terminated byte sequence that may contain escaped null bytes.
    ///
    /// This function is designed for a specific escaping scheme where:
    /// * `[0x00, 0x00]` acts as the sequence terminator.
    /// * `[0x00, 0xFF]` represents a single literal null byte (`0x00`) within the data.
    /// * Any other byte sequence is treated literally (silent resilience), i.e. returns no error
    ///   when encountering an orphan null-byte (`[0x00, x]`, where x is neither 0x00 nor 0xFF).
    ///
    /// # Returns
    /// * `Ok(Cow::Borrowed)` if the sequence contains no escape characters (`0x00 0xFF`),
    ///   allowing for zero-copy access to the underlying buffer.
    /// * `Ok(Cow::Owned)` if the sequence contains escapes, returning a new vector with
    ///   the `0xFF` escape bytes removed.
    /// * `Err(DecodeError::UnexpectedEof)` if the buffer ends before a `[0x00, 0x00]`
    ///   terminator is found.
    ///
    /// # Performance
    /// This method performs a single pass to locate the terminator and detect escapes.
    /// A second pass (allocation) only occurs if internal null bytes were actually escaped.
    fn decode_bytes_null_terminated_escaped(&mut self) -> Result<Cow<'a, [u8]>, DecodeError> {
        let mut has_escapes = false;
        let raw_slice = self.read_window_while(|window| {
            match window {
                [0, 0, ..] => None,
                [0, 0xFF, ..] => {
                    has_escapes = true;
                    Some(2)
                }
                [_, ..] => Some(1),
                // errors when no \0\0 is found
                [] => Some(1),
            }
        })?;

        // consume the terminator
        self.advance(2)?;

        if !has_escapes {
            Ok(Cow::Borrowed(raw_slice))
        } else {
            let mut decoded = Vec::with_capacity(raw_slice.len());
            let mut i = 0;
            while i < raw_slice.len() {
                decoded.push(raw_slice[i]);
                if raw_slice[i] == 0 && i + 1 < raw_slice.len() && raw_slice[i + 1] == 0xFF {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            Ok(Cow::Owned(decoded))
        }
    }
}

/// An implementation of the [`TempestReader`] trait over a byte-slice.
pub(crate) struct SliceReader<'a> {
    slice: &'a [u8],
    position: usize,
}

impl SliceReader<'_> {
    pub(crate) fn new<'a>(slice: &'a [u8]) -> SliceReader<'a> {
        SliceReader { slice, position: 0 }
    }
}

impl<'a> TempestReader<'a> for SliceReader<'a> {
    fn len(&self) -> usize {
        self.slice.len()
    }

    fn position(&self) -> usize {
        self.position
    }

    fn peek(&self) -> Result<u8, DecodeError> {
        if !self.is_eof() {
            Ok(self.slice[self.position])
        } else {
            Err(DecodeError::UnexpectedEof)
        }
    }

    fn remaining(&self) -> &'a [u8] {
        &self.slice[self.position..]
    }

    fn read_remaining(&mut self) -> &'a [u8] {
        let slice = &self.slice[self.position..];
        self.position = self.slice.len();
        slice
    }

    fn advance(&mut self, len: usize) -> Result<(), DecodeError> {
        if self.position + len > self.slice.len() {
            Err(DecodeError::UnexpectedEof)
        } else {
            self.position += len;
            Ok(())
        }
    }

    fn read_u8(&mut self) -> Result<u8, DecodeError> {
        if !self.is_eof() {
            let byte = self.slice[self.position];
            self.position += 1;
            Ok(byte)
        } else {
            Err(DecodeError::UnexpectedEof)
        }
    }

    fn read_slice_from(&mut self, start: usize, len: usize) -> Result<&'a [u8], DecodeError> {
        let end = start + len;
        if end > self.slice.len() {
            Err(DecodeError::UnexpectedEof)
        } else {
            Ok(&self.slice[start..end])
        }
    }
}

/// The internal trait for any buffer that can be written to.
/// An implementation is provided for `Vec<u8>`.
pub(crate) trait TempestWriter {
    /// Return how many bytes were written so far by the writer.
    fn position(&self) -> usize;

    /// Reserves capacity for at least `additional` more elements in the internal buffer.
    /// This useful for performance optimizations, to reduce the number of reallocations.
    fn reserve(&mut self, additional: usize);

    /// Writes a single byte.
    fn write_u8(&mut self, val: u8);

    /// Writes a slice of bytes.
    fn write_bytes(&mut self, bytes: &[u8]);

    fn write_i64_sortable(&mut self, val: i64) {
        self.write_bytes(&encode_i64_sortable(val));
    }

    fn write_f64_sortable(&mut self, val: f64) {
        self.write_bytes(&encode_f64_sortable(val));
    }

    /// Encodes a null-terminated [`TempestStr`] into the buffer.
    ///
    /// [`TempestStr`]: crate::core::TempestStr
    fn write_string_null_terminated(&mut self, s: &TempestStr<'_>) {
        let bytes = s.as_bytes();
        for (pos, &b) in bytes.iter().enumerate() {
            debug_assert_ne!(b, 0u8, "string contains null-byte at position {}", pos)
        }
        self.write_bytes(bytes);
        self.write_u8(0);
    }

    /// Encodes a null-terminated byte sequence into a buffer. The string may contain null bytes,
    /// at the cost of potentially increased encoded size.
    /// Most often (without \0 occurances), for strings the size will be `s.len() + 2`; this knowledge
    /// may be used for preallocating the buffer to fit this amount of bytes.
    fn encode_bytes_null_terminated_escaped(&mut self, bytes: &[u8]) {
        for &b in bytes {
            if b == 0 {
                // null bytes within get escaped by being followed with a \xff
                self.write_u8(0x00);
                self.write_u8(0xFF);
            } else {
                self.write_u8(b);
            }
        }
        // double null-byte \0\0 is the new escape sequence
        self.write_u8(0x00);
        self.write_u8(0x00);
    }
}

impl TempestWriter for Vec<u8> {
    fn position(&self) -> usize {
        self.len()
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    fn write_u8(&mut self, val: u8) {
        self.push(val);
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.extend_from_slice(bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tempest_reader_writer() {
        let strings_with_nulls = [
            "Hey,\0what's\0up?\0:)",
            "Apples\0and\0Oranges\0with\0null\0at\0the\0end",
            "A string without nulls that is read quite fast and without an additional allocation",
        ];

        let mut buf = Vec::new();
        for s in strings_with_nulls {
            buf.encode_bytes_null_terminated_escaped(s.as_bytes());
        }

        let mut slice_reader: SliceReader<'_> = SliceReader::new(&buf);
        let mut i = 0;
        while i < strings_with_nulls.len() {
            let decoded = slice_reader.decode_bytes_null_terminated_escaped().unwrap();
            assert_eq!(&decoded, &strings_with_nulls[i].as_bytes());
            i += 1;
        }
        assert!(
            slice_reader.is_eof(),
            "reader should have reached end of byte sequence"
        );

        // (value, expected, is_owned)
        let encoded_cases = [
            // orphan case: a null-byte not followed by \xFF is recovered silently
            ("\x01\0\x02\0\0".as_ref(), "\x01\0\x02", false),
            // empty case
            ("\0\0".as_ref(), "", false),
            // cloned cow case
            ([0, 0xFF, 0x42, 0, 0xFF, 0, 0].as_ref(), "\0B\0", true),
        ];

        let buf: Vec<_> = encoded_cases
            .iter()
            .map(|(value, _expected, _borrowed)| *value)
            .flatten()
            .copied()
            .collect();
        let mut slice_reader = SliceReader::new(&buf);
        let mut i = 0;
        while i < encoded_cases.len() {
            let (_, expected, owned) = encoded_cases[i];
            let decoded = slice_reader.decode_bytes_null_terminated_escaped().unwrap();
            assert_eq!(decoded, expected.as_bytes());
            assert_eq!(matches!(decoded, Cow::Owned(_)), owned);
            i += 1;
        }
        assert!(
            slice_reader.is_eof(),
            "reader should have reached end of byte sequence"
        )
    }
}
