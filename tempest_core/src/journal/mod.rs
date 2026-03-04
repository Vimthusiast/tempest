use std::{io, ops::Deref, path::PathBuf};

use bincode::Options;
use bytes::{BufMut, BytesMut};
use crc64::crc64;
use serde::{Serialize, de::DeserializeOwned};
use tokio_uring::buf::BoundedBuf;

use crate::{
    bincode_options,
    fio::{FioFS, FioFile},
};

pub const JOURNAL_MAGIC_NUM: &[u8; 8] = b"TMPSJRNL";

#[derive(Debug, Display, Error, From)]
pub enum JournalError {
    #[display("i/o error: {_0}")]
    Io(io::Error),

    #[display("i/o error: {_0}")]
    Encode(bincode::Error),

    #[display("journal record checksum mismatch: potential corruption")]
    Checksum,

    #[display("invalid magic number")]
    InvalidMagic,
}

const EDIT_PREFIX_SIZE: usize = 12;

struct EditPrefix {
    checksum: u64,
    len: u32,
}

impl EditPrefix {
    /// Creates a new `EditPrefix` for `data`, computing the checksum and length for framing it.
    /// The length of `data` may not be larger than `u32::MAX`.
    ///
    /// # Panics
    ///
    /// Panics if `data.len() > u32::MAX`.
    pub fn new(data: &[u8]) -> Self {
        assert!(
            data.len() <= u32::MAX as usize,
            "journal edits may not be larger than u32::MAX bytes"
        );
        let checksum = crc64(0, data);
        let len = data.len() as u32;
        let mut buf = [0u8; EDIT_PREFIX_SIZE];
        buf[0..8].copy_from_slice(&checksum.to_le_bytes());
        buf[8..12].copy_from_slice(&len.to_le_bytes());
        Self { checksum, len }
    }

    /// Encode this into bytes.
    pub fn encode(&self) -> [u8; EDIT_PREFIX_SIZE] {
        let mut buf = [0u8; EDIT_PREFIX_SIZE];
        buf[0..8].copy_from_slice(&self.checksum.to_le_bytes());
        buf[8..12].copy_from_slice(&self.len.to_le_bytes());
        buf
    }

    /// A helper function for `decode`, that converts the slice into a fixed length slice.
    /// The length of `buf` must be equal to `EDIT_PREFIX_SIZE`.
    ///
    /// # Panics
    ///
    /// Panics if `buf.len() != EDIT_PREFIX_SIZE`.
    pub fn decode_from_slice(buf: &[u8]) -> Self {
        assert_eq!(
            buf.len(),
            EDIT_PREFIX_SIZE,
            "could not decode EditPrefix: invalid slice length"
        );
        Self::decode(buf.try_into().unwrap())
    }

    pub fn decode(buf: &[u8; EDIT_PREFIX_SIZE]) -> Self {
        let checksum = u64::from_le_bytes(buf[0..8].try_into().unwrap());
        let len = u32::from_le_bytes(buf[8..12].try_into().unwrap());
        Self { checksum, len }
    }

    /// Returns the length of data this is framing.
    pub const fn len(&self) -> u32 {
        self.len
    }

    /// Checks if the data is valid, by comparing the checksum result with the stored checksum.
    /// The length of `data` must be equal to the stored length.
    ///
    /// # Panics
    ///
    /// Panics if `data.len() != self.len`.
    pub fn is_valid(&self, data: &[u8]) -> bool {
        assert_eq!(data.len(), self.len as usize);
        let computed = crc64(0, data);
        computed == self.checksum
    }
}

pub trait Replayable {
    /// This atomic edit is serialized into the journal for later
    /// reconstruction via sequential replay.
    type Edit: Serialize + DeserializeOwned;

    /// Apply another [`Self::Edit`] to the current state.
    fn apply(&mut self, edit: &Self::Edit);

    /// Calculate a new edit that can be used to reconstruct the current state.
    /// This is required to create the initial edit for file rotations.
    fn snapshot(&self) -> Self::Edit;

    /// This prefix is used to create new files for rotation internally.
    fn filename_prefix() -> &'static str;

    /// Separated from [`Default`], but usually has the same implementation,
    /// just as a semantic distinction.
    fn initial() -> Self;
}

pub struct Journal<T: Replayable, F: FioFS> {
    dir: PathBuf,
    current_filenum: u64,
    current_file: F::File,
    filepos: u64,
    scratch: Option<BytesMut>,
    state: T,
}

// TODO: journal config for file rotation conditions:
// - growth_baseline
// - growth_factor
// => threshold: max(baseline, factor)
impl<T: Replayable, F: FioFS> Journal<T, F> {
    pub async fn open(fs: F, dir: PathBuf) -> Result<Self, JournalError> {
        fs.create_dir_all(&dir).await?;
        // TODO: find newest journal file and replay, or initialize new journal file
        todo!()
    }

    pub async fn append(&mut self, edit: &T::Edit) -> Result<(), JournalError> {
        // serialize the edit into the scratch buffer
        let mut scratch = self.scratch.take().expect("scratch buffer exists");
        scratch.clear();
        if let Err(e) = bincode_options().serialize_into((&mut scratch).writer(), edit) {
            self.scratch = Some(scratch);
            return Err(e.into());
        }

        // write the scratch buffer to the file
        let (res, sliced_scratch) = self
            .current_file
            .write_all_at(scratch.slice(..), self.filepos)
            .await;
        self.scratch = Some(sliced_scratch.into_inner());
        if let Err(e) = res {
            return Err(e.into());
        }

        // apply the edit to memory
        self.state.apply(edit);

        Ok(())
    }

    pub async fn rotate(&mut self) -> Result<(), JournalError> {
        todo!("implement journal file rotations")
    }

    /// Retrieve the current state of the journals data.
    pub fn state(&self) -> &T {
        &self.state
    }
}

impl<T: Replayable, F: FioFS> Deref for Journal<T, F> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}
