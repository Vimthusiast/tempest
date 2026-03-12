use std::{
    io,
    ops::Deref,
    path::{Path, PathBuf},
};

use bincode::Options;
use bytes::{BufMut, BytesMut};
use crc64::crc64;
use futures::TryStreamExt;
use serde::{Serialize, de::DeserializeOwned};
use tokio_uring::buf::BoundedBuf;

use crate::{
    bincode_options,
    fio::{FioFS, FioFile},
    utils::{ByteSize, HexU64},
};

#[cfg(test)]
mod tests;

pub const JOURNAL_MAGIC_NUM: &[u8; 8] = b"TMPSJRNL";

#[derive(Debug, Display, Error, From)]
pub enum JournalError {
    #[display("i/o error: {_0}")]
    Io(io::Error),

    #[display("encode error: {_0}")]
    Encode(bincode::Error),

    #[display("journal checksum mismatch: potential corruption")]
    Checksum,

    #[display("invalid magic number")]
    InvalidMagic,
}

const JOURNAL_HEADER_SIZE: usize = 24;

#[derive(Debug)]
struct JournalHeader {
    filenum: u64,
}

impl JournalHeader {
    fn new(filenum: u64) -> Self {
        Self { filenum }
    }

    fn encode(&self) -> [u8; JOURNAL_HEADER_SIZE] {
        let mut buf = [0u8; JOURNAL_HEADER_SIZE];
        buf[0..8].copy_from_slice(JOURNAL_MAGIC_NUM);
        buf[8..16].copy_from_slice(&self.filenum.to_le_bytes());
        let checksum = crc64(0, &buf[0..16]);
        buf[16..24].copy_from_slice(&checksum.to_le_bytes());
        buf
    }

    /// A helper function for `decode`, that converts the slice into a fixed length slice.
    /// The length of `buf` must be equal to `EDIT_PREFIX_SIZE`.
    ///
    /// # Panics
    ///
    /// Panics if `buf.len() != EDIT_PREFIX_SIZE`.
    fn decode_from_slice(buf: &[u8]) -> Result<Self, JournalError> {
        assert_eq!(
            buf.len(),
            JOURNAL_HEADER_SIZE,
            "could not decode JournalHeader: invalid slice length"
        );
        Self::decode(buf.try_into().unwrap())
    }

    fn decode(buf: [u8; JOURNAL_HEADER_SIZE]) -> Result<Self, JournalError> {
        // validate magic num
        let magic_bytes = &buf[0..8];
        if magic_bytes != JOURNAL_MAGIC_NUM {
            return Err(JournalError::InvalidMagic);
        }

        // validate checksum
        let stored_checksum = u64::from_le_bytes(buf[16..24].try_into().unwrap());
        let computed_checksum = crc64(0, &buf[0..16]);
        if stored_checksum != computed_checksum {
            return Err(JournalError::Checksum);
        }

        // retrieve filenum
        let filenum = u64::from_le_bytes(buf[8..16].try_into().unwrap());
        Ok(Self { filenum })
    }
}

const EDIT_PREFIX_SIZE: usize = 12;

#[derive(Debug)]
struct EditPrefix {
    #[debug("{:?}", HexU64(*checksum))]
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

#[derive(Debug, Clone)]
#[debug("JournalConfig({:?} => {}x)", ByteSize(*growth_baseline), growth_factor)]
pub struct JournalConfig {
    pub growth_factor: f64,
    pub growth_baseline: u64,
}

impl Default for JournalConfig {
    fn default() -> Self {
        Self {
            growth_factor: 1.5,
            growth_baseline: 64 * 1024 * 1024,
        }
    }
}

pub trait Replayable {
    /// This atomic edit is serialized into the journal for later
    /// reconstruction via sequential replay.
    type Edit: Serialize + DeserializeOwned;

    /// Apply another [`Self::Edit`] to the current state.
    fn apply(&mut self, edit: Self::Edit);

    /// Calculate a new edit that can be used to reconstruct the current state.
    /// This is required to create the initial edit for file rotations.
    fn snapshot(&self) -> Self::Edit;

    /// This prefix is used to create new files for rotation internally.
    fn filename_prefix() -> &'static str;

    /// Separated from [`Default`], but usually has the same implementation,
    /// just as a semantic distinction.
    fn initial() -> Self;
}

#[derive(Debug)]
pub struct Journal<T: Replayable, F: FioFS> {
    // file access
    dir: PathBuf,
    fs: F,
    current_file: F::File,
    current_filepath: PathBuf,
    filepos: u64,

    // local state for file operations
    current_filenum: u64,
    initial_filesize: u64,
    scratch: Option<BytesMut>,

    // inner state that is managed
    state: T,

    // config
    config: JournalConfig,
}

// TODO: journal config for file rotation conditions:
// - growth_baseline
// - growth_factor
// => threshold: max(baseline, initial_filesize * factor)
impl<T: Replayable, F: FioFS> Journal<T, F> {
    fn filepath(dir: &Path, filenum: u64) -> PathBuf {
        dir.join(&format!("{}-{}", T::filename_prefix(), filenum))
    }

    // NB: Here we take a &mut BytesMut, instead of the take/put-back pattern, because this is a
    // static helper and we do not have any access to the inner fields of the Journal.
    fn write_edit(scratch: &mut BytesMut, edit: &T::Edit) -> Result<u64, JournalError> {
        // reserve space for the edit prefix
        scratch.put_bytes(0, EDIT_PREFIX_SIZE);

        // serialize the edit into the scratch buffer
        if let Err(e) = bincode_options().serialize_into(scratch.writer(), edit) {
            return Err(e.into());
        }

        // compute the edit prefix to frame the edit
        let prefix = EditPrefix::new(&scratch[EDIT_PREFIX_SIZE..]);
        scratch[..EDIT_PREFIX_SIZE].copy_from_slice(&prefix.encode());

        // return bytes written
        Ok(scratch.len() as u64)
    }

    #[instrument(skip(fs), level = "debug")]
    pub async fn open(fs: F, dir: PathBuf, config: JournalConfig) -> Result<Self, JournalError> {
        fs.create_dir_all(&dir).await?;
        let mut entries = fs.read_dir(&dir).await?;
        let mut scratch = BytesMut::with_capacity(4096);

        let mut journal_details = Vec::new();
        while let Some(entry) = entries.try_next().await? {
            let file = fs.opts().read(true).write(true).open(entry.path()).await?;

            scratch.resize(JOURNAL_HEADER_SIZE, 0);
            let (res, sliced_scratch) = file.read_exact_at(scratch.slice(..), 0).await;
            res?;
            scratch = sliced_scratch.into_inner();
            let header = match JournalHeader::decode_from_slice(&scratch) {
                Ok(h) => h,
                Err(e) => {
                    warn!("could not decode journal header: {}, skipping file", e);
                    continue;
                }
            };
            trace!(?header, "got journal file");
            journal_details.push((header, file, entry.path));
        }

        if !journal_details.is_empty() {
            trace!(
                "found {} journal files, getting latest",
                journal_details.len()
            );
            // sort by filenum (descending)
            journal_details.sort_by_key(|(h, _f, _p)| u64::MAX - h.filenum);
            let (header, current_file, current_filepath) =
                journal_details.into_iter().next().unwrap();
            let current_filenum = header.filenum;
            trace!(
                ?header,
                ?current_filepath,
                "starting to replay latest journal"
            );

            let mut filepos = JOURNAL_HEADER_SIZE as u64;
            let initial_filesize = current_file.size().await?;
            let mut state = T::initial();
            let mut had_error = false;
            while filepos < initial_filesize {
                let res;
                (res, scratch) = Self::read_edit(&current_file, filepos, scratch).await;
                match res {
                    Ok((edit, bytes_read)) => {
                        state.apply(edit);
                        filepos += bytes_read;
                    }
                    // i/o errors are fatal
                    Err(err @ JournalError::Io(_)) => {
                        error!(filepos=?HexU64(filepos), "failed to read journal edit: {}", err);
                        return Err(err);
                    }
                    // checksum mismatch: file corruption is recoverable
                    Err(err) => {
                        warn!(filepos=?HexU64(filepos), "failed to read journal edit: {}, skipping", err);
                        had_error = true;
                        break;
                    }
                }
            }

            let mut journal = Self {
                dir,
                fs,
                current_file,
                current_filepath,
                filepos,
                current_filenum,
                initial_filesize,
                scratch: Some(scratch),
                state,
                config,
            };

            if had_error {
                journal.rotate().await?;
            }

            return Ok(journal);
        }
        assert!(scratch.is_empty(), "scratch buffer not used yet");

        // create and initialize new journal file
        let current_filenum = 0u64;
        let header = JournalHeader::new(current_filenum);
        scratch.put_slice(&header.encode());
        let current_filepath = Self::filepath(&dir, current_filenum);
        let current_file = fs
            .opts()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&current_filepath)
            .await?;
        let (res, scratch) = current_file.write_all_at(scratch, 0).await;
        res?;
        current_file.sync_all().await?;

        let filepos = JOURNAL_HEADER_SIZE as u64;

        Ok(Self {
            dir,
            fs,
            current_file,
            current_filepath,
            filepos,

            current_filenum,
            initial_filesize: filepos,
            scratch: Some(scratch),

            state: T::initial(),

            config,
        })
    }

    #[instrument(skip(file, scratch), level = "trace")]
    async fn read_edit(
        file: &F::File,
        filepos: u64,
        mut scratch: BytesMut,
    ) -> (Result<(T::Edit, u64), JournalError>, BytesMut) {
        let mut current_filepos = filepos;
        scratch.clear();

        // read edit prefix
        scratch.resize(EDIT_PREFIX_SIZE, 0);
        let (res, sliced_scratch) = file.read_exact_at(scratch.slice(..), current_filepos).await;
        let mut scratch = sliced_scratch.into_inner();
        if let Err(e) = res {
            return (Err(e.into()), scratch);
        }
        current_filepos += EDIT_PREFIX_SIZE as u64;
        let prefix = EditPrefix::decode_from_slice(&scratch);
        trace!(current_filepos, ?prefix, "read edit prefix");

        // read edit body
        scratch.resize(prefix.len() as usize, 0);
        let (res, sliced_scratch) = file.read_exact_at(scratch.slice(..), current_filepos).await;
        let scratch = sliced_scratch.into_inner();
        if let Err(e) = res {
            return (Err(e.into()), scratch);
        }
        current_filepos += prefix.len() as u64;
        trace!("read edit body");

        // validate edit with crc64 checksum
        if !prefix.is_valid(&scratch) {
            return (Err(JournalError::Checksum), scratch);
        }
        trace!("validated edit body");

        // decode the edit
        let edit: T::Edit = match bincode_options().deserialize(&scratch) {
            Ok(e) => e,
            Err(e) => return (Err(e.into()), scratch),
        };
        trace!("parsed edit");

        let bytes_read = current_filepos - filepos;
        (Ok((edit, bytes_read)), scratch)
    }

    #[instrument(skip_all, fields(filesize=?ByteSize(self.filepos)), level = "trace")]
    pub async fn append(&mut self, edit: T::Edit) -> Result<(), JournalError> {
        let mut scratch = self.scratch.take().expect("scratch buffer exists");
        scratch.clear();

        // write the edit into the scratch buffer
        let edit_length = match Self::write_edit(&mut scratch, &edit) {
            Ok(len) => len,
            Err(err) => {
                self.scratch = Some(scratch);
                return Err(err);
            }
        };

        // write the scratch buffer to the file
        let (res, scratch) = self.current_file.write_all_at(scratch, self.filepos).await;
        self.scratch = Some(scratch);
        if let Err(e) = res {
            return Err(e.into());
        }
        self.filepos += edit_length;
        self.current_file.sync_all().await?;
        trace!(edit_length = ?ByteSize(edit_length), "wrote edit to file");

        // apply the edit to memory
        self.state.apply(edit);

        self.maybe_rotate().await?;

        Ok(())
    }

    async fn maybe_rotate(&mut self) -> Result<(), JournalError> {
        let factored_filesize = (self.initial_filesize as f64 * self.config.growth_factor) as u64;
        if self.filepos >= u64::max(self.config.growth_baseline, factored_filesize) {
            self.rotate().await?;
        }
        Ok(())
    }

    #[instrument(skip(self), fields(filesize=?ByteSize(self.filepos)))]
    async fn rotate(&mut self) -> Result<(), JournalError> {
        // open a new file
        let filenum = self.current_filenum + 1;
        let filepath = Self::filepath(&self.dir, filenum);
        let file = self
            .fs
            .opts()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&filepath)
            .await?;

        let mut scratch = self.scratch.take().expect("scratch buffer exists");
        scratch.clear();
        let snapshot = self.snapshot();
        let edit_len = match Self::write_edit(&mut scratch, &snapshot) {
            Ok(len) => len,
            Err(e) => {
                self.scratch = Some(scratch);
                return Err(e);
            }
        };

        // NB: We write the snapshot but leave space for header. We write the header afterwards, to
        // prevent this file from being read when writing the snapshot fails for example.
        let (res, mut scratch) = file.write_all_at(scratch, JOURNAL_HEADER_SIZE as u64).await;
        if let Err(e) = res {
            self.scratch = Some(scratch);
            return Err(e.into());
        }
        trace!("wrote snapshot");

        scratch.clear();
        let header = JournalHeader::new(filenum);
        scratch.put_slice(&header.encode());
        let (res, scratch) = file.write_all_at(scratch, 0).await;
        self.scratch = Some(scratch);
        res?;
        trace!("wrote header");

        self.current_file = file;
        self.current_filepath = filepath;
        self.current_filenum = filenum;
        self.filepos = JOURNAL_HEADER_SIZE as u64 + edit_len;
        self.initial_filesize = self.filepos;

        trace!(
            filesize = ?ByteSize(self.initial_filesize), filepath=?self.current_filepath,
            filenum = self.current_filenum, "finished journal file rotation"
        );
        Ok(())
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
