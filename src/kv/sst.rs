use zerocopy::{FromBytes, IntoBytes};

use crate::fio::FioFile;

#[repr(C, packed)]
#[derive(FromBytes, IntoBytes)]
pub(crate) struct SstFooter {
    /// The offset to the block index from the start of the SST file.
    index_handle_offset: u64,
    /// The size of the block index in bytes.
    index_handle_size: u32,
    /// Must always be equal to [`SST_MAGICNUM`].
    ///
    /// [`SST_MAGICNUM`]: crate::core::SST_MAGICNUM
    magic_number: u64,
}

pub(crate) struct SstReader<F: FioFile> {
    /// The file this reader is reading from.
    file: F,
    footer: SstFooter,
}
