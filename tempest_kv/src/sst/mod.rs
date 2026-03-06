use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, LittleEndian, U32, U64};

use crate::sst::bloom::BloomFilterFooter;

pub(crate) mod block;
pub(crate) mod bloom;
pub(crate) mod index;

pub(crate) mod reader;
pub(crate) mod writer;

#[cfg(test)]
mod tests;

#[derive(IntoBytes, FromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct SstFooter {
    magic: [u8; 8],
    bloom_offset: U64<LittleEndian>,
    bloom_size: U32<LittleEndian>,
    bloom_footer: BloomFilterFooter,
    index_offset: U64<LittleEndian>,
    index_size: U32<LittleEndian>,
}
