use std::{io, marker::PhantomData};

use bytes::{Bytes, BytesMut};
use tokio_uring::buf::BoundedBuf;
use zerocopy::FromBytes;

use crate::{
    base::{Comparer, InternalKey, SST_MAGICNUM, TempestResult},
    fio::FioFile,
    silo::sst::{SstFooter, block::BlockReader, bloom::BloomFilter, index::IndexReader},
};

pub struct SstReader<F: FioFile, C: Comparer> {
    file: F,
    bloom: BloomFilter,
    index: IndexReader<C>,
    _marker: PhantomData<C>,
}

impl<F: FioFile, C: Comparer> SstReader<F, C> {
    pub async fn open(file: F) -> TempestResult<Self> {
        // read footer
        let file_size = file.size().await?;
        let footer_offset = file_size - size_of::<SstFooter>() as u64;
        let footer_buf = BytesMut::zeroed(size_of::<SstFooter>());
        let (res, footer_buf) = file
            .read_exact_at(footer_buf.slice(..), footer_offset)
            .await;
        res?;
        let footer = SstFooter::read_from_bytes(&footer_buf).unwrap();

        // verify magic
        if &footer.magic != SST_MAGICNUM {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "invalid magic number: not an sst file. expected {:?} but got {:?}.",
                    SST_MAGICNUM, footer.magic
                ),
            )
            .into());
        }

        // read bloom filter bits
        let bloom_buf = BytesMut::zeroed(footer.bloom_size.get() as usize);
        let (res, bloom_buf) = file
            .read_exact_at(bloom_buf.slice(..), footer.bloom_offset.get())
            .await;
        res?;
        let bloom_buf = bloom_buf.into_inner();
        let bloom = BloomFilter::from_parts(bloom_buf.freeze(), footer.bloom_footer);

        // read index
        let index_buf = BytesMut::zeroed(footer.index_size.get() as usize);
        let (res, index_buf) = file
            .read_exact_at(index_buf.slice(..), footer.index_offset.get())
            .await;
        res?;
        let index_buf = index_buf.into_inner();
        let index = IndexReader::new(index_buf.freeze());

        Ok(Self {
            file,
            bloom,
            index,
            _marker: PhantomData,
        })
    }

    pub async fn get<K: AsRef<[u8]>>(
        &self,
        key: &InternalKey<C, K>,
    ) -> TempestResult<Option<Bytes>> {
        // check bloom filter first - if definitely not present, skip
        let c = C::default();
        let (prefix, _) = c.split_up(key.key().as_ref());
        if !self.bloom.maybe_contains(prefix) {
            return Ok(None);
        }

        // find the block that may contain this key
        let Some((block_offset, block_size)) = self.index.get_block_for(key) else {
            return Ok(None);
        };

        // load the block
        let block_buf = BytesMut::zeroed(block_size as usize);
        let (res, block_buf) = self
            .file
            .read_exact_at(block_buf.slice(..), block_offset)
            .await;
        res?;
        let block_buf = block_buf.into_inner();

        // search within the block
        let reader = BlockReader::<C>::new(block_buf.freeze());
        Ok(reader.get(key))
    }
}
