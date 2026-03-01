use std::{
    io,
    marker::PhantomData,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
};

use bytes::{Bytes, BytesMut};
use tokio_uring::buf::BoundedBuf;
use zerocopy::FromBytes;

use crate::{
    base::{Comparer, InternalKey, SILO_SST_MAGICNUM, TempestResult},
    fio::FioFile,
    silo::{
        iterator::TempestIterator,
        sst::{
            SstFooter,
            block::{BlockIterator, BlockReader},
            bloom::BloomFilter,
            index::IndexReader,
        },
    },
};

pub struct SstIterator<F: FioFile, C: Comparer> {
    /// the file we are reading
    file: Arc<F>,
    /// the key we got through polling
    current_key: Option<(InternalKey<C>, Bytes)>,
    /// the current block we are on
    current_block: Option<BlockIterator<C>>,
    /// index reader for the block index
    index: IndexReader<C>,
    /// the position of the current block within the index
    index_pos: usize,
    /// in-progress block load future
    loading: Option<Pin<Box<dyn Future<Output = TempestResult<Bytes>>>>>,
    _marker: PhantomData<C>,
}

impl<F: FioFile, C: Comparer> SstIterator<F, C> {
    pub fn new(file: Arc<F>, index: IndexReader<C>) -> Self {
        Self {
            file,
            current_key: None,
            current_block: None,
            index,
            index_pos: 0,
            loading: None,
            _marker: PhantomData,
        }
    }
}

impl<F: FioFile, C: Comparer> TempestIterator<'_, C> for SstIterator<F, C> {
    fn poll_next(&mut self, cx: &mut Context<'_>) -> Poll<TempestResult<Option<()>>> {
        loop {
            if let Some(loading) = &mut self.loading {
                match loading.as_mut().poll(cx) {
                    Poll::Pending => return Poll::Pending,
                    Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
                    Poll::Ready(Ok(buf)) => {
                        self.loading = None;
                        self.current_block = Some(BlockIterator::new(buf));
                    }
                }
            }

            if let Some(block) = &mut self.current_block {
                if let Some((key, value)) = block.next() {
                    self.current_key = Some((key, value));
                    return Poll::Ready(Ok(Some(())));
                }
                self.current_block = None;
                self.index_pos += 1;
            }

            let Some((block_offset, block_size)) = self.index.get_block_by_index(self.index_pos)
            else {
                return Poll::Ready(Ok(None));
            };

            let file = self.file.clone();
            self.loading = Some(Box::pin(async move {
                let buf = BytesMut::zeroed(block_size as usize);
                let (res, buf) = file.read_exact_at(buf.slice(..), block_offset).await;
                res?;
                Ok(buf.into_inner().freeze())
            }));
        }
    }

    fn key(&self) -> Option<&InternalKey<C>> {
        self.current_key.as_ref().map(|(k, _v)| k)
    }

    fn value(&self) -> Option<&Bytes> {
        self.current_key.as_ref().map(|(_k, v)| v)
    }
}

pub struct SstReader<F: FioFile, C: Comparer> {
    file: Arc<F>,
    bloom: BloomFilter,
    index: IndexReader<C>,
    _marker: PhantomData<C>,
}

impl<F: FioFile, C: Comparer> SstReader<F, C> {
    pub async fn open(file: F) -> TempestResult<Self> {
        let file = Arc::new(file);
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
        if &footer.magic != SILO_SST_MAGICNUM {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "invalid magic number: not an sst file. expected {:?} but got {:?}.",
                    SILO_SST_MAGICNUM, footer.magic
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

    pub fn iter(&self) -> SstIterator<F, C> {
        SstIterator::new(self.file.clone(), self.index.clone())
    }
}
