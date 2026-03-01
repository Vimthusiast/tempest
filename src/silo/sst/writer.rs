use std::marker::PhantomData;

use bytes::Bytes;
use zerocopy::IntoBytes;

use crate::{
    base::{Comparer, InternalKey, SST_MAGICNUM, TempestResult},
    fio::FioFile,
    silo::sst::{
        SstFooter,
        block::{BlockBuilder, BlockStatus},
        bloom::BloomFilterBuilder,
        index::IndexBuilder,
    },
};

const FALSE_POSITIVE_RATE: f64 = 0.01;

pub struct SstWriter<F: FioFile, C: Comparer> {
    file: F,
    filepos: u64,
    entries_written: u64,
    entries: u64,
    block_builder: BlockBuilder,
    index_builder: IndexBuilder,
    bloom_builder: BloomFilterBuilder,
    last_key: Option<InternalKey<C>>,
    _marker: PhantomData<C>,
}

impl<F: FioFile, C: Comparer> SstWriter<F, C> {
    /// Create a new writer for a total of `n` entries.
    pub fn new(file: F, entries: usize) -> Self {
        Self {
            file,
            filepos: 0,
            entries: entries as u64,
            entries_written: 0,
            block_builder: BlockBuilder::new(),
            index_builder: IndexBuilder::new(),
            bloom_builder: BloomFilterBuilder::new(entries, FALSE_POSITIVE_RATE),
            last_key: None,
            _marker: PhantomData,
        }
    }

    pub async fn write_entry(&mut self, key: &InternalKey<C>, value: &Bytes) -> TempestResult<()> {
        // insert user key into bloom filter
        let c = C::default();
        let (prefix, _) = c.split_up(key.key());
        self.bloom_builder.insert(prefix);

        // store the last key here to create the index (arc clone, so cheap)
        self.last_key = Some(key.clone());

        // write to current block
        match self
            .block_builder
            .write_entry(key.key(), key.trailer(), value)
        {
            BlockStatus::Ok => {}
            BlockStatus::Full => self.flush_block().await?,
        }

        Ok(())
    }

    async fn flush_block(&mut self) -> TempestResult<()> {
        let Some(last_key) = self.last_key.take() else {
            return Ok(());
        };
        let block = std::mem::replace(&mut self.block_builder, BlockBuilder::new()).finalize();
        let block_offset = self.filepos;
        let block_size = block.len() as u32;

        let (res, _) = self.file.write_all_at(block.freeze(), self.filepos).await;
        res?;
        self.filepos += block_size as u64;

        self.index_builder.push(&last_key, block_offset, block_size);
        Ok(())
    }

    pub async fn finalize(mut self) -> TempestResult<()> {
        // flush any remaining entries in the current block
        self.flush_block().await?;

        // write bloom filter
        let bloom = self.bloom_builder.finalize();
        let bloom_offset = self.filepos;
        let bloom_bits = bloom.bits().clone();
        let bloom_size = bloom_bits.len() as u32;
        let (res, _) = self.file.write_all_at(bloom_bits, self.filepos).await;
        res?;
        self.filepos += bloom_size as u64;

        // write index
        let index = self.index_builder.finalize().freeze();
        let index_offset = self.filepos;
        let index_size = index.len() as u32;
        let (res, _) = self.file.write_all_at(index, self.filepos).await;
        res?;
        self.filepos += index_size as u64;

        // write footer
        let footer = SstFooter {
            magic: *SST_MAGICNUM,
            bloom_offset: bloom_offset.into(),
            bloom_size: bloom_size.into(),
            bloom_footer: bloom.footer(),
            index_offset: index_offset.into(),
            index_size: index_size.into(),
        };
        let (res, _) = self
            .file
            .write_all_at(Bytes::copy_from_slice(footer.as_bytes()), self.filepos)
            .await;
        res?;
        self.file.sync_all().await?;

        Ok(())
    }
}
