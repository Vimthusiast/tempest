use std::marker::PhantomData;

use bytes::Bytes;
use serde::{Deserialize, Serialize};
use tempest_core::fio::FioFile;
use zerocopy::IntoBytes;

use crate::{
    base::{Comparer, InternalKey, SST_MAGICNUM, SeqNum, StorageResult},
    config::SstConfig,
    iterator::StorageIterator,
    sst::{
        SstFooter,
        block::{BlockBuilder, BlockStatus},
        bloom::BloomFilterBuilder,
        index::IndexBuilder,
    },
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SstWriterStats {
    pub(crate) file_size: u64,
    pub(crate) entry_count: u64,
    pub(crate) min_key: Bytes,
    pub(crate) max_key: Bytes,
    pub(crate) min_seqnum: SeqNum,
    pub(crate) max_seqnum: SeqNum,
}

impl Default for SstWriterStats {
    fn default() -> Self {
        Self {
            file_size: 0,
            entry_count: 0,
            min_key: Bytes::new(),
            max_key: Bytes::new(),
            // NB: will automatically fall back to the minimum on the first write
            min_seqnum: SeqNum::MAX,
            // NB: will automatically fall back to the maximum on the first write
            max_seqnum: SeqNum::MIN,
        }
    }
}

pub(crate) struct SstWriter<F: FioFile, C: Comparer> {
    file: F,
    filepos: u64,
    entry_estimate: u64,
    block_builder: BlockBuilder,
    index_builder: IndexBuilder,
    bloom_builder: BloomFilterBuilder,
    last_key: Option<InternalKey<C>>,
    config: SstConfig,
    stats: SstWriterStats,
    _marker: PhantomData<C>,
}

impl<F: FioFile, C: Comparer> SstWriter<F, C> {
    /// Create a new writer for a maximum of `entry_estimate` key-value pairs.
    pub(crate) fn new(file: F, entry_estimate: usize, config: SstConfig) -> Self {
        Self {
            file,
            filepos: 0,
            entry_estimate: entry_estimate as u64,
            block_builder: BlockBuilder::new(
                config.block_target_size,
                config.block_restart_interval,
            ),
            index_builder: IndexBuilder::new(),
            bloom_builder: BloomFilterBuilder::new(
                entry_estimate,
                config.bloom_false_positive_rate,
            ),
            last_key: None,
            config,
            stats: SstWriterStats::default(),
            _marker: PhantomData,
        }
    }

    pub(crate) async fn extend_from_collection<I: IntoIterator<Item = (InternalKey<C>, Bytes)>>(
        &mut self,
        iter: I,
    ) -> StorageResult<()> {
        for (key, value) in iter {
            self.write_entry(&key, &value).await?;
        }
        Ok(())
    }

    pub(crate) async fn extend_from_stream<'a, I: StorageIterator<'a, C>>(
        &mut self,
        mut iter: I,
    ) -> StorageResult<()> {
        while let Some(()) = iter.next().await? {
            self.write_entry(iter.key().unwrap(), iter.value().unwrap())
                .await?;
        }
        Ok(())
    }

    pub(crate) async fn write_entry(
        &mut self,
        key: &InternalKey<C>,
        value: &Bytes,
    ) -> StorageResult<()> {
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

        self.stats.entry_count += 1;
        let seqnum = key.trailer().seqnum();
        self.stats.min_seqnum = self.stats.min_seqnum.min(seqnum);
        self.stats.max_seqnum = self.stats.max_seqnum.max(seqnum);
        if self.stats.entry_count == 1 {
            // first key written is min
            self.stats.min_key = key.key().clone();
        }
        self.stats.max_key = key.key().clone(); // last key written is max

        Ok(())
    }

    async fn flush_block(&mut self) -> StorageResult<()> {
        let Some(last_key) = self.last_key.take() else {
            return Ok(());
        };
        let block = std::mem::replace(
            &mut self.block_builder,
            BlockBuilder::new(
                self.config.block_target_size,
                self.config.block_restart_interval,
            ),
        )
        .finalize();
        let block_offset = self.filepos;
        let block_size = block.len() as u32;

        let (res, _) = self.file.write_all_at(block.freeze(), self.filepos).await;
        res?;
        self.filepos += block_size as u64;

        self.index_builder.push(&last_key, block_offset, block_size);
        Ok(())
    }

    /// Finalize this SST and return the file size.
    pub(crate) async fn finalize(mut self) -> StorageResult<SstWriterStats> {
        assert!(self.stats.entry_count <= self.entry_estimate);
        assert_ne!(self.stats.entry_count, 0);
        if self.stats.entry_count < self.entry_estimate {
            trace!(
                overestimation = self.entry_estimate - self.stats.entry_count,
                entry_count = self.stats.entry_count,
                entry_estimate = self.entry_estimate,
                "overestimated the number of entries"
            );
        }

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
        self.filepos += size_of::<SstFooter>() as u64;
        self.stats.file_size = self.filepos;

        self.file.sync_all().await?;
        Ok(self.stats)
    }
}
