use bytes::{Buf, Bytes};
use tempest_core::fio::FioFS;

use crate::{
    Storage,
    base::{Comparer, InternalKey, KeyKind, KeyTrailer, StorageError, StorageResult},
    batch::WriteBatch,
    read_varint,
    wal::WalRecoveryReader,
};

impl<F: FioFS, C: Comparer> Storage<F, C> {
    pub(crate) fn apply_batch_to_memtable(&mut self, mut body: Bytes) -> StorageResult<()> {
        let header = body.split_to(12);

        let seqnum_raw = u64::from_le_bytes(header[0..8].try_into().unwrap());
        let seqnum = seqnum_raw.try_into()?;

        let count = u32::from_le_bytes(header[8..12].try_into().unwrap());

        // TODO: verify remaining length along the way, to prevent crashes if batch is malformed
        let mut pairs: Vec<(KeyKind, Bytes, Bytes)> = Vec::new();
        for idx in 0..count {
            trace!(idx, "reading entry");

            // get kind
            let kind_byte = body.split_to(1)[0];
            let kind: KeyKind = kind_byte.try_into()?;

            // get key length varint
            let (key_len, varint_bytes_read) =
                read_varint(&body[..]).ok_or(StorageError::InvalidVarint)?;
            body.advance(varint_bytes_read);

            // get key
            let key = body.split_to(key_len);
            trace!(?kind, key_len, ?key, idx, "got key");

            match kind {
                KeyKind::Delete => {
                    pairs.push((kind, key, Bytes::new()));
                }
                KeyKind::Put => {
                    // get value length varint
                    let (value_len, varint_bytes_read) =
                        read_varint(&body[..]).ok_or(StorageError::InvalidVarint)?;
                    body.advance(varint_bytes_read);

                    // get value
                    let value = body.split_to(value_len);
                    trace!(value_len, ?value, idx, "got value");

                    pairs.push((kind, key, value));
                }
            }
        }

        for (kind, key, value) in pairs {
            let trailer = KeyTrailer::new(seqnum, kind);
            let key = InternalKey::new(key, trailer);
            self.active.insert(key, value);
        }

        Ok(())
    }

    #[instrument(skip_all)]
    pub(crate) async fn replay_wal(
        &mut self,
        mut recovery_reader: WalRecoveryReader<F>,
    ) -> StorageResult<()> {
        let max_flushed_seqnum = self.manifest.max_flushed_seqnum();
        while let Some(res) = recovery_reader.next().await {
            // skip over errors
            let data = match res {
                Ok(d) => d,
                Err(e) => {
                    warn!("could not recover record from wal: {}, skipping", e);
                    continue;
                }
            };

            let batch_seqnum = WriteBatch::seqnum(&data)?;
            if batch_seqnum <= max_flushed_seqnum {
                trace!(
                    ?batch_seqnum,
                    "skipping already flushed batch during recovery"
                );
                continue;
            }

            self.apply_batch_to_memtable(data.freeze())?;
        }

        Ok(())
    }
}
