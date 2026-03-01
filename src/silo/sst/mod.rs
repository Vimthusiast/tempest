use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, LittleEndian, U32, U64};

use crate::silo::sst::bloom::BloomFilterFooter;

pub mod block;
pub mod bloom;
pub mod index;

pub mod reader;
pub mod writer;

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

#[cfg(test)]
mod tests {
    use super::reader::SstReader;
    use super::writer::SstWriter;
    use crate::base::{DefaultComparer, InternalKey, KeyKind, KeyTrailer, SeqNum};
    use crate::fio::{FioFS, FioFile, VirtualFile, VirtualFileSystem};
    use crate::silo::iterator::TempestIterator;
    use bytes::Bytes;

    fn make_trailer(seqnum: u64, kind: KeyKind) -> KeyTrailer {
        KeyTrailer::new(unsafe { SeqNum::new_unchecked(seqnum) }, kind)
    }

    fn make_key(s: &str, seqnum: u64) -> InternalKey<DefaultComparer> {
        InternalKey::new(
            Bytes::copy_from_slice(s.as_bytes()),
            make_trailer(seqnum, KeyKind::Put),
        )
    }

    fn make_delete_key(s: &str, seqnum: u64) -> InternalKey<DefaultComparer> {
        InternalKey::new(
            Bytes::copy_from_slice(s.as_bytes()),
            make_trailer(seqnum, KeyKind::Delete),
        )
    }

    async fn build_sst(entries: &[(&str, u64, &str)]) -> (VirtualFileSystem, String) {
        let fs = VirtualFileSystem::new();
        let path = "test.sst";
        let file = fs
            .opts()
            .write(true)
            .create_new(true)
            .open(path)
            .await
            .unwrap();

        let mut writer = SstWriter::<_, DefaultComparer>::new(file, entries.len());
        for (key, seqnum, value) in entries {
            let k = make_key(key, *seqnum);
            let v = Bytes::copy_from_slice(value.as_bytes());
            writer.write_entry(&k, &v).await.unwrap();
        }
        writer.finalize().await.unwrap();

        (fs, path.to_string())
    }

    async fn open_sst(
        fs: &VirtualFileSystem,
        path: &str,
    ) -> SstReader<VirtualFile, DefaultComparer> {
        let file = fs.opts().read(true).open(path).await.unwrap();
        SstReader::open(file).await.unwrap()
    }

    #[tokio::test]
    async fn test_get_existing_key() {
        let (fs, path) = build_sst(&[
            ("apple", 1, "fruit"),
            ("banana", 1, "yellow"),
            ("cherry", 1, "red"),
        ])
        .await;

        let reader = open_sst(&fs, &path).await;
        let result = reader.get(&make_key("banana", 1)).await.unwrap();
        assert_eq!(result.unwrap(), Bytes::from("yellow"));
    }

    #[tokio::test]
    async fn test_get_missing_key() {
        let (fs, path) = build_sst(&[("apple", 1, "fruit"), ("cherry", 1, "red")]).await;

        let reader = open_sst(&fs, &path).await;
        assert!(reader.get(&make_key("banana", 1)).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn test_bloom_filter_rejects_missing_key() {
        let (fs, path) = build_sst(&[("apple", 1, "fruit"), ("banana", 1, "yellow")]).await;

        let reader = open_sst(&fs, &path).await;
        // completely different key space - bloom should reject most of these
        let missing = ["zzz", "yyy", "xxx", "www", "vvv"];
        for key in &missing {
            let result = reader.get(&make_key(key, 1)).await.unwrap();
            assert!(result.is_none());
        }
    }

    #[tokio::test]
    async fn test_get_first_and_last_key() {
        let (fs, path) = build_sst(&[
            ("aaa", 1, "first"),
            ("mmm", 1, "middle"),
            ("zzz", 1, "last"),
        ])
        .await;

        let reader = open_sst(&fs, &path).await;
        assert_eq!(
            reader.get(&make_key("aaa", 1)).await.unwrap().unwrap(),
            Bytes::from("first")
        );
        assert_eq!(
            reader.get(&make_key("zzz", 1)).await.unwrap().unwrap(),
            Bytes::from("last")
        );
    }

    #[tokio::test]
    async fn test_many_keys_across_multiple_blocks() {
        // enough entries to span multiple 4KB blocks
        let mut entries: Vec<(String, u64, String)> = Vec::new();
        for i in 0..500u32 {
            entries.push((format!("key:{:08}", i), 1, format!("value:{}", i)));
        }
        let entries_ref: Vec<(&str, u64, &str)> = entries
            .iter()
            .map(|(k, s, v)| (k.as_str(), *s, v.as_str()))
            .collect();

        let (fs, path) = build_sst(&entries_ref).await;
        let reader = open_sst(&fs, &path).await;

        // verify every key is found with correct value
        for i in 0..500u32 {
            let key = format!("key:{:08}", i);
            let expected = format!("value:{}", i);
            let result = reader.get(&make_key(&key, 1)).await.unwrap();
            assert_eq!(
                result.unwrap(),
                Bytes::copy_from_slice(expected.as_bytes()),
                "failed at key {}",
                key
            );
        }
    }

    #[tokio::test]
    async fn test_missing_key_between_existing_keys() {
        let (fs, path) = build_sst(&[
            ("key:0001", 1, "a"),
            ("key:0003", 1, "b"),
            ("key:0005", 1, "c"),
        ])
        .await;

        let reader = open_sst(&fs, &path).await;
        assert!(
            reader
                .get(&make_key("key:0002", 1))
                .await
                .unwrap()
                .is_none()
        );
        assert!(
            reader
                .get(&make_key("key:0004", 1))
                .await
                .unwrap()
                .is_none()
        );
    }

    #[tokio::test]
    async fn test_empty_value() {
        let (fs, path) = build_sst(&[("key", 1, "")]).await;
        let reader = open_sst(&fs, &path).await;
        assert_eq!(
            reader.get(&make_key("key", 1)).await.unwrap().unwrap(),
            Bytes::new()
        );
    }

    #[tokio::test]
    async fn test_magic_number_verified() {
        let fs = VirtualFileSystem::new();
        let path = "corrupt.sst";
        let file = fs
            .opts()
            .write(true)
            .create_new(true)
            .open(path)
            .await
            .unwrap();
        // write garbage
        file.write_all_at(Bytes::from(vec![0u8; 64]), 0)
            .await
            .0
            .unwrap();

        let file = fs.opts().read(true).open(path).await.unwrap();
        let result = SstReader::<VirtualFile, DefaultComparer>::open(file).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_delete_tombstone_key() {
        let fs = VirtualFileSystem::new();
        let path = "test.sst";
        let file = fs
            .opts()
            .write(true)
            .create_new(true)
            .open(path)
            .await
            .unwrap();

        let mut writer = SstWriter::<_, DefaultComparer>::new(file, 2);
        // tombstone - delete marker with higher seqnum
        // NB: higher seqnum comes first!
        writer
            .write_entry(&make_delete_key("apple", 2), &Bytes::new())
            .await
            .unwrap();
        writer
            .write_entry(&make_key("apple", 1), &Bytes::from("fruit"))
            .await
            .unwrap();
        writer.finalize().await.unwrap();

        let file = fs.opts().read(true).open(path).await.unwrap();
        let reader = SstReader::<VirtualFile, DefaultComparer>::open(file)
            .await
            .unwrap();

        // both seqnums should be found since the SST stores all versions
        assert!(
            reader
                .get(&make_delete_key("apple", 2))
                .await
                .unwrap()
                .is_some()
        );
        assert!(reader.get(&make_key("apple", 1)).await.unwrap().is_some());
    }

    #[tokio::test]
    async fn test_iterator_all_entries() {
        let (fs, path) = build_sst(&[
            ("apple", 1, "fruit"),
            ("banana", 1, "yellow"),
            ("cherry", 1, "red"),
        ])
        .await;

        let reader = open_sst(&fs, &path).await;
        let mut iter = reader.iter();
        let mut results = Vec::new();
        while let Ok(Some(())) = iter.next().await {
            results.push((
                iter.key().unwrap().key().clone(),
                iter.value().unwrap().clone(),
            ));
        }

        assert_eq!(results.len(), 3);
        assert_eq!(results[0], (Bytes::from("apple"), Bytes::from("fruit")));
        assert_eq!(results[1], (Bytes::from("banana"), Bytes::from("yellow")));
        assert_eq!(results[2], (Bytes::from("cherry"), Bytes::from("red")));
    }

    #[tokio::test]
    async fn test_iterator_across_multiple_blocks() {
        let mut entries: Vec<(String, u64, String)> = Vec::new();
        for i in 0..500u32 {
            entries.push((format!("key:{:08}", i), 1, format!("value:{}", i)));
        }
        let entries_ref: Vec<(&str, u64, &str)> = entries
            .iter()
            .map(|(k, s, v)| (k.as_str(), *s, v.as_str()))
            .collect();

        let (fs, path) = build_sst(&entries_ref).await;
        let reader = open_sst(&fs, &path).await;
        let mut iter = reader.iter();

        let mut count = 0;
        while let Ok(Some(())) = iter.next().await {
            let key = iter.key().unwrap().key().clone();
            let value = iter.value().unwrap().clone();
            let expected_key = format!("key:{:08}", count);
            let expected_value = format!("value:{}", count);
            assert_eq!(
                key,
                Bytes::copy_from_slice(expected_key.as_bytes()),
                "wrong key at {}",
                count
            );
            assert_eq!(
                value,
                Bytes::copy_from_slice(expected_value.as_bytes()),
                "wrong value at {}",
                count
            );
            count += 1;
        }
        assert_eq!(count, 500);
    }

    #[tokio::test]
    async fn test_iterator_matches_get() {
        let mut entries: Vec<(String, u64, String)> = Vec::new();
        for i in 0..100u32 {
            entries.push((format!("key:{:08}", i), 1, format!("value:{}", i)));
        }
        let entries_ref: Vec<(&str, u64, &str)> = entries
            .iter()
            .map(|(k, s, v)| (k.as_str(), *s, v.as_str()))
            .collect();

        let (fs, path) = build_sst(&entries_ref).await;
        let reader = open_sst(&fs, &path).await;
        let mut iter = reader.iter();

        while let Ok(Some(())) = iter.next().await {
            let key = iter.key().unwrap().clone();
            let iter_value = iter.value().unwrap().clone();
            let get_value = reader.get(&key).await.unwrap();
            assert_eq!(Some(iter_value), get_value);
        }
    }

    #[tokio::test]
    async fn test_iterator_empty_sst() {
        let (fs, path) = build_sst(&[("only", 1, "entry")]).await;
        let reader = open_sst(&fs, &path).await;
        let mut iter = reader.iter();

        assert!(matches!(iter.next().await, Ok(Some(()))));
        assert_eq!(iter.key().unwrap().key().clone(), Bytes::from("only"));
        assert!(matches!(iter.next().await, Ok(None)));
    }

    #[tokio::test]
    async fn test_iterator_trailers_preserved() {
        let fs = VirtualFileSystem::new();
        let path = "test.sst";
        let file = fs
            .opts()
            .write(true)
            .create_new(true)
            .open(path)
            .await
            .unwrap();

        let mut writer = SstWriter::<_, DefaultComparer>::new(file, 2);
        writer
            .write_entry(&make_delete_key("apple", 2), &Bytes::new())
            .await
            .unwrap();
        writer
            .write_entry(&make_key("apple", 1), &Bytes::from("fruit"))
            .await
            .unwrap();
        writer.finalize().await.unwrap();

        let reader = open_sst(&fs, path).await;
        let mut iter = reader.iter();

        assert!(matches!(iter.next().await, Ok(Some(()))));
        let key = iter.key().unwrap();
        assert_eq!(key.trailer().kind(), KeyKind::Delete);
        assert_eq!(key.trailer().seqnum().get(), 2);

        assert!(matches!(iter.next().await, Ok(Some(()))));
        let key = iter.key().unwrap();
        assert_eq!(key.trailer().kind(), KeyKind::Put);
        assert_eq!(key.trailer().seqnum().get(), 1);

        assert!(matches!(iter.next().await, Ok(None)));
    }
}
