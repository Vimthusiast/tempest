use serde::Deserialize;

use crate::{fio::VirtualFileSystem, test_utils::setup_tracing};

use super::*;

#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct ReplayableCounter(i64);

#[derive(Serialize, Deserialize)]
enum ReplayableCounterEdit {
    Add(i64),
    Set(i64),
}

impl ReplayableCounter {
    fn count(&self) -> i64 {
        self.0
    }
}

impl Replayable for ReplayableCounter {
    type Edit = ReplayableCounterEdit;

    fn apply(&mut self, edit: Self::Edit) {
        match edit {
            ReplayableCounterEdit::Add(v) => self.0 += v,
            ReplayableCounterEdit::Set(v) => self.0 = v,
        }
    }

    fn snapshot(&self) -> Self::Edit {
        ReplayableCounterEdit::Set(self.0)
    }

    fn filename_prefix() -> &'static str {
        "replayable-counter"
    }

    fn initial() -> Self {
        Self(0)
    }
}

#[tokio::test]
async fn test_journal() -> Result<(), JournalError> {
    setup_tracing();

    let fs = VirtualFileSystem::new();
    let dir = PathBuf::from("/journal-dir");
    let config = JournalConfig::default();
    {
        // open first journal
        let mut journal =
            Journal::<ReplayableCounter, _>::open(fs.clone(), dir.clone(), config.clone()).await?;
        assert_eq!(journal.state(), &ReplayableCounter::initial());

        // first edit
        journal.append(ReplayableCounterEdit::Add(1)).await?;
        assert_eq!(journal.count(), 1);
        assert!(matches!(journal.snapshot(), ReplayableCounterEdit::Set(1)));

        // second edit
        journal.append(ReplayableCounterEdit::Add(-6)).await?;
        assert_eq!(journal.count(), -5);
        assert!(matches!(journal.snapshot(), ReplayableCounterEdit::Set(-5)));

        // set to final value
        journal.append(ReplayableCounterEdit::Set(42)).await?;
        assert_eq!(journal.count(), 42);
        assert_eq!(journal.current_filenum, 0);
        assert!(journal.scratch.is_some());
        assert!(matches!(journal.snapshot(), ReplayableCounterEdit::Set(42)));
    }

    {
        // reopen journal again
        let mut journal =
            Journal::<ReplayableCounter, _>::open(fs.clone(), dir.clone(), config.clone()).await?;

        // verify state
        assert_eq!(journal.count(), 42);
        assert_eq!(journal.current_filenum, 0);

        // rotate the journal
        journal.rotate().await?;
        assert!(journal.scratch.is_some());
    }

    {
        // reopen journal again
        let journal =
            Journal::<ReplayableCounter, _>::open(fs.clone(), dir.clone(), config.clone()).await?;
        assert_eq!(journal.current_filenum, 1);
        assert!(journal.scratch.is_some());
    }

    Ok(())
}
