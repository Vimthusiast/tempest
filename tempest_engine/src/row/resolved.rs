use std::collections::BTreeMap;

use crate::catalog::schema::{FieldDef, FieldId, TableId};

#[derive(Debug)]
pub(crate) struct ResolvedTable<'a> {
    pub(crate) id: TableId,
    pub(crate) fields: &'a BTreeMap<FieldId, FieldDef>,
    pub(crate) primary_key: &'a [FieldId],
}
