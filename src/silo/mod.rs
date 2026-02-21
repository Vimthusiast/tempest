use crate::{fio::FioFS, silo::manifest::SiloManifest};

mod manifest;

pub(crate) struct Silo<F: FioFS> {
    manifest: SiloManifest<F>,
}

impl<F: FioFS> Silo<F> {}
