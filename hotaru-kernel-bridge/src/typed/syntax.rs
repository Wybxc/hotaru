//! Syntax metadata shared by the typed type and term wrappers.

use crate::{Error, Result, raw as bridge};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub scope: String,
    pub name: String,
}

impl Name {
    pub fn new(scope: impl Into<String>, name: impl Into<String>) -> Self {
        Self {
            scope: scope.into(),
            name: name.into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceKind {
    TheoryFile,
    Checkpoint,
}

/// A claimed construction source, not authentication of an artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source {
    pub kind: SourceKind,
    pub artifact: String,
}

impl Source {
    pub fn new(kind: SourceKind, artifact: impl Into<String>) -> Self {
        Self {
            kind,
            artifact: artifact.into(),
        }
    }

    pub(super) fn to_native(&self) -> Result<bridge::runtime::Handle> {
        let kind = match self.kind {
            SourceKind::TheoryFile => 0,
            SourceKind::Checkpoint => 1,
        };
        bridge::source(kind, &self.artifact).map_err(Error::from)
    }
}
