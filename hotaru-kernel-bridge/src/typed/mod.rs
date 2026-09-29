//! Typed, safe wrappers around the private raw kernel boundary.

mod error;
mod foundation;
mod syntax;
mod theorem;
mod theory;

mod context;
mod term;
mod type_;

pub use error::{Error, KernelError, Result};
pub use foundation::Foundation;
pub use syntax::{Name, Source, SourceKind};
pub use term::{CheckedTerm, Term, TermKind};
pub use theorem::Theorem;
pub use theory::Theory;
pub use type_::{Type, TypeKind};
