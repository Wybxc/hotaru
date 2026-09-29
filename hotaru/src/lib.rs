#![forbid(unsafe_code)]

//! Safe, typed Rust values for the verified Lean kernel.
//! Values are confined to the first thread that initializes the runtime.
//!
//! ```compile_fail
//! let ty = hotaru::Type::bool().unwrap();
//! std::thread::spawn(move || drop(ty));
//! ```
//!
//! ```compile_fail
//! fn require_sync<T: Sync>() {}
//! require_sync::<hotaru::Theorem>();
//! ```

mod error;
mod foundation;
mod syntax;
mod theorem;
mod theory;

pub use error::{Error, KernelError, Result};
pub use foundation::Foundation;
pub use hotaru_kernel_bridge::{beta, check, conclusion, mp, refl};
pub use syntax::{CheckedTerm, Name, Source, SourceKind, Term, TermKind, Type, TypeKind};
pub use theorem::Theorem;
pub use theory::Theory;
