//! The private boundary around bindgen, Lean pointers, and FFI calls.
//!
//! Nothing in this module is part of the bridge's public API. The module
//! itself is private at the crate root, so these internal re-exports are only
//! reachable by the sibling `typed` implementation.

mod bindings;
mod convert;
pub mod error;
mod exports;
pub mod ops;
pub mod runtime;
pub mod thread;

pub use error::Error;
pub use ops::*;
pub use thread::ensure_initialized;
