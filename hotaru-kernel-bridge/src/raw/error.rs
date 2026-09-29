//! Native error-code decoding and bridge-level errors.

use super::runtime::{Handle, Obj};

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    WrongThread,
    Initialization,
    WrongKind,
    OutOfRange,
    Kernel(u32),
    UnknownNativeError(i32),
}

pub(super) type Result<T> = std::result::Result<T, Error>;

pub(super) fn from_native(code: i32) -> Error {
    match code {
        6 => Error::WrongKind,
        8 => Error::OutOfRange,
        100..=121 => Error::Kernel(code as u32),
        n => Error::UnknownNativeError(n),
    }
}

/// Converts a Lean `Except UInt32` result into an opaque owned handle.
pub(super) unsafe fn checked(raw: Obj) -> Result<Handle> {
    // Every call site passes the one owned reference returned by a matching
    // HotaruKernel export.
    unsafe { Handle::from_raw(raw) }
        .result()
        .map_err(from_native)
}
