//! Lean runtime initialization and its single-thread constraint.

use super::{
    error::{Error, Result},
    runtime,
};
use std::{sync::OnceLock, thread::ThreadId};

pub fn ensure_initialized() -> Result<()> {
    static INIT: OnceLock<(ThreadId, bool)> = OnceLock::new();

    let current = std::thread::current().id();
    let (owner, ok) = INIT.get_or_init(|| (current, runtime::initialize()));

    if *owner != current {
        Err(Error::WrongThread)
    } else if !ok {
        Err(Error::Initialization)
    } else {
        Ok(())
    }
}
