//! Runtime identity for one dynamically extended theory.

use crate::raw as bridge;
use std::rc::Rc;

/// A context is intentionally an implementation detail. Its identity is
/// compared by `Rc` pointer equality so descendants can be checked without
/// making dynamic theory extension state part of the public API.
pub(super) struct Context {
    pub(super) value: bridge::runtime::Handle,
    pub(super) edge: Option<bridge::runtime::Handle>,
    pub(super) parent: Option<Rc<Context>>,
}

impl Drop for Context {
    fn drop(&mut self) {
        let mut parent = self.parent.take();

        while let Some(rc) = parent {
            match Rc::try_unwrap(rc) {
                Ok(mut context) => parent = context.parent.take(),
                Err(_) => break,
            }
        }
    }
}
