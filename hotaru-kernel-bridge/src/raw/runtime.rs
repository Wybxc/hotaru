//! RAII ownership over bindgen's Lean runtime bindings.

use super::{
    bindings::*,
    exports::{initialize_HotaruKernel_HotaruKernelFFI, lean_initialize},
};
use std::{marker::PhantomData, ptr::NonNull, rc::Rc};

pub(super) type Obj = *mut lean_object;

// Owned Lean references cannot leave the runtime's initialization thread.
pub(super) struct Owned(NonNull<lean_object>, PhantomData<Rc<()>>);

impl Owned {
    /// Takes exactly one reference returned by a Lean export.
    pub(super) unsafe fn from_raw(raw: Obj) -> Self {
        Self(unsafe { NonNull::new_unchecked(raw) }, PhantomData)
    }

    pub(super) fn unit() -> Self {
        unsafe { Self::from_raw(lean_box(0)) }
    }

    pub(super) fn into_raw(self) -> Obj {
        let ptr = self.0.as_ptr();
        std::mem::forget(self);
        ptr
    }

    pub(super) fn argument(&self) -> Obj {
        self.clone().into_raw()
    }

    fn tag(&self) -> u32 {
        unsafe { lean_obj_tag(self.0.as_ptr()) }
    }

    pub(super) fn result(self) -> Result<Self, i32> {
        // Only Except UInt32 results reach this method; its payload is borrowed.
        unsafe {
            let payload = lean_ctor_get(self.0.as_ptr(), 0);

            if self.tag() == 0 {
                Err(lean_unbox_uint32(payload) as i32)
            } else {
                lean_inc(payload);
                Ok(Self::from_raw(payload))
            }
        }
    }

    pub(super) fn uint64(&self) -> u64 {
        unsafe { lean_unbox_uint64(self.0.as_ptr()) }
    }

    pub(super) fn bytes(&self) -> &[u8] {
        // Lean's size includes its final NUL; embedded NUL bytes remain intact.
        unsafe {
            std::slice::from_raw_parts(
                lean_string_cstr(self.0.as_ptr()).cast(),
                lean_string_size(self.0.as_ptr()) - 1,
            )
        }
    }

    pub(super) fn string(text: &str) -> Self {
        unsafe { Self::from_raw(lean_mk_string_from_bytes(text.as_ptr().cast(), text.len())) }
    }

    pub(super) fn array() -> Self {
        unsafe { Self::from_raw(lean_array_mk(Self::unit().into_raw())) }
    }

    pub(super) fn push(self, value: Self) -> Self {
        unsafe { Self::from_raw(lean_array_push(self.into_raw(), value.into_raw())) }
    }
}

impl Clone for Owned {
    fn clone(&self) -> Self {
        unsafe {
            lean_inc(self.0.as_ptr());
            Self::from_raw(self.0.as_ptr())
        }
    }
}

impl Drop for Owned {
    fn drop(&mut self) {
        unsafe { lean_dec(self.0.as_ptr()) };
    }
}

pub(super) fn initialize() -> bool {
    unsafe {
        lean_initialize();
        let result = Owned::from_raw(initialize_HotaruKernel_HotaruKernelFFI(1));
        lean_io_mark_end_initialization();
        result.tag() == 0
    }
}

/// An owned, thread-confined Lean object handle.
///
/// This type is visible only inside the private `raw` module. The typed layer
/// wraps it in distinct semantic newtypes before exposing any operation.
#[derive(Clone)]
pub struct Handle(Owned);

impl std::fmt::Debug for Handle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Handle").finish_non_exhaustive()
    }
}

impl Handle {
    pub(super) unsafe fn from_raw(raw: Obj) -> Self {
        Self(unsafe { Owned::from_raw(raw) })
    }

    pub(super) fn into_raw(self) -> Obj {
        self.0.into_raw()
    }

    pub(super) fn argument(&self) -> Obj {
        self.0.argument()
    }

    pub(super) fn result(self) -> Result<Self, i32> {
        self.0.result().map(Self)
    }

    pub(super) fn uint64(&self) -> u64 {
        self.0.uint64()
    }

    pub(super) fn bytes(&self) -> &[u8] {
        self.0.bytes()
    }

    pub(super) fn string(text: &str) -> Self {
        Self(Owned::string(text))
    }

    pub(super) fn array() -> Self {
        Self(Owned::array())
    }

    pub(super) fn push(self, value: Self) -> Self {
        Self(self.0.push(value.0))
    }
}
