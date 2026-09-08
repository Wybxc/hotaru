//! RAII ownership over bindgen's Lean runtime bindings.

use crate::{
    lean::*,
    raw::{initialize_HotaruKernel_HotaruKernelFFI, lean_initialize},
};
use std::{marker::PhantomData, ptr::NonNull, rc::Rc};

pub type Obj = *mut lean_object;

// Owned Lean references cannot leave the runtime's initialization thread.
pub struct Owned(NonNull<lean_object>, PhantomData<Rc<()>>);

impl Owned {
    /// Takes exactly one reference returned by a Lean export.
    pub unsafe fn from_raw(raw: Obj) -> Self {
        Self(unsafe { NonNull::new_unchecked(raw) }, PhantomData)
    }

    pub fn unit() -> Self {
        unsafe { Self::from_raw(lean_box(0)) }
    }

    pub fn into_raw(self) -> Obj {
        let ptr = self.0.as_ptr();
        std::mem::forget(self);
        ptr
    }

    pub fn argument(&self) -> Obj {
        self.clone().into_raw()
    }

    fn tag(&self) -> u32 {
        unsafe { lean_obj_tag(self.0.as_ptr()) }
    }

    pub fn result(self) -> Result<Self, i32> {
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

    pub fn uint64(&self) -> u64 {
        unsafe { lean_unbox_uint64(self.0.as_ptr()) }
    }

    pub fn bytes(&self) -> &[u8] {
        // Lean's size includes its final NUL; embedded NUL bytes remain intact.
        unsafe {
            std::slice::from_raw_parts(
                lean_string_cstr(self.0.as_ptr()).cast(),
                lean_string_size(self.0.as_ptr()) - 1,
            )
        }
    }

    pub fn string(text: &str) -> Self {
        unsafe { Self::from_raw(lean_mk_string_from_bytes(text.as_ptr().cast(), text.len())) }
    }

    pub fn array() -> Self {
        unsafe { Self::from_raw(lean_array_mk(Self::unit().into_raw())) }
    }

    pub fn push(self, value: Self) -> Self {
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

pub fn initialize() -> bool {
    unsafe {
        lean_initialize();
        let result = Owned::from_raw(initialize_HotaruKernel_HotaruKernelFFI(1));
        lean_io_mark_end_initialization();
        result.tag() == 0
    }
}
