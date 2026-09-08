//! The small portion of Lean 4.29.0's lean.h needed by the adapter.
//! Layouts are restricted by build.rs to the pinned 64-bit little-endian runtime.
use std::{
    marker::PhantomData,
    ptr::NonNull,
    rc::Rc,
    sync::atomic::{AtomicI32, Ordering},
};

#[repr(C)]
pub(crate) struct Object {
    rc: AtomicI32,
    size: u16,
    other: u8,
    tag: u8,
}
pub(crate) type Obj = *mut Object;

#[repr(C)]
struct StringObject {
    header: Object,
    size: usize,
    capacity: usize,
    length: usize,
}

unsafe extern "C" {
    fn lean_initialize();
    fn initialize_HotaruKernel_HotaruKernelFFI(builtin: u8) -> Obj;
    fn lean_io_mark_end_initialization();
    fn lean_dec_ref_cold(object: Obj);
    fn lean_mk_string_from_bytes(bytes: *const u8, length: usize) -> Obj;
    fn lean_array_mk(list: Obj) -> Obj;
    fn lean_array_push(array: Obj, value: Obj) -> Obj;
}

// Owned Lean references cannot leave the runtime's initialization thread.
pub(crate) struct Owned(NonNull<Object>, PhantomData<Rc<()>>);

impl Owned {
    /// Takes exactly one reference returned by a Lean export.
    pub(crate) unsafe fn from_raw(raw: Obj) -> Self {
        Self(unsafe { NonNull::new_unchecked(raw) }, PhantomData)
    }

    pub(crate) fn unit() -> Self {
        // Lean encodes scalar constructor zero as the tagged pointer 1.
        unsafe { Self::from_raw(std::ptr::without_provenance_mut(1)) }
    }

    pub(crate) fn into_raw(self) -> Obj {
        let ptr = self.0.as_ptr();
        std::mem::forget(self);
        ptr
    }

    pub(crate) fn argument(&self) -> Obj {
        self.clone().into_raw()
    }

    pub(crate) fn tag(&self) -> u8 {
        if self.0.as_ptr().addr() & 1 != 0 {
            (self.0.as_ptr().addr() >> 1) as u8
        } else {
            unsafe { self.0.as_ref().tag }
        }
    }

    fn field(&self, index: usize) -> Self {
        // Only known constructor objects are passed here, with an in-range index.
        let raw = unsafe { self.0.as_ptr().byte_add(8).cast::<Obj>().add(index).read() };
        unsafe {
            retain(raw);
            Self::from_raw(raw)
        }
    }

    pub(crate) fn result(self) -> Result<Self, i32> {
        if self.tag() == 0 {
            let raw = unsafe { self.0.as_ptr().byte_add(8).cast::<Obj>().read() };
            Err((raw.addr() >> 1) as i32)
        } else {
            Ok(self.field(0))
        }
    }

    pub(crate) fn uint64(&self) -> u64 {
        unsafe { self.0.as_ptr().byte_add(8).cast::<u64>().read() }
    }

    pub(crate) fn bytes(&self) -> &[u8] {
        let string = unsafe { &*self.0.as_ptr().cast::<StringObject>() };
        unsafe { std::slice::from_raw_parts(self.0.as_ptr().byte_add(32).cast(), string.size - 1) }
    }

    pub(crate) fn string(text: &str) -> Self {
        unsafe { Self::from_raw(lean_mk_string_from_bytes(text.as_ptr(), text.len())) }
    }

    pub(crate) fn array() -> Self {
        unsafe { Self::from_raw(lean_array_mk(Self::unit().into_raw())) }
    }

    pub(crate) fn push(self, value: Self) -> Self {
        unsafe { Self::from_raw(lean_array_push(self.into_raw(), value.into_raw())) }
    }
}

unsafe fn retain(raw: Obj) {
    if raw.addr() & 1 == 0 {
        let rc = unsafe { &(*raw).rc };
        let count = rc.load(Ordering::Relaxed);
        if count > 0 {
            rc.store(count.wrapping_add(1), Ordering::Relaxed);
        } else if count < 0 {
            rc.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

impl Clone for Owned {
    fn clone(&self) -> Self {
        unsafe {
            retain(self.0.as_ptr());
            Self::from_raw(self.0.as_ptr())
        }
    }
}

impl Drop for Owned {
    fn drop(&mut self) {
        if self.0.as_ptr().addr() & 1 == 0 {
            let rc = unsafe { &self.0.as_ref().rc };
            let count = rc.load(Ordering::Relaxed);
            if count > 1 {
                rc.store(count - 1, Ordering::Relaxed);
            } else if count != 0 {
                unsafe { lean_dec_ref_cold(self.0.as_ptr()) };
            }
        }
    }
}

pub(crate) fn initialize() -> bool {
    unsafe {
        lean_initialize();
        let result = Owned::from_raw(initialize_HotaruKernel_HotaruKernelFFI(1));
        lean_io_mark_end_initialization();
        result.tag() == 0
    }
}

const _: () = assert!(size_of::<Object>() == 8 && size_of::<StringObject>() == 32);
