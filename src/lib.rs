// Parts of tests and documentation that were copied from the rust code-base
// are Copyright The Rust Project Developers, and licensed under the MIT or
// Apache-2.0, license, like the rest of this project. See the LICENSE-MIT and
// LICENSE-APACHE files at the root of this crate.

//! OS-backed thread-local storage
//!
//! This crate provides a [`ThreadLocal`] type as an alternative to
//! `std::thread_local!` that allows per-object thread-local storage, while
//! providing a similar API. It always uses the thread-local storage primitives
//! provided by the OS.
//!
//! On Unix systems, pthread-based thread-local storage is used.
//!
//! On Windows, fiber-local storage is used. This acts like thread-local
//! storage when fibers are unused, but also provides per-fiber values
//! after fibers are created with e.g. `winapi::um::winbase::CreateFiber`.
//!
//! See [`ThreadLocal`] for more details.
//!
//!   [`ThreadLocal`]: struct.ThreadLocal.html
//!
//! The [`thread_local`](https://crates.io/crates/thread_local) crate also
//! provides per-object thread-local storage, with a different API, and
//! different features, but with more performance overhead than this one.

//#![deny(missing_docs)]

pub mod thread_local;
pub mod thread_local_cell;

use core::fmt;
use core::ptr::NonNull;
use std::error::Error;

use crate::oskey::c_void;

pub use thread_local::ThreadLocal;
pub use thread_local_cell::ThreadLocalCell;

#[cfg(windows)]
mod oskey {
    use winapi::um::fibersapi;

    pub(crate) type Key = winapi::shared::minwindef::DWORD;
    #[allow(non_camel_case_types)]
    pub(crate) type c_void = winapi::ctypes::c_void;

    #[inline]
    pub(crate) unsafe fn create(dtor: Option<unsafe extern "system" fn(*mut c_void)>) -> Key {
        fibersapi::FlsAlloc(dtor)
    }

    #[inline]
    pub(crate) unsafe fn set(key: Key, value: *mut c_void) {
        let r = fibersapi::FlsSetValue(key, value);
        debug_assert_ne!(r, 0);
    }

    #[inline]
    pub(crate) unsafe fn get(key: Key) -> *mut c_void {
        fibersapi::FlsGetValue(key)
    }

    #[inline]
    pub(crate) unsafe fn destroy(key: Key) {
        let r = fibersapi::FlsFree(key);
        debug_assert_ne!(r, 0);
    }
}

#[cfg(not(windows))]
mod oskey {
    use core::mem::{self, MaybeUninit};

    pub(crate) type Key = libc::pthread_key_t;
    #[allow(non_camel_case_types)]
    pub(crate) type c_void = core::ffi::c_void;

    #[inline]
    pub(crate) unsafe fn create(dtor: Option<unsafe extern "system" fn(*mut c_void)>) -> Key {
        let mut key = MaybeUninit::uninit();
        assert_eq!(
            libc::pthread_key_create(key.as_mut_ptr(), mem::transmute(dtor)),
            0
        );
        key.assume_init()
    }

    #[inline]
    pub(crate) unsafe fn set(key: Key, value: *mut c_void) {
        let r = libc::pthread_setspecific(key, value);
        debug_assert_eq!(r, 0);
    }

    #[inline]
    pub(crate) unsafe fn get(key: Key) -> *mut c_void {
        libc::pthread_getspecific(key)
    }

    #[inline]
    pub(crate) unsafe fn destroy(key: Key) {
        let r = libc::pthread_key_delete(key);
        debug_assert_eq!(r, 0);
    }
}

/// An error returned by [`ThreadLocal::try_with`](struct.ThreadLocal.html#method.try_with).
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct AccessError {
    _private: (),
}

impl fmt::Debug for AccessError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("AccessError").finish()
    }
}

impl fmt::Display for AccessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("already destroyed", f)
    }
}

impl Error for AccessError {}

/// A wrapper holding values stored in TLS. We store a `Box<ThreadLocalValue<T>>`,
/// turned into raw pointers.
struct ThreadLocalValue<T> {
    inner: T,
    key: oskey::Key,
}

const GUARD: NonNull<c_void> = NonNull::dangling();

/// Drops the local value from the calling thread.
unsafe extern "system" fn thread_local_drop<T>(ptr: *mut c_void) {
    let ptr = NonNull::new_unchecked(ptr as *mut ThreadLocalValue<T>);
    if ptr != GUARD.cast() {
        let value = Box::from_raw(ptr.as_ptr());
        oskey::set(value.key, GUARD.as_ptr());
        // value is dropped here, and the `Box` destroyed.
    }
}

