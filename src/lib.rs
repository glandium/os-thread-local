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

#![deny(missing_docs)]

use core::fmt;
use core::ptr::NonNull;
use std::boxed::Box;
use std::error::Error;

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

use oskey::c_void;

/// A thread-local storage handle.
///
/// In many ways, this struct works similarly to [`std::thread::LocalKey`], but
/// always relies on OS primitives (see [module-level documentation](index.html)).
///
/// The [`with`] method yields a reference to the contained value which cannot
/// be sent across threads or escape the given closure.
///
/// # Initialization and Destruction
///
/// Initialization is dynamically performed on the first call to [`with`]
/// within a thread, and values that implement [`Drop`] get destructed when a
/// thread exits. Some caveats apply, which are explained below.
///
/// A `ThreadLocal`'s initializer cannot recursively depend on itself, and
/// using a `ThreadLocal` in this way will cause the initializer to infinitely
/// recurse on the first call to [`with`].
///
///   [`std::thread::LocalKey`]: https://doc.rust-lang.org/std/thread/struct.LocalKey.html
///   [`with`]: #method.with
///   [`Drop`]: https://doc.rust-lang.org/std/ops/trait.Drop.html
///
/// # Examples
///
/// This is the same as the example in the [`std::thread::LocalKey`] documentation,
/// but adjusted to use `ThreadLocal` instead. To use it in a `static` context, a
/// lazy initializer, such as [`once_cell::sync::Lazy`] or [`lazy_static!`] is
/// required.
///
///   [`once_cell::sync::Lazy`]: https://docs.rs/once_cell/1.2.0/once_cell/sync/struct.Lazy.html
///   [`lazy_static!`]: https://docs.rs/lazy_static/1.4.0/lazy_static/
///
/// ```rust
/// use std::cell::RefCell;
/// use std::thread;
/// use once_cell::sync::Lazy;
/// use os_thread_local::ThreadLocal;
///
/// static FOO: Lazy<ThreadLocal<RefCell<u32>>> =
///     Lazy::new(|| ThreadLocal::new(|| RefCell::new(1)));
///
/// FOO.with(|f| {
///     assert_eq!(*f.borrow(), 1);
///     *f.borrow_mut() = 2;
/// });
///
/// // each thread starts out with the initial value of 1
/// let t = thread::spawn(move || {
///     FOO.with(|f| {
///         assert_eq!(*f.borrow(), 1);
///         *f.borrow_mut() = 3;
///     });
/// });
///
/// // wait for the thread to complete and bail out on panic
/// t.join().unwrap();
///
/// // we retain our original value of 2 despite the child thread
/// FOO.with(|f| {
///     assert_eq!(*f.borrow(), 2);
/// });
/// ```
///
/// A variation of the same with scoped threads and per-object thread-local
/// storage:
///
/// ```rust
/// use std::cell::RefCell;
/// use crossbeam_utils::thread::scope;
/// use os_thread_local::ThreadLocal;
///
/// struct Foo {
///     data: u32,
///     tls: ThreadLocal<RefCell<u32>>,
/// }
///
/// let foo = Foo {
///     data: 0,
///     tls: ThreadLocal::new(|| RefCell::new(1)),
/// };
///
/// foo.tls.with(|f| {
///     assert_eq!(*f.borrow(), 1);
///     *f.borrow_mut() = 2;
/// });
///
/// scope(|s| {
///     // each thread starts out with the initial value of 1
///     let foo2 = &foo;
///     let t = s.spawn(move |_| {
///         foo2.tls.with(|f| {
///             assert_eq!(*f.borrow(), 1);
///             *f.borrow_mut() = 3;
///         });
///     });
///
///     // wait for the thread to complete and bail out on panic
///     t.join().unwrap();
///
///     // we retain our original value of 2 despite the child thread
///     foo.tls.with(|f| {
///         assert_eq!(*f.borrow(), 2);
///     });
/// }).unwrap();
/// ```
///
/// # Platform-specific behavior and caveats
///
/// Note that a "best effort" is made to ensure that destructors for types
/// stored in thread-local storage are run, but it is not guaranteed that
/// destructors will be run for all types in thread-local storage.
///
/// - Destructors may not run on the main thread when it exits.
/// - Destructors will not run if the corresponding `ThreadLocal` is dropped
///   in a child thread (this can happen e.g. if the object or binding holding
///   it is moved into a child thread ; or when the `ThreadLocal` is created
///   in a child thread).
/// - Destructors may not run if a `ThreadLocal` is initialized during the `Drop`
///   impl of a type held by another `ThreadLocal`.
/// - The order in which destructors may run when using multiple `ThreadLocal`
///   is not guaranteed.
///
/// On Windows, `ThreadLocal` provides per-thread storage as long as fibers
/// are unused. When fibers are used, it provides per-fiber storage, which
/// is similar but more fine-grained.
pub struct ThreadLocal<T> {
    key: oskey::Key,
    init: fn() -> T,
}

impl<T: Default> Default for ThreadLocal<T> {
    fn default() -> Self {
        ThreadLocal::new(Default::default)
    }
}

impl<T> fmt::Debug for ThreadLocal<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("ThreadLocal {{ .. }}")
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

unsafe extern "system" fn thread_local_drop<T>(ptr: *mut c_void) {
    let ptr = NonNull::new_unchecked(ptr as *mut ThreadLocalValue<T>);
    if ptr != GUARD.cast() {
        let value = Box::from_raw(ptr.as_ptr());
        oskey::set(value.key, GUARD.as_ptr());
        // value is dropped here, and the `Box` destroyed.
    }
}

impl<T> ThreadLocal<T> {
    /// Creates a new thread-local storage handle.
    ///
    /// The provided function is used to initialize the value on the first use in
    /// each thread.
    ///
    /// ```rust
    /// use os_thread_local::ThreadLocal;
    ///
    /// let tls = ThreadLocal::new(|| 42);
    /// ```
    pub fn new(f: fn() -> T) -> Self {
        ThreadLocal {
            key: unsafe { oskey::create(Some(thread_local_drop::<T>)) },
            init: f,
        }
    }

    /// Acquires a reference to the value in this thread-local storage.
    ///
    /// This will lazily initialize the value if this thread has not accessed it
    /// yet.
    ///
    /// ```rust
    /// use os_thread_local::ThreadLocal;
    /// use std::cell::Cell;
    ///
    /// let tls = ThreadLocal::new(|| Cell::new(42));
    /// tls.with(|v| v.set(21));
    /// ```
    ///
    /// # Panics
    ///
    /// This function will `panic!()` if the handle currently has its destructor
    /// running, and it **may** panic if the destructor has previously been run for
    /// this thread.
    /// This function can also `panic!()` if the storage is uninitialized and there
    /// is not enough available memory to allocate a new thread local storage for
    /// the current thread, or if the OS primitives fail.
    pub fn with<R, F: FnOnce(&T) -> R>(&self, f: F) -> R {
        self.try_with(f)
            .expect("cannot access a TLS value during or after it is destroyed")
    }

    /// Acquires a reference to the value in this thread-local storage.
    ///
    /// This will lazily initialize the value if this thread has not accessed it
    /// yet. If the storage has been destroyed, this function will return an
    /// `AccessError`.
    ///
    /// ```rust
    /// use os_thread_local::ThreadLocal;
    /// use std::cell::Cell;
    ///
    /// let tls = ThreadLocal::new(|| Cell::new(42));
    /// tls.try_with(|v| v.set(21)).expect("storage destroyed");
    /// ```
    ///
    /// # Panics
    ///
    /// This function will `panic!()` if the storage is uninitialized and the
    /// initializer given to [`ThreadLocal::new`](#method.new) panics.
    /// This function can also `panic!()` if the storage is uninitialized and there
    /// is not enough available memory to allocate a new thread local storage for
    /// the current thread, or if the OS primitives fail.
    pub fn try_with<R, F: FnOnce(&T) -> R>(&self, f: F) -> Result<R, AccessError> {
        let ptr = unsafe { oskey::get(self.key) as *mut ThreadLocalValue<T> };
        let value = NonNull::new(ptr).unwrap_or_else(|| unsafe {
            // Equivalent to currently unstable Box::into_raw_non_null.
            // https://github.com/rust-lang/rust/issues/47336#issuecomment-373941458
            let result = NonNull::new_unchecked(Box::into_raw(Box::new(ThreadLocalValue {
                inner: (self.init)(),
                key: self.key,
            })));
            oskey::set(self.key, result.as_ptr() as *mut _);
            result
        });
        // Avoid reinitializing a TLS that was destroyed.
        if value != GUARD.cast() {
            Ok(f(&unsafe { value.as_ref() }.inner))
        } else {
            Err(AccessError { _private: () })
        }
    }
}

impl<T> Drop for ThreadLocal<T> {
    fn drop(&mut self) {
        unsafe {
            oskey::destroy(self.key);
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::ThreadLocal;
    use core::cell::{Cell, UnsafeCell};
    use crossbeam_utils::thread::scope;
    use once_cell::sync::Lazy;
    use std::sync::mpsc::{channel, Sender};
    use std::sync::RwLock;
    use std::thread;

    // Some tests use multiple ThreadLocal handles and rely on them having a
    // deterministic-ish order, which is not guaranteed when multiple tests
    // run in parallel. So we make all tests using a single handle hold a
    // read lock, and all tests using multiple handles hold a write lock,
    // avoiding race conditions between tests.
    pub static LOCK: Lazy<RwLock<()>> = Lazy::new(|| RwLock::new(()));

    #[test]
    fn assumptions() {
        use super::oskey;
        use core::ptr::{self, NonNull};
        use core::sync::atomic::{AtomicBool, Ordering};

        let _l = LOCK.write().unwrap();
        static CALLED: AtomicBool = AtomicBool::new(false);
        unsafe extern "system" fn call(_: *mut oskey::c_void) {
            CALLED.store(true, Ordering::Release);
        }
        unsafe {
            // Test our assumptions wrt the OS TLS implementation.
            let key = oskey::create(None);
            // A newly created handle returns a NULL value.
            assert_eq!(oskey::get(key), ptr::null_mut());
            oskey::set(key, NonNull::dangling().as_ptr());
            assert_eq!(oskey::get(key), NonNull::dangling().as_ptr());
            oskey::destroy(key);
            let key2 = oskey::create(None);
            // Destroying a handle and creating a new one right after gives
            // the same handle.
            assert_eq!(key, key2);
            // A re-create handle with the same number still returns a NULL
            // value.
            assert_eq!(oskey::get(key), ptr::null_mut());
            oskey::destroy(key2);

            let key = oskey::create(Some(call));
            scope(|s| {
                s.spawn(|_| {
                    oskey::get(key);
                })
                .join()
                .unwrap();
                // The destructor of a handle that hasn't been set is not called.
                assert_eq!(CALLED.load(Ordering::Acquire), false);
                s.spawn(|_| {
                    oskey::set(key, NonNull::dangling().as_ptr());
                })
                .join()
                .unwrap();
                // The destructor is called if the handle has been set.
                assert_eq!(CALLED.load(Ordering::Acquire), true);
                CALLED.store(false, Ordering::Release);
                s.spawn(|_| {
                    oskey::set(key, NonNull::dangling().as_ptr());
                    oskey::set(key, ptr::null_mut());
                })
                .join()
                .unwrap();
                // The destructor of a handle explicitly (re)set to NULL is not called.
                assert_eq!(CALLED.load(Ordering::Acquire), false);
            })
            .unwrap();
        }
    }

    // The tests below were adapted from the tests in libstd/thread/local.rs
    // in the rust source.
    struct Foo(Sender<()>);

    impl Drop for Foo {
        fn drop(&mut self) {
            let Foo(ref s) = *self;
            s.send(()).unwrap();
        }
    }

    #[test]
    fn smoke_dtor() {
        let _l = LOCK.read().unwrap();
        let foo = ThreadLocal::new(|| UnsafeCell::new(None));
        scope(|s| {
            let foo = &foo;
            let (tx, rx) = channel();
            let _t = s.spawn(move |_| unsafe {
                let mut tx = Some(tx);
                foo.with(|f| {
                    *f.get() = Some(Foo(tx.take().unwrap()));
                });
            });
            rx.recv().unwrap();
        })
        .unwrap();
    }

    #[test]
    fn smoke_no_dtor() {
        let _l = LOCK.read().unwrap();
        let foo = ThreadLocal::new(|| Cell::new(1));
        scope(|s| {
            let foo = &foo;
            foo.with(|f| {
                assert_eq!(f.get(), 1);
                f.set(2);
            });
            let (tx, rx) = channel();
            let _t = s.spawn(move |_| {
                foo.with(|f| {
                    assert_eq!(f.get(), 1);
                });
                tx.send(()).unwrap();
            });
            rx.recv().unwrap();
            foo.with(|f| {
                assert_eq!(f.get(), 2);
            });
        })
        .unwrap();
    }

    #[test]
    fn states() {
        let _l = LOCK.read().unwrap();
        struct Foo;
        impl Drop for Foo {
            fn drop(&mut self) {
                assert!(FOO.try_with(|_| ()).is_err());
            }
        }
        static FOO: Lazy<ThreadLocal<Foo>> = Lazy::new(|| ThreadLocal::new(|| Foo));

        thread::spawn(|| {
            assert!(FOO.try_with(|_| ()).is_ok());
        })
        .join()
        .ok()
        .expect("thread panicked");
    }

    #[test]
    fn circular() {
        let _l = LOCK.read().unwrap();
        struct S1;
        struct S2;
        static K1: Lazy<ThreadLocal<UnsafeCell<Option<S1>>>> =
            Lazy::new(|| ThreadLocal::new(|| UnsafeCell::new(None)));
        static K2: Lazy<ThreadLocal<UnsafeCell<Option<S2>>>> =
            Lazy::new(|| ThreadLocal::new(|| UnsafeCell::new(None)));
        static mut HITS: u32 = 0;

        impl Drop for S1 {
            fn drop(&mut self) {
                unsafe {
                    HITS += 1;
                    if K2.try_with(|_| ()).is_err() {
                        assert_eq!(HITS, 3);
                    } else {
                        if HITS == 1 {
                            K2.with(|s| *s.get() = Some(S2));
                        } else {
                            assert_eq!(HITS, 3);
                        }
                    }
                }
            }
        }
        impl Drop for S2 {
            fn drop(&mut self) {
                unsafe {
                    HITS += 1;
                    assert!(K1.try_with(|_| ()).is_ok());
                    assert_eq!(HITS, 2);
                    K1.with(|s| *s.get() = Some(S1));
                }
            }
        }

        thread::spawn(move || {
            drop(S1);
        })
        .join()
        .ok()
        .expect("thread panicked");
    }

    #[test]
    fn self_referential() {
        let _l = LOCK.read().unwrap();
        struct S1;
        static K1: Lazy<ThreadLocal<UnsafeCell<Option<S1>>>> =
            Lazy::new(|| ThreadLocal::new(|| UnsafeCell::new(None)));

        impl Drop for S1 {
            fn drop(&mut self) {
                assert!(K1.try_with(|_| ()).is_err());
            }
        }

        thread::spawn(move || unsafe {
            K1.with(|s| *s.get() = Some(S1));
        })
        .join()
        .ok()
        .expect("thread panicked");
    }

    #[test]
    fn dtors_in_dtors_in_dtors() {
        let _l = LOCK.write().unwrap();
        struct S1(Sender<()>);
        static K: Lazy<(
            ThreadLocal<UnsafeCell<Option<S1>>>,
            ThreadLocal<UnsafeCell<Option<Foo>>>,
        )> = Lazy::new(|| {
            (
                ThreadLocal::new(|| UnsafeCell::new(None)),
                ThreadLocal::new(|| UnsafeCell::new(None)),
            )
        });

        impl Drop for S1 {
            fn drop(&mut self) {
                let S1(ref tx) = *self;
                unsafe {
                    let _ = K.1.try_with(|s| *s.get() = Some(Foo(tx.clone())));
                }
            }
        }

        let (tx, rx) = channel();
        let _t = thread::spawn(move || unsafe {
            let mut tx = Some(tx);
            K.0.with(|s| *s.get() = Some(S1(tx.take().unwrap())));
        });
        rx.recv().unwrap();
    }
}

#[cfg(test)]
mod dynamic_tests {
    use super::tests::LOCK;
    use super::ThreadLocal;
    use core::cell::RefCell;
    use std::collections::HashMap;
    use std::vec;

    #[test]
    fn smoke() {
        let _l = LOCK.read().unwrap();
        fn square(i: i32) -> i32 {
            i * i
        }
        let foo = ThreadLocal::new(|| square(3));

        foo.with(|f| {
            assert_eq!(*f, 9);
        });
    }

    #[test]
    fn hashmap() {
        let _l = LOCK.read().unwrap();
        fn map() -> RefCell<HashMap<i32, i32>> {
            let mut m = HashMap::new();
            m.insert(1, 2);
            RefCell::new(m)
        }
        let foo = ThreadLocal::new(|| map());

        foo.with(|map| {
            assert_eq!(map.borrow()[&1], 2);
        });
    }

    #[test]
    fn refcell_vec() {
        let _l = LOCK.read().unwrap();
        let foo = ThreadLocal::new(|| RefCell::new(vec![1, 2, 3]));

        foo.with(|vec| {
            assert_eq!(vec.borrow().len(), 3);
            vec.borrow_mut().push(4);
            assert_eq!(vec.borrow()[3], 4);
        });
    }
}
