use core::fmt;
use core::ptr::NonNull;
use std::boxed::Box;
use std::marker::PhantomData;

use crate::oskey;
use crate::{AccessError, ThreadLocalValue, GUARD, thread_local_drop};

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
/// A `ThreadLocalCell`'s initializer cannot recursively depend on itself, and
/// using a `ThreadLocalCell` in this way will cause the initializer to infinitely
/// recurse on the first call to [`with`].
///
///   [`std::thread::LocalKey`]: https://doc.rust-lang.org/std/thread/struct.LocalKey.html
///   [`with`]: #method.with
///   [`Drop`]: https://doc.rust-lang.org/std/ops/trait.Drop.html
///
/// # Examples
///
/// This is the same as the example in the [`std::thread::LocalKey`] documentation,
/// but adjusted to use `ThreadLocalCell` instead. To use it in a `static` context, a
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
/// use os_thread_local::ThreadLocalCell;
///
/// static FOO: Lazy<ThreadLocalCell<RefCell<u32>>> =
///     Lazy::new(|| ThreadLocalCell::new(|| RefCell::new(1)));
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
/// use os_thread_local::ThreadLocalCell;
///
/// struct Foo {
///     data: u32,
///     tls: ThreadLocalCell<RefCell<u32>>,
/// }
///
/// let foo = Foo {
///     data: 0,
///     tls: ThreadLocalCell::new(|| RefCell::new(1)),
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
/// - Destructors will not run if the corresponding `ThreadLocalCell` is dropped
///   in a child thread (this can happen e.g. if the object or binding holding
///   it is moved into a child thread ; or when the `ThreadLocalCell` is created
///   in a child thread).
/// - Destructors may not run if a `ThreadLocalCell` is initialized during the `Drop`
///   impl of a type held by another `ThreadLocalCell`.
/// - The order in which destructors may run when using multiple `ThreadLocalCell`
///   is not guaranteed.
///
/// On Windows, `ThreadLocalCell` provides per-thread storage as long as fibers
/// are unused. When fibers are used, it provides per-fiber storage, which
/// is similar but more fine-grained.
pub struct ThreadLocalCell<T> {
    key: oskey::Key,
    value_type: PhantomData<T>,
}

impl<T> fmt::Debug for ThreadLocalCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("ThreadLocalCell {{ .. }}")
    }
}

impl<T> ThreadLocalCell<T> {
    /// Creates a new thread-local storage handle.
    ///
    /// The provided function is used to initialize the value on the first use in
    /// each thread.
    ///
    /// ```rust
    /// use os_thread_local::ThreadLocalCell;
    ///
    /// let tls = ThreadLocalCell::new(|| 42);
    /// ```
    pub fn new() -> Self {
        ThreadLocalCell::<T> {
            key: unsafe { oskey::create(Some(thread_local_drop::<T>)) },
            value_type: PhantomData,
        }
    }

    /// Acquires a reference to the value in this thread-local storage.
    ///
    /// This will lazily initialize the value if this thread has not accessed it
    /// yet, by calling the `i` clojure.
    ///
    /// ```rust
    /// use os_thread_local::ThreadLocalCell;
    /// use std::cell::Cell;
    ///
    /// let tls = ThreadLocalCell::new(|| Cell::new(42));
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
    pub fn with<R, F, I>(&self, i: I, f: F) -> R where
        F: FnOnce(&T) -> R,
        I: FnOnce() -> T
    {
        self.try_with(i, f)
            .expect("cannot access a TLS value during or after it is destroyed")
    }

    /// Acquires a reference to the value in this thread-local storage.
    ///
    /// This will lazily initialize the value if this thread has not accessed it
    /// yet, by calling the `i` clojure. If the storage has been destroyed, this
    /// function will return an `AccessError`.
    ///
    /// ```rust
    /// use os_thread_local::ThreadLocalCell;
    /// use std::cell::Cell;
    ///
    /// let tls = ThreadLocalCell::new(|| Cell::new(42));
    /// tls.try_with(|v| v.set(21)).expect("storage destroyed");
    /// ```
    ///
    /// # Panics
    ///
    /// This function will `panic!()` if the storage is uninitialized and the
    /// initializer given to [`ThreadLocalCell::new`](#method.new) panics.
    /// This function can also `panic!()` if the storage is uninitialized and there
    /// is not enough available memory to allocate a new thread local storage for
    /// the current thread, or if the OS primitives fail.
    pub fn try_with<R, F, I>(&self, i: I, f: F) -> Result<R, AccessError> where
        F: FnOnce(&T) -> R,
        I: FnOnce() -> T
    {
        let ptr = unsafe { oskey::get(self.key) as *mut ThreadLocalValue<T> };

        let value = NonNull::new(ptr).unwrap_or_else(|| unsafe {
            // Equivalent to currently unstable Box::into_raw_non_null.
            // https://github.com/rust-lang/rust/issues/47336#issuecomment-373941458
            let result = NonNull::new_unchecked(Box::into_raw(Box::new(ThreadLocalValue {
                inner: i(),
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

impl<T> Drop for ThreadLocalCell<T> {
    fn drop(&mut self) {
        unsafe {
            oskey::destroy(self.key);
        }
    }
}

/// Since the value is always initialized by the calling thread, and the only shared field is a pure function,
/// `ThreadLocalCell` is always safe to send between threads.
/// Drop notes and restrictions still apply.
unsafe impl<T> Send for ThreadLocalCell<T> {}

#[cfg(test)]
pub(crate) mod tests {
    use super::ThreadLocalCell;
    use core::cell::{Cell, UnsafeCell};
    use crossbeam_utils::thread::scope;
    use once_cell::sync::Lazy;
    use std::sync::mpsc::{channel, Sender};
    use std::sync::RwLock;
    use std::thread;

    // Some tests use multiple ThreadLocalCell handles and rely on them having a
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
        let foo = ThreadLocalCell::new();
        scope(|s| {
            let foo = &foo;
            let (tx, rx) = channel();
            let _t = s.spawn(move |_| unsafe {
                let mut tx = Some(tx);
                foo.with(|| UnsafeCell::new(None), |f| {
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
        let foo = ThreadLocalCell::new();
        scope(|s| {
            let foo = &foo;
            foo.with(|| Cell::new(1), |f| {
                assert_eq!(f.get(), 1);
                f.set(2);
            });
            let (tx, rx) = channel();
            let _t = s.spawn(move |_| {
                foo.with(|| Cell::new(1), |f| {
                    assert_eq!(f.get(), 1);
                });
                tx.send(()).unwrap();
            });
            rx.recv().unwrap();
            foo.with(|| Cell::new(1), |f| {
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
                assert!(FOO.try_with(|| Foo, |_| ()).is_err());
            }
        }
        static FOO: Lazy<ThreadLocalCell<Foo>> = Lazy::new(|| ThreadLocalCell::new());

        thread::spawn(|| {
            assert!(FOO.try_with(|| Foo, |_| ()).is_ok());
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
        static K1: Lazy<ThreadLocalCell<UnsafeCell<Option<S1>>>> =
            Lazy::new(|| ThreadLocalCell::new());
        static K2: Lazy<ThreadLocalCell<UnsafeCell<Option<S2>>>> =
            Lazy::new(|| ThreadLocalCell::new());
        static mut HITS: u32 = 0;

        impl Drop for S1 {
            fn drop(&mut self) {
                unsafe {
                    HITS += 1;
                    if K2.try_with(|| UnsafeCell::new(None), |_| ()).is_err() {
                        assert_eq!(HITS, 3);
                    } else {
                        if HITS == 1 {
                            K2.with(|| UnsafeCell::new(None), |s| *s.get() = Some(S2));
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
                    assert!(K1.try_with(|| UnsafeCell::new(None), |_| ()).is_ok());
                    assert_eq!(HITS, 2);
                    K1.with(|| UnsafeCell::new(None), |s| *s.get() = Some(S1));
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
        static K1: Lazy<ThreadLocalCell<UnsafeCell<Option<S1>>>> =
            Lazy::new(|| ThreadLocalCell::new());

        impl Drop for S1 {
            fn drop(&mut self) {
                assert!(K1.try_with(|| UnsafeCell::new(None), |_| ()).is_err());
            }
        }

        thread::spawn(move || unsafe {
            K1.with(|| UnsafeCell::new(None), |s| *s.get() = Some(S1));
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
            ThreadLocalCell<UnsafeCell<Option<S1>>>,
            ThreadLocalCell<UnsafeCell<Option<Foo>>>,
        )> = Lazy::new(|| {
            (
                ThreadLocalCell::new(),
                ThreadLocalCell::new(),
            )
        });

        impl Drop for S1 {
            fn drop(&mut self) {
                let S1(ref tx) = *self;
                unsafe {
                    let _ = K.1.try_with(|| UnsafeCell::new(None), |s| *s.get() = Some(Foo(tx.clone())));
                }
            }
        }

        let (tx, rx) = channel();
        let _t = thread::spawn(move || unsafe {
            let mut tx = Some(tx);
            K.0.with(|| UnsafeCell::new(None), |s| *s.get() = Some(S1(tx.take().unwrap())));
        });
        rx.recv().unwrap();
    }
}

#[cfg(test)]
mod dynamic_tests {
    use super::tests::LOCK;
    use super::ThreadLocalCell;
    use core::cell::RefCell;
    use std::collections::HashMap;
    use std::vec;

    #[test]
    fn smoke() {
        let _l = LOCK.read().unwrap();
        fn square(i: i32) -> i32 {
            i * i
        }
        let foo = ThreadLocalCell::new();

        foo.with(|| square(3), |f| {
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
        let foo = ThreadLocalCell::new();

        foo.with(|| map(), |map| {
            assert_eq!(map.borrow()[&1], 2);
        });
    }

    #[test]
    fn refcell_vec() {
        let _l = LOCK.read().unwrap();
        let foo = ThreadLocalCell::new();

        foo.with(|| RefCell::new(vec![1, 2, 3]), |vec| {
            assert_eq!(vec.borrow().len(), 3);
            vec.borrow_mut().push(4);
            assert_eq!(vec.borrow()[3], 4);
        });
    }
}
