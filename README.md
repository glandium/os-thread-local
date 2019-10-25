# OS-backed thread-local storage

This library provides a `ThreadLocal` type which provides an alternative
to `std::thread_local!` that always uses the thread-local storage
primitives provided by the OS.

Unlike `std::thread_local!`, `ThreadLocal` allows per-object thread-local
storage, while providing a similar API.

On Unix systems, pthread-based thread-local storage is used.

On Windows, fiber-local storage is used. This acts like thread-local
storage when fibers are unused, but also provides per-fiber values
after fibers are created with `winapi::um::winbase::CreateFiber`.

The [`thread_local`](https://crates.io/crates/thread_local) crate also provides
per-object thread-local storage, with a different API, and different features,
but with more performance overhead than this one.

# Examples

This is the same as the example in [`std::thread::LocalKey`], but adjusted
to use `ThreadLocal` instead. To use it in a `static` context, a lazy
initializer, such as [`once_cell::sync::Lazy`] or [`lazy_static!`] is required.

  [`std::thread::LocalKey`]: https://doc.rust-lang.org/std/thread/struct.LocalKey.html
  [`once_cell::sync::Lazy`]: https://docs.rs/once_cell/1.2.0/once_cell/sync/struct.Lazy.html
  [`lazy_static!`]: https://docs.rs/lazy_static/1.4.0/lazy_static/

```rust
use std::cell::RefCell;
use std::thread;
use once_cell::sync::Lazy;
use os_thread_local::ThreadLocal;

static FOO: Lazy<ThreadLocal<RefCell<u32>>> =
    Lazy::new(|| ThreadLocal::new(|| RefCell::new(1)));

FOO.with(|f| {
    assert_eq!(*f.borrow(), 1);
    *f.borrow_mut() = 2;
});

// each thread starts out with the initial value of 1
let t = thread::spawn(move || {
    FOO.with(|f| {
        assert_eq!(*f.borrow(), 1);
        *f.borrow_mut() = 3;
    });
});

// wait for the thread to complete and bail out on panic
t.join().unwrap();

// we retain our original value of 2 despite the child thread
FOO.with(|f| {
    assert_eq!(*f.borrow(), 2);
});
```

A variation of the same with scoped threads and per-object thread-local
storage:

```rust
use std::cell::RefCell;
use crossbeam_utils::thread::scope;
use os_thread_local::ThreadLocal;

struct Foo {
    data: u32,
    tls: ThreadLocal<RefCell<u32>>,
}

let foo = Foo {
    data: 0,
    tls: ThreadLocal::new(|| RefCell::new(1)),
};

foo.tls.with(|f| {
    assert_eq!(*f.borrow(), 1);
    *f.borrow_mut() = 2;
});

scope(|s| {
    // each thread starts out with the initial value of 1
    let foo2 = &foo;
    let t = s.spawn(move |_| {
        foo2.tls.with(|f| {
            assert_eq!(*f.borrow(), 1);
            *f.borrow_mut() = 3;
        });
    });

    // wait for the thread to complete and bail out on panic
    t.join().unwrap();

    // we retain our original value of 2 despite the child thread
    foo.tls.with(|f| {
        assert_eq!(*f.borrow(), 2);
    });
}).unwrap();
```
