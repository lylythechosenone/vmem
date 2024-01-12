//! Locking traits and implementations.
//!
//! This allows for mutexes in a `no_std` environment, where there is no generic
//! mutex type. Users are encouraged to implement this trait for a custom type,
//! however some implementations are provided.
//!
//! # Default implementations
//! With the `std` feature, this crate provides an implementation for
//! [`std::sync::Mutex`], and with the `spin` feature, this crate provides an
//! implementation for [`spin::Mutex`]. The std implementation is recommended
//! for situations where libstd is available. The spin implementation is [not
//! recommended](https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html),
//! however. If possible, implement your own non-spinning lock type.

#[cfg(feature = "spin")]
use spin::Mutex;

/// A trait for types that can be used as locks.
///
/// In order to avoid exposing private types, this lock is typeless and does not
/// actually store the value directly. It should usually be implemented with a
/// mutex with an empty data field.
///
/// # Safety
/// The type must provide unique access to the underlying data, like a mutex
/// would.
pub unsafe trait Lock: Default {
    /// The guard type returned by this lock.
    ///
    /// This type will be held for as long as the lock is held, and will be
    /// dropped when the arena should be unlocked.
    type Guard<'a>
    where
        Self: 'a;

    /// Locks the type.
    ///
    /// This function should block until the lock is acquired. It should return
    /// a guard that will be held for as long as the lock is held. It should not
    /// allow any other access until the guard is dropped.
    fn lock(&self) -> Self::Guard<'_>;
}

#[cfg(feature = "spin")]
unsafe impl Lock for Mutex<()> {
    type Guard<'a> = spin::MutexGuard<'a, ()>;

    fn lock(&self) -> Self::Guard<'_> {
        self.lock()
    }
}

#[cfg(any(test, feature = "std"))]
unsafe impl Lock for std::sync::Mutex<()> {
    type Guard<'a> = std::sync::MutexGuard<'a, ()>;

    fn lock(&self) -> Self::Guard<'_> {
        self.lock().unwrap()
    }
}
