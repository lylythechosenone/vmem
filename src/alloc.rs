//! Allocation-related traits
//!
//! In order to facilitate operation in many different environments, this crate
//! does not use the `alloc` crate. Instead, it provides a generic interface for
//! specifying your own allocator specifically for boundary tags.
//!
//! With the `nightly` feature, you can use any type that implements
//! [`core::alloc::Allocator`]. Alternatively, you can implement the
//! [`Allocator`] trait yourself if you are able to provide a specialized
//! implementation.

use core::ptr::NonNull;

use crate::Bt;

/// A generic allocator for boundary tags
///
/// # Implementing
/// In order to implement this trait, you must implement both
/// [`allocate`](Allocator::allocate) and [`deallocate`](Allocator::deallocate).
/// The value returned by these two functions is unspecified, as long as it is a
/// valid allocation of memory that satisfies the size and alignment of a
/// boundary tag. The tag itself may be initialized to any value, and it will be
/// immediately overwritten before use.
///
/// # Bootstrapping
/// Running vmem as the heap allocator is a fairly common use case. However, for
/// this to work, special care must be taken in the [`Allocator`]
/// implementation. The arena will often attempt to allocate boundary tags while
/// it is locked, so it is important to ensure that a bootstrapped allocator
/// does not allocate directly from the arena. Some indirection is necessary. A
/// recommended layout is a slab-style caching allocator. In such an
/// implementation, an allocation would result in the following:
/// 1. If there is space inside the slab, allocate from the slab.
/// 2. If the slab is empty, keep a small emergency cache of boundary tags. Once
///    the allocation is complete (`done` has been called), a new slab can be
///    allocated to restock the emergency cache. Be sure to keep at least 2 tags
///    for this new slab (return `None` 2 elements early).
///
/// A free would simply return the tag to the slab. An allocator may also
/// optionally deallocate slabs, although this is not a necessity, and is not
/// necessarily better for either performance or memory usage.
///
/// In addition, one could choose to return boundary tags to the emergency cache
/// on free if there is a hole. This is not necessary, but may be beneficial.
///
/// If an allocator cannot satisfy an allocation (i.e. the emergency cache is
/// completely empty), it should return `None`. This will be propagated to the
/// caller via [`Error::AllocatorError`](crate::error::Error::AllocatorError)
/// and can be handled there. `done` will not be called in this case.
///
/// # Safety
/// For more advanced safety concerns, this trait follows the same rules as
/// [`core::alloc::Allocator`].
pub unsafe trait Allocator {
    /// Allocate a single boundary tag.
    fn allocate(&self) -> Option<NonNull<Bt>>;
    /// Free an allocated boundary tag.
    ///
    /// # Safety
    /// Follows the safety contract of [`core::alloc::Allocator::deallocate`].
    unsafe fn deallocate(&self, ptr: NonNull<Bt>);

    /// Called by the arena when it is finished with a certain operation.
    /// Implementations, especially bootstrapping ones, can use this time to
    /// restock any caches they may hold.
    fn done(&self) {}
}
#[cfg(feature = "nightly")]
unsafe impl<T: core::alloc::Allocator> Allocator for T {
    fn allocate(&self) -> Option<NonNull<Bt>> {
        let layout = core::alloc::Layout::new::<Bt>();
        let ptr = <Self as core::alloc::Allocator>::allocate(self, layout);
        ptr.map(|ptr| ptr.cast()).ok()
    }
    unsafe fn deallocate(&self, ptr: NonNull<Bt>) {
        let layout = core::alloc::Layout::new::<Bt>();
        unsafe { <Self as core::alloc::Allocator>::deallocate(self, ptr.cast(), layout) }
    }
}
