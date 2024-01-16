#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(test, doc, feature = "std")), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![deny(missing_docs)]

use core::{cell::UnsafeCell, fmt::Debug, num::NonZeroUsize, ptr::NonNull};

use allocation_table::AllocationTable;
use freelists::Freelists;
use list::{SegmentList, SpecialList};

pub use crate::bt::Bt;
use crate::bt::{Link, Type};

#[doc(inline)]
pub use alloc::*;
#[doc(inline)]
pub use error::*;
#[doc(inline)]
pub use layout::*;
#[doc(inline)]
pub use lock::*;

pub mod alloc;
pub mod error;
pub mod layout;
pub mod lock;

mod allocation_table;
mod bt;
mod freelists;
mod list;

#[derive(PartialEq, Eq, Clone, Copy)]
/// An allocation policy.
pub enum AllocPolicy {
    /// Allocate from the first block found that has a size greater than or
    /// equal to the requested size. This can cause fragmentation, but it is
    /// still generally the recommended policy, as it is O(1).
    InstantFit,
    /// Allocate the smallest block that can fit the requested size. This
    /// framgents less than [`InstantFit`](AllocPolicy::InstantFit), but is O(n)
    /// in the worst case.
    BestFit,
    /// Allocate from a block after the last-allocated block. This guarantees
    /// that allocations will not be reused, even after they are freed, until
    /// the arena wraps around again. This is beneficial for process IDs, for
    /// example, where re-allocating the same ID instantly could cause a
    /// spurious kill left over from the first process. Like
    /// [`InstantFit`](AllocPolicy::InstantFit), this policy does not take
    /// wasted size into account. However, it is not quite O(1), because it
    /// needs to traverse list to find the next block. It will likely be close
    /// to O(1), but could be O(n) in the worst case.
    NextFit,
}

/// Something that can be used as a source for an arena. See
/// [`Arena`](Arena#importing-from-a-source) for more details.
pub trait Source: Sync {
    /// Import a block that satisfies `Layout` from this source, returning its
    /// base.
    ///
    /// # Panics
    /// This function must not panic. If it fails, it should return an error.
    fn import(&self, layout: Layout) -> error::Result<usize>;
    /// Release a block of memory that was previously imported from this source.
    ///
    /// # Panics
    /// This function must not panic. If it fails, it should return an error.
    ///
    /// # Safety
    /// The base and size must point to a valid block of memory that was
    /// allocated through [`import`](Source::import) from this source, and was
    /// not [`release`](Source::release)d yet.
    unsafe fn release(&self, base: usize, size: usize) -> error::Result<()>;
}
impl<'label, 'src, A: alloc::Allocator + Sync, L: lock::Lock + Sync> Source
    for Arena<'label, 'src, A, L>
{
    fn import(&self, layout: Layout) -> error::Result<usize> {
        match (layout.min(), layout.max(), layout.phase(), layout.nocross()) {
            (None, None, None, None) if layout.align() <= self.quantum => {
                self.alloc(layout.size(), AllocPolicy::InstantFit)
            }
            _ => self.xalloc(layout, AllocPolicy::InstantFit),
        }
    }

    unsafe fn release(&self, base: usize, _size: usize) -> error::Result<()> {
        self.free(base)
    }
}

/// A vmem arena.
///
/// This arena can be used for allocation of any resource that can be
/// represented by a base and a length. However, it is quite inefficient in its
/// memory usage for small allocations, so it is recommended to allocate larger
/// blocks and then suballocate from those, unless memory usage is not a
/// concern.
///
/// # Usage
/// In order to create an arena, two things are needed:
/// - **A locking mechanism**. You have many choices. Whatever you decide to
///   use, it must implement [`lock::Lock`]. The trait is implemented by
///   [`spin::Mutex<()>`] by default, but that does not mean that you should use
///   [`spin`]'s mutex. [Spinlocks are rarely the right choice for a
///   lock](https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html).
/// - **An allocator**. This is the type that will be used to allocate the
///   boundary tags used within the allocator. It must implement the
///   [`alloc::Allocator`] trait. With the `nightly` feature, the trait is
///   implemented for all types that implement [`core::alloc::Allocator`].
///
/// Once you have these things, you can move on to [`Arena::create`]:
/// ```rust
/// # #![feature(allocator_api)]
/// # use vmem::{Arena};
/// # use std::alloc::Global as Allocator;
/// # type Lock = std::sync::Mutex<()>;
/// let arena = Arena::<_, Lock>::create("test", 8, None, Allocator).unwrap();
/// ```
/// > #### Why `unwrap`?
/// > The `create` function only returns an error if the specified quantum value
/// > is not a power of two. Since we know that 8 is a power of two, we can
/// > unwrap the value without worrying about any panics.
///
/// ## Filling the arena
/// Without a source, arenas are empty by default. In order to allocate from
/// them, you must first add a span via [`Arena::add_span`]. This function takes
/// a base and a length, and marks it as available for allocation.
///
/// ## Importing from a source
/// A source can be another arena, or any other type that implements [`Source`].
/// In order to add a source to an arena, you must pass it to the parameter
/// `source` during creation. Once a source is specified, allocations will be
/// redirected there (unless the arena has its own free spans available).
pub struct Arena<'label, 'src, A: alloc::Allocator, L: lock::Lock> {
    label: &'label str,
    lock: L,
    inner: UnsafeCell<ArenaInner>,
    source: Option<&'src dyn Source>,
    allocator: A,
    quantum: usize,
}
impl<'label, 'src, A: alloc::Allocator, L: lock::Lock> Arena<'label, 'src, A, L> {
    /// Create a new empty arena.
    ///
    /// # Parameters
    /// - `label` - a label for the arena. This is used for debugging purposes.
    /// - `quantum` - the quantum of the arena. It is the smallest transactional
    ///  unit in the arena (meaning that any allocations within the arena will
    ///  be rounded up to and aligned to a multiple of it), and must be a power
    ///  of two.
    /// - `source` - an optional source for allocations. If specified, any calls
    ///   to [`alloc`](Arena::alloc) or [`xalloc`](Arena::xalloc) that fail will
    ///   be forwarded to the source. If not specified, allocations will fail
    ///   directly if the arena is empty.
    /// - `allocator` - the allocator to use for allocating boundary tags.
    ///
    /// # Returns
    /// If the quantum is not a power of two, [`Error::InvalidQuantum`] will be
    /// returned. Otherwise, the function will return an arena
    pub fn create(
        label: &'label str,
        quantum: usize,
        source: Option<&'src dyn Source>,
        allocator: A,
    ) -> error::Result<Self> {
        if !quantum.is_power_of_two() {
            return Err(Error::InvalidQuantum);
        }

        let segment_list = SegmentList::EMPTY;
        let freelists = Freelists::new();
        let allocation_table = AllocationTable::new();

        Ok(Self {
            label,
            lock: L::default(),
            inner: UnsafeCell::new(ArenaInner {
                segment_list,
                freelists,
                allocation_table,
                last_allocated: None,
                next_fit_offset: None,
            }),
            allocator,
            source,
            quantum,
        })
    }

    /// Add a span to the arena. The span will be used for future allocations.
    ///
    /// # Parameters
    /// - `base` - the base of the span. This is the address of the first byte
    ///   or index of the span. Do note that it is **not** a multiple of
    ///   quantum, but the actual value.
    /// - `len` - the length of the span. This is the number of bytes or indices
    ///   in the span. Do note that it is **not** a multiple of quantum, but the
    ///   actual value.
    ///
    /// # Returns
    /// If the span could not be added, one of these errors will be returned:
    /// - [`Error::AllocatorError`] - the allocator could not allocate a
    ///   boundary tag to support this span.
    /// - [`Error::AllocZeroSize`] - the span has no size.
    /// - [`Error::UnalignedSpan`] - the span is not aligned to `quantum`
    /// - [`Error::WrappingSpan`] - the span could not be added because it would
    ///   overflow.
    pub fn add_span(&self, base: usize, len: usize) -> error::Result<()> {
        if len == 0 {
            return Err(Error::AllocZeroSize);
        }
        if usize::MAX - base < len {
            return Err(Error::WrappingSpan);
        }
        if base % self.quantum != 0 || len % self.quantum != 0 {
            return Err(Error::UnalignedSpan);
        }
        let guard = self.lock.lock();
        unsafe { (*self.inner.get()).add_span(base, len, false, &self.allocator)? };
        drop(guard);

        self.allocator.done();

        Ok(())
    }

    /// Borrow a span from the source, and add it to the arena.
    ///
    /// # Parameters
    /// - `layout` - the layout of the span to borrow. See [`Layout`] for more
    ///   details.
    ///
    /// # Returns
    /// If a span could not be borrowed, this function will forward the error
    /// given by the source. The function could also return one of these errors:
    /// - [`Error::NoSource`] - no source was specified for this arena.
    /// - [`Error::AllocatorError`] - the allocator could not allocate a boundary
    ///   tag to support this span.
    pub fn import(&self, mut layout: Layout) -> error::Result<()> {
        layout.align_up_to(self.quantum);
        layout.set_size(layout.size().next_multiple_of(self.quantum));

        let source = self.source.ok_or(Error::NoSource)?;
        let base = source.import(layout.clone())?;

        let guard = self.lock.lock();
        unsafe { (*self.inner.get()).add_span(base, layout.size(), true, &self.allocator)? };
        drop(guard);

        self.allocator.done();

        Ok(())
    }

    /// Allocates a block based on a size and an allocation policy.
    ///
    /// # Parameters
    /// - `size` - the size of the block to allocate. This is the number of
    ///   bytes or indices in the block. Do note that it is **not** a multiple
    ///   of quantum, but the actual value.
    /// - `policy` - the allocation policy to use. See [`AllocPolicy`] for more
    ///   details.
    ///
    /// # Returns
    /// If a block could not be allocated, one of the following errors will be
    /// returned:
    /// - [`Error::Empty`] - the arena is empty, and no source was specified to
    ///   borrow from.
    /// - [`Error::AllocatorError`] - the allocator could not allocate a
    ///   boundary tag to support this block.
    /// - [`Error::AllocZeroSize`] - the requested allocation has no size.
    ///
    /// If a source is specified, this function will forward any errors given by
    /// it.
    pub fn alloc(&self, size: usize, policy: AllocPolicy) -> error::Result<usize> {
        if size == 0 {
            return Err(Error::AllocZeroSize);
        }
        let size = size.next_multiple_of(self.quantum);
        let guard = self.lock.lock();
        let result = unsafe { (*self.inner.get()).alloc(size, policy, &self.allocator) };
        drop(guard);

        self.allocator.done();

        result.or_else(|e| {
            if e == Error::Empty && self.source.is_some() {
                self.import(Layout::from_size_align(size, self.quantum).unwrap())?;
                self.alloc(size, policy)
            } else {
                Err(e)
            }
        })
    }

    /// Allocates a block based on a layout and an allocation policy. See
    /// [`Layout`] for more details on what features are supported.
    ///
    /// # Parameters
    /// - `layout` - the layout of the block to allocate.
    /// - `policy` - the allocation policy to use. See [`AllocPolicy`] for more
    ///   details.
    ///
    /// # Returns
    /// If a block could not be allocated, one of the following errors will be
    /// returned:
    /// - [`Error::Empty`] - the arena is empty, and no source was specified to
    ///  borrow from.
    /// - [`Error::AllocatorError`] - the allocator could not allocate a boundary
    /// tag to support this block.
    /// - [`Error::AllocZeroSize`] - the requested allocation has no size.
    ///
    /// If a source is specified, this function will forward any errors given by
    /// it.
    ///
    /// # Panics
    /// This function will panic if you attempt to call it with
    /// [`AllocPolicy::NextFit`]. This policy is purposefully unsupported.
    pub fn xalloc(&self, mut layout: Layout, policy: AllocPolicy) -> error::Result<usize> {
        if policy == AllocPolicy::NextFit {
            // if we panic after the lock is held, we could cause a poison, and
            // poison is guaranteed to never happen.
            unimplemented!("next fit constrained allocations are not supported");
        }

        layout.set_size(layout.size().next_multiple_of(self.quantum));
        let guard = self.lock.lock();
        let result = unsafe { (*self.inner.get()).xalloc(layout.clone(), policy, &self.allocator) };
        drop(guard);

        self.allocator.done();

        result.or_else(|_| {
            if self.source.is_some() {
                self.import(layout.clone())?;
                self.xalloc(layout, policy)
            } else {
                Err(Error::Empty)
            }
        })
    }

    /// Free a block of memory.
    ///
    /// # Parameters
    /// - `base` - the base of the block to free. This is the address of the
    ///  first byte or index of the block. Do note that it is **not** a multiple
    /// of quantum, but the actual value.
    ///
    /// # Returns
    /// If the block could not be freed, one of the following errors will be
    /// returned:
    /// - [`Error::NoSuchAllocation`] - the block was not allocated by this
    ///   arena, or was already freed.
    pub fn free(&self, base: usize) -> error::Result<()> {
        let guard = self.lock.lock();

        let inner = unsafe { &mut *self.inner.get() };
        let bt = inner.free(base, &self.allocator)?;
        let to_free = match (
            unsafe { bt.as_ref() }.link.prev,
            unsafe { bt.as_ref() }.link.next,
        ) {
            (Some(prev), next)
                if unsafe { prev.as_ref() }.ty == Type::Borrowed
                    && next
                        .map(|bt| unsafe { bt.as_ref() }.is_span())
                        .unwrap_or(true) =>
            {
                let base = unsafe { prev.as_ref() }.base;
                unsafe {
                    inner.segment_list.remove(prev);
                    inner.segment_list.remove(bt);
                }

                unsafe {
                    self.allocator.deallocate(prev);
                    self.allocator.deallocate(bt);
                }

                Some(base)
            }
            _ => {
                let freelist = inner.freelists.list_of_mut(unsafe { bt.as_ref() }.len);
                unsafe {
                    freelist.insert(bt);
                }
                None
            }
        };

        drop(guard);

        self.allocator.done();

        if let Some(base) = to_free {
            unsafe {
                self.source
                    .ok_or(Error::NoSource)?
                    .release(base, bt.as_ref().len)?;
            }
        }

        Ok(())
    }

    /// Get the total space contained in this arena.
    ///
    /// Note that this iterates the entire list, and as such is not incredibly
    /// performant. This may change in the future.
    ///
    /// # Returns
    /// The total space contained in this arena, in terms of bytes/indices. This
    /// includes both allocated and free space, including borrowed space.
    pub fn total_space(&self) -> usize {
        let guard = self.lock.lock();
        let inner = unsafe { &*self.inner.get() };
        let total = unsafe { inner.segment_list.iter() }
                .filter(|bt| unsafe { bt.as_ref() }.ty == Type::Span || unsafe { bt.as_ref() }.ty == Type::Borrowed)
                .fold(0, |acc, bt| acc + unsafe { bt.as_ref() }.len);
        drop(guard);
        total
    }

    /// Get the allocated space contained in this arena.
    ///
    /// Note that this iterates the entire list, and as such is not incredibly
    /// performant. This may change in the future.
    ///
    /// # Returns
    /// The allocated space contained in this arena, in terms of bytes/indices.
    /// This includes both borrowed and non-borrowed allocations.
    pub fn allocated_space(&self) -> usize {
        let guard = self.lock.lock();
        let inner = unsafe { &*self.inner.get() };
        let allocated = unsafe { inner.segment_list.iter() }
            .filter(|bt| unsafe { bt.as_ref() }.ty == Type::Allocated)
            .fold(0, |acc, bt| acc + unsafe { bt.as_ref() }.len);
        drop(guard);
        allocated
    }

    /// Get the free space contained in this arena.
    ///
    /// Note that this iterates the entire list, and as such is not incredibly
    /// performant. This is subject to change in the future.
    ///
    /// # Returns
    /// The free space contained in this arena, in terms of bytes/indices.
    /// This includes both borrowed and non-borrowed allocations.
    pub fn free_space(&self) -> usize {
        let guard = self.lock.lock();
        let inner = unsafe { &*self.inner.get() };
        let free = unsafe { inner.segment_list.iter() }
            .filter(|bt| unsafe { bt.as_ref() }.ty == Type::Free)
            .fold(0, |acc, bt| acc + unsafe { bt.as_ref() }.len);
        drop(guard);
        free
    }

    /// Get the borrowed space contained in this arena.
    ///
    /// Note that this iterates the entire list, and as such is not incredibly
    /// performant. This is subject to change in the future.
    ///
    /// # Returns
    /// The borrowed space contained in this arena, in terms of bytes/indices.
    /// This includes both free and allocated borrowed space.
    pub fn borrowed_space(&self) -> usize {
        let guard = self.lock.lock();
        let inner = unsafe { &*self.inner.get() };
        let borrowed = unsafe { inner.segment_list.iter() }
            .filter(|bt| unsafe { bt.as_ref() }.ty == Type::Borrowed)
            .fold(0, |acc, bt| acc + unsafe { bt.as_ref() }.len);
        drop(guard);
        borrowed
    }

    /// Get the label for this arena.
    pub fn label(&self) -> &'label str {
        self.label
    }
}
impl<'label, 'src, A: alloc::Allocator, L: lock::Lock> Debug for Arena<'label, 'src, A, L> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "Arena {} with:", self.label)?;
        let guard = self.lock.lock();

        let inner = unsafe { &*self.inner.get() };
        for bt in unsafe { inner.segment_list.iter() } {
            writeln!(f, "  {:?}", unsafe { bt.as_ref() })?;
        }

        writeln!(
            f,
            "  Last alloc: {:?}",
            inner.last_allocated.map(|v| unsafe { v.as_ref() })
        )?;
        writeln!(
            f,
            "  Next fit offset: {:#x?}",
            inner.next_fit_offset.map(NonZeroUsize::get).unwrap_or(0)
        )?;

        drop(guard);

        Ok(())
    }
}
impl<'label, 'src, A: alloc::Allocator, L: lock::Lock> Drop for Arena<'label, 'src, A, L> {
    fn drop(&mut self) {
        let guard = self.lock.lock();
        let inner = unsafe { &mut *self.inner.get() };
        for bt in unsafe { inner.segment_list.iter() } {
            if unsafe { bt.as_ref() }.ty == Type::Borrowed {
                unsafe {
                    self.source
                        .unwrap()
                        .release(bt.as_ref().base, bt.as_ref().len)
                        .unwrap();
                }
            }
            unsafe {
                self.allocator.deallocate(bt);
            }
        }
        drop(guard);
    }
}
unsafe impl<'label, 'src, A: alloc::Allocator + Sync, L: lock::Lock + Sync> Sync
    for Arena<'label, 'src, A, L>
{
}
unsafe impl<'label, 'src, A: alloc::Allocator + Send, L: lock::Lock + Send> Send
    for Arena<'label, 'src, A, L>
{
}

struct ArenaInner {
    segment_list: SegmentList,
    freelists: Freelists,
    allocation_table: AllocationTable,
    last_allocated: Option<NonNull<Bt>>,
    next_fit_offset: Option<NonZeroUsize>,
}
impl ArenaInner {
    fn add_span(
        &mut self,
        base: usize,
        len: usize,
        borrowed: bool,
        allocator: &impl alloc::Allocator,
    ) -> error::Result<()> {
        let span = allocator.allocate().ok_or(Error::AllocatorError)?;
        let bt = allocator.allocate().ok_or_else(|| {
            unsafe {
                // We don't want to leak memory in the case that the second
                // allocation fails.
                allocator.deallocate(span);
            }
            Error::AllocatorError
        })?;

        unsafe {
            span.as_ptr().write(Bt {
                link: Link::UNLINKED,
                base,
                len,
                special: Link::UNLINKED,
                ty: if borrowed { Type::Borrowed } else { Type::Span },
            })
        }
        unsafe {
            bt.as_ptr().write(Bt {
                link: Link::UNLINKED,
                base,
                len,
                special: Link::UNLINKED,
                ty: Type::Free,
            })
        }

        unsafe {
            let (prev, next) = self.segment_list.insertion_point(base);
            self.segment_list.insert_between(span, prev, next);
            self.segment_list.insert_between(bt, Some(span), next);
        }
        let freelist = self.freelists.list_of_mut(len);
        unsafe {
            freelist.insert(bt);
        }

        Ok(())
    }

    fn split(
        &mut self,
        new_size: usize,
        base: usize,
        len: usize,
        mut bt: NonNull<Bt>,
        allocator: &impl alloc::Allocator,
    ) -> error::Result<()> {
        if len == new_size {
            return Ok(());
        }

        unsafe { bt.as_mut() }.len = new_size;

        let after_split = allocator.allocate().ok_or(Error::AllocatorError)?;
        unsafe {
            after_split.as_ptr().write(Bt {
                link: Link::UNLINKED,
                base: base + new_size,
                len: len - new_size,
                special: Link::UNLINKED,
                ty: Type::Free,
            })
        }
        unsafe {
            self.segment_list.insert_after(after_split, bt);
        }
        let freelist = self.freelists.list_of_mut(len - new_size);
        unsafe {
            freelist.insert(after_split);
        }

        Ok(())
    }

    fn non_empty_freelist_for(&mut self, aligned_size: usize) -> error::Result<&mut SpecialList> {
        let mut freelist_n = aligned_size.next_power_of_two();
        let mut freelist = self.freelists.list_for_mut(freelist_n);
        while freelist.is_empty() {
            freelist_n = freelist_n.checked_mul(2).ok_or(Error::Empty)?;
            freelist = self.freelists.list_for_mut(freelist_n);
        }
        Ok(unsafe { &mut *(freelist as *mut _) })
    }

    fn alloc(
        &mut self,
        size: usize,
        policy: AllocPolicy,
        allocator: &impl alloc::Allocator,
    ) -> error::Result<usize> {
        let mut bt = match policy {
            AllocPolicy::InstantFit => {
                let freelist = self.non_empty_freelist_for(size)?;

                unsafe { freelist.pop() }.unwrap()
            }
            AllocPolicy::BestFit => {
                let bt = if !size.is_power_of_two() {
                    let smaller_freelist = self.freelists.list_of_mut(size);
                    if !smaller_freelist.is_empty() {
                        unsafe { smaller_freelist.iter() }
                            .filter(|bt| unsafe { bt.as_ref() }.len >= size)
                            .min_by_key(|bt| unsafe { bt.as_ref() }.len - size)
                            .map(|bt| unsafe {
                                smaller_freelist.remove(bt);
                                bt
                            })
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(bt) = bt {
                    bt
                } else {
                    let freelist = self.non_empty_freelist_for(size)?;
                    let bt = unsafe { freelist.iter() }
                        .min_by_key(|bt| unsafe { bt.as_ref() }.len)
                        .unwrap();
                    unsafe {
                        freelist.remove(bt);
                    }
                    bt
                }
            }
            AllocPolicy::NextFit => {
                if let Some(mut bt) = self.last_allocated {
                    if let Some(offset) = self.next_fit_offset {
                        if unsafe { bt.as_ref() }.len - offset.get() >= size {
                            let base = unsafe { bt.as_ref() }.base;
                            let len = unsafe { bt.as_ref() }.len;
                            let freelist = self.freelists.list_of_mut(len);
                            unsafe {
                                freelist.remove(bt);
                            }

                            self.split(offset.get(), base, len, bt, allocator)?;
                        }
                    }
                    bt = match unsafe { bt.as_ref() }.link.next {
                        Some(bt) => bt,
                        None => return self.alloc(size, AllocPolicy::InstantFit, allocator),
                    };
                    while unsafe { bt.as_ref() }.ty != Type::Free
                        || unsafe { bt.as_ref() }.len < size
                    {
                        bt = match unsafe { bt.as_ref() }.link.next {
                            Some(bt) => bt,
                            None => return self.alloc(size, AllocPolicy::InstantFit, allocator),
                        };
                    }

                    let freelist = self.freelists.list_of_mut(unsafe { bt.as_ref() }.len);
                    unsafe {
                        freelist.remove(bt);
                    }

                    bt
                } else {
                    return self.alloc(size, AllocPolicy::InstantFit, allocator);
                }
            }
        };

        let base = unsafe { bt.as_ref() }.base;
        let len = unsafe { bt.as_ref() }.len;

        self.split(size, base, len, bt, allocator).map_err(|e| {
            let freelist = self.freelists.list_of_mut(len);
            unsafe {
                freelist.insert(bt);
            }
            e
        })?;

        unsafe { bt.as_mut() }.ty = Type::Allocated;
        unsafe {
            self.allocation_table.insert(bt);
        }

        self.last_allocated = Some(bt);
        self.next_fit_offset = None;

        Ok(base)
    }

    fn xalloc(
        &mut self,
        layout: Layout,
        policy: AllocPolicy,
        allocator: &impl alloc::Allocator,
    ) -> error::Result<usize> {
        let (mut bt, offset) = match policy {
            AllocPolicy::InstantFit => {
                let freelist = self.non_empty_freelist_for(layout.size())?;
                let (bt, offset) = unsafe { freelist.iter() }
                    .find_map(|bt| {
                        unsafe { bt.as_ref() }
                            .satisfies_layout(&layout)
                            .map(|offset| (bt, offset))
                    })
                    .ok_or(Error::Empty)?;

                unsafe {
                    freelist.remove(bt);
                }

                (bt, offset)
            }
            AllocPolicy::BestFit => {
                let bt = if !layout.size().is_power_of_two() {
                    let smaller_freelist = self.freelists.list_of_mut(layout.size());
                    if !smaller_freelist.is_empty() {
                        unsafe { smaller_freelist.iter() }
                            .filter_map(|bt| {
                                unsafe { bt.as_ref() }
                                    .satisfies_layout(&layout)
                                    .map(|offset| (bt, offset))
                            })
                            .min_by_key(|(bt, _)| unsafe { bt.as_ref() }.len - layout.size())
                            .map(|(bt, offset)| unsafe {
                                smaller_freelist.remove(bt);
                                (bt, offset)
                            })
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(bt) = bt {
                    bt
                } else {
                    let freelist = self.non_empty_freelist_for(layout.size())?;
                    let (bt, offset) = unsafe { freelist.iter() }
                        .filter_map(|bt| {
                            unsafe { bt.as_ref() }
                                .satisfies_layout(&layout)
                                .map(|offset| (bt, offset))
                        })
                        .min_by_key(|(bt, _)| unsafe { bt.as_ref() }.len)
                        .ok_or(Error::Empty)?;
                    unsafe {
                        freelist.remove(bt);
                    }
                    (bt, offset)
                }
            }
            AllocPolicy::NextFit => unreachable!(),
        };

        let base = unsafe { bt.as_ref() }.base;
        let len = unsafe { bt.as_ref() }.len;

        if offset != 0 {
            self.split(offset, base, len, bt, allocator).map_err(|e| {
                let freelist = self.freelists.list_of_mut(unsafe { bt.as_ref() }.len);
                unsafe {
                    freelist.insert(bt);
                }
                e
            })?;

            let freelist = self.freelists.list_of_mut(unsafe { bt.as_ref() }.len);
            unsafe {
                freelist.insert(bt);
            }

            bt = unsafe { bt.as_ref() }.link.next.unwrap();
        }

        let aligned_base = base + offset;

        let len = unsafe { bt.as_ref() }.len;

        self.split(layout.size(), aligned_base, len - offset, bt, allocator)?;

        let freelist = self.freelists.list_of_mut(len);
        unsafe {
            freelist.remove(bt);
        }

        unsafe { bt.as_mut() }.ty = Type::Allocated;
        unsafe {
            self.allocation_table.insert(bt);
        }

        self.last_allocated = Some(bt);
        self.next_fit_offset = None;

        Ok(aligned_base)
    }

    fn free(
        &mut self,
        base: usize,
        allocator: &impl alloc::Allocator,
    ) -> error::Result<NonNull<Bt>> {
        let mut bt =
            unsafe { self.allocation_table.remove(base) }.ok_or(Error::NoSuchAllocation)?;
        unsafe { bt.as_mut() }.ty = Type::Free;

        match unsafe { bt.as_ref() }.link.prev {
            Some(mut prev)
                if unsafe { prev.as_ref() }.ty == Type::Free
                    && unsafe { prev.as_ref() }.base + unsafe { prev.as_ref() }.len == base =>
            {
                let prev_mut = unsafe { prev.as_mut() };
                let freelist = self.freelists.list_of_mut(prev_mut.len);
                unsafe {
                    freelist.remove(prev);
                }
                prev_mut.len += unsafe { bt.as_ref() }.len;
                if self.last_allocated == Some(bt) {
                    self.last_allocated = Some(prev);
                }
                unsafe {
                    self.segment_list.remove(bt);
                }
                unsafe {
                    allocator.deallocate(bt);
                }
                bt = prev;
            }
            _ => {}
        }

        match unsafe { bt.as_ref() }.link.next {
            Some(next)
                if unsafe { next.as_ref() }.ty == Type::Free
                    && base + unsafe { bt.as_ref() }.len == unsafe { next.as_ref() }.base =>
            {
                let bt_mut = unsafe { bt.as_mut() };
                if self.last_allocated == Some(next) {
                    self.last_allocated = Some(bt);
                } else if self.last_allocated == Some(bt) && self.next_fit_offset.is_none() {
                    self.next_fit_offset = NonZeroUsize::new(unsafe { bt.as_ref() }.len);
                }
                bt_mut.len += unsafe { next.as_ref() }.len;
                let freelist = self.freelists.list_of_mut(unsafe { next.as_ref() }.len);
                unsafe {
                    freelist.remove(next);
                }
                unsafe {
                    self.segment_list.remove(next);
                }
                unsafe {
                    allocator.deallocate(next);
                }
            }
            _ => {}
        }

        Ok(bt)
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::Global;
    use std::sync::Mutex;

    use super::*;

    fn create_arena() -> Arena<'static, 'static, Global, Mutex<()>> {
        Arena::<_, Mutex<()>>::create("root", 8, None, Global).unwrap()
    }

    fn create_arena_source(source: &dyn Source) -> Arena<'static, '_, Global, Mutex<()>> {
        Arena::<_, Mutex<()>>::create("borrower", 8, Some(source), Global).unwrap()
    }

    #[test]
    fn invalid_quantum() {
        assert!(matches!(
            Arena::<_, Mutex<()>>::create("test", 42, None, Global),
            Err(Error::InvalidQuantum)
        ));
    }

    #[test]
    fn instant_fit() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x1000).unwrap();
        println!("{my_arena:?}");
        my_arena.alloc(0x10, AllocPolicy::InstantFit).unwrap();
        println!("{my_arena:?}");
        my_arena.alloc(0x10, AllocPolicy::InstantFit).unwrap();
        println!("{my_arena:?}");
        assert!(matches!(
            my_arena.alloc(0x1000, AllocPolicy::InstantFit),
            Err(Error::Empty)
        ))
    }

    #[test]
    fn best_fit() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x400).unwrap();
        my_arena.add_span(0x1400, 0x100).unwrap();
        my_arena.add_span(0x1500, 0x200).unwrap();
        println!("{my_arena:?}");
        let base = my_arena.alloc(0x10, AllocPolicy::BestFit).unwrap();
        assert_eq!(base, 0x1400);
        println!("{my_arena:?}");
        let base = my_arena.alloc(0x100, AllocPolicy::BestFit).unwrap();
        assert_eq!(base, 0x1500);
    }

    #[test]
    fn next_fit() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x1000).unwrap();
        println!("{my_arena:?}");
        let base = my_arena.alloc(0x10, AllocPolicy::NextFit).unwrap();
        println!("{my_arena:?}");
        my_arena.free(base).unwrap();
        println!("{my_arena:?}");
        let new_base = my_arena.alloc(0x10, AllocPolicy::NextFit).unwrap();
        assert_ne!(base, new_base);
    }

    #[test]
    fn xalloc_instant_fit() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x1000).unwrap();
        println!("{my_arena:?}");
        let base = my_arena
            .xalloc(
                Layout::from_size_align(0x10, 0x10).unwrap(),
                AllocPolicy::InstantFit,
            )
            .unwrap();
        println!("{my_arena:?}");
        assert!(base % 0x10 == 0);
        let base = my_arena
            .xalloc(
                Layout::from_size_align(0x10, 0x100).unwrap(),
                AllocPolicy::InstantFit,
            )
            .unwrap();
        println!("{my_arena:?}");
        assert!(base % 0x100 == 0);
        let base = my_arena
            .xalloc(
                Layout::from_size_align(0x10, 0x10).unwrap(),
                AllocPolicy::InstantFit,
            )
            .unwrap();
        assert!(base % 0x10 == 0);
    }

    #[test]
    fn xalloc_best_fit() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x400).unwrap();
        my_arena.add_span(0x1400, 0x100).unwrap();
        my_arena.add_span(0x1500, 0x200).unwrap();
        println!("{my_arena:?}");
        let base = my_arena
            .xalloc(
                Layout::from_size_align(0x10, 0x100).unwrap(),
                AllocPolicy::BestFit,
            )
            .unwrap();
        assert_eq!(base, 0x1400);
        println!("{my_arena:?}");
        let base = my_arena
            .xalloc(
                Layout::from_size_align(0x100, 0x10).unwrap(),
                AllocPolicy::BestFit,
            )
            .unwrap();
        assert_eq!(base, 0x1500);
    }

    #[test]
    fn free() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x1000).unwrap();
        println!("{my_arena:?}");
        let base = my_arena.alloc(0x10, AllocPolicy::InstantFit).unwrap();
        println!("{my_arena:?}");
        my_arena.free(base).unwrap();
        println!("{my_arena:?}");
        my_arena.alloc(0x1000, AllocPolicy::InstantFit).unwrap();
    }

    #[test]
    fn import() {
        let source = create_arena();
        source.add_span(0x1000, 0x1000).unwrap();
        println!("{source:?}");

        let my_arena = create_arena_source(&source);
        let first_base = my_arena.alloc(0x10, AllocPolicy::InstantFit).unwrap();
        println!("{source:?}");
        println!("{my_arena:?}");

        let my_second_arena = create_arena_source(&source);
        my_second_arena
            .alloc(0x10, AllocPolicy::InstantFit)
            .unwrap();
        println!("{source:?}");
        println!("{my_second_arena:?}");

        let second_base = my_arena
            .xalloc(
                Layout::from_size_align(0x10, 0x100).unwrap(),
                AllocPolicy::InstantFit,
            )
            .unwrap();
        assert_eq!(second_base % 0x100, 0);
        println!("{source:?}");
        println!("{my_arena:?}");

        my_arena.free(first_base).unwrap();
        println!("{source:?}");
        println!("{my_arena:?}");
        my_arena.free(second_base).unwrap();
        println!("{source:?}");
        println!("{my_arena:?}");

        assert_eq!(my_arena.borrowed_space(), 0x0);
    }

    #[test]
    fn metrics() {
        let my_arena = create_arena();
        my_arena.add_span(0x1000, 0x1000).unwrap();
        println!("{my_arena:?}");
        my_arena.alloc(0x10, AllocPolicy::InstantFit).unwrap();
        println!("{my_arena:?}");
        my_arena.alloc(0x10, AllocPolicy::InstantFit).unwrap();
        println!("{my_arena:?}");
        assert_eq!(my_arena.total_space(), 0x1000);
        assert_eq!(my_arena.allocated_space(), 0x20);
        assert_eq!(my_arena.free_space(), 0xfe0);
        assert_eq!(my_arena.borrowed_space(), 0x0);
    }
}
