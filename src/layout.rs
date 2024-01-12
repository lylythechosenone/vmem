//! Special layouts for constrained allocations.

use core::num::NonZeroUsize;

#[derive(Clone)]
/// A layout for a constrained allocation. See functions for more details.
///
/// # Usage
/// For a standard Rust type, you can simply use `Layout::new::<T>()` to get a
/// layout object. This type also implements `From<`[`core::alloc::Layout`]`>`,
/// so you can construct it from a standard layout. For cases that are not about
/// a specific type, you can use [`Layout::from_size_align`].
///
/// You can also use the builder functions on the type to further constrain the
/// layout.
pub struct Layout {
    size: usize,
    align: usize,
    phase: Option<NonZeroUsize>,
    nocross: Option<NonZeroUsize>,
    min: Option<NonZeroUsize>,
    max: Option<NonZeroUsize>,
}
impl Layout {
    /// Constructs a new layout from a size and an alignment.
    ///
    /// The size must be non-zero, and the alignment must be a power of two. If
    /// either of these conditions is not met, this function returns `None`.
    pub const fn from_size_align(size: usize, align: usize) -> Option<Self> {
        if !align.is_power_of_two() {
            return None;
        }
        if size == 0 {
            return None;
        }
        Some(Self {
            size,
            align,
            phase: None,
            nocross: None,
            min: None,
            max: None,
        })
    }
    /// Constructs a new layout that matches a standard Rust type.
    pub const fn new<T>() -> Self {
        let core_layout = core::alloc::Layout::new::<T>();
        Self {
            size: core_layout.size(),
            align: core_layout.align(),
            phase: None,
            nocross: None,
            min: None,
            max: None,
        }
    }

    pub(crate) fn set_size(&mut self, size: usize) {
        self.size = size;
    }
    pub(crate) fn align_up_to(&mut self, align: usize) {
        self.align = self.align.max(align);
    }

    /// Set the phase of this layout.
    ///
    /// The phase of a layout is the offset from the alignment boundary that the
    /// allocation should have. For example, if the alignment is 8 and the phase
    /// is 2, then the allocation will be 2 bytes after the nearest 8-byte
    /// boundary.
    pub const fn with_phase(mut self, phase: usize) -> Self {
        self.phase = NonZeroUsize::new(phase);
        self
    }
    /// Set the nocross of this layout.
    ///
    /// The nocross of a layout is an alignment boundary that the allocation
    /// must not contain. For example, if the nocross is 8 and the allocation
    /// would land such that it would contain an 8-byte boundary, then the
    /// allocation would be moved to the next 8-byte boundary. Nocross is
    /// similar to alignment.
    ///
    /// The nocross must be a power of two, and must be greater than or equal to
    /// the size of the layout. If it is equal, you would be better off using
    /// `align` instead.
    pub const fn with_nocross(mut self, align: usize) -> Option<Self> {
        if !align.is_power_of_two() {
            return None;
        }
        if self.size > align {
            return None;
        }
        self.nocross = NonZeroUsize::new(align);
        Some(self)
    }
    /// Set the minimum address/index of this layout.
    pub const fn with_min(mut self, min: usize) -> Self {
        self.min = NonZeroUsize::new(min);
        self
    }
    /// Set the maximum address/index of this layout.
    pub const fn with_max(mut self, max: usize) -> Self {
        self.max = NonZeroUsize::new(max);
        self
    }

    /// Queries the size of this layout.
    ///
    /// The size is non-zero.
    pub fn size(&self) -> usize {
        self.size
    }
    /// Queries the alignment of this layout.
    ///
    /// The alignment is a power of two.
    pub fn align(&self) -> usize {
        self.align
    }
    /// Queries the phase of this layout.
    pub fn phase(&self) -> Option<usize> {
        self.phase.map(NonZeroUsize::get)
    }
    /// Queries the nocross of this layout.
    ///
    /// The nocross is a power of two, and is greater than or equal to the size
    /// of the layout.
    pub fn nocross(&self) -> Option<usize> {
        self.nocross.map(NonZeroUsize::get)
    }
    /// Queries the minimum address/index of this layout.
    pub fn min(&self) -> Option<usize> {
        self.min.map(NonZeroUsize::get)
    }
    /// Queries the maximum address/index of this layout.
    pub fn max(&self) -> Option<usize> {
        self.max.map(NonZeroUsize::get)
    }
}
impl From<core::alloc::Layout> for Layout {
    fn from(core_layout: core::alloc::Layout) -> Self {
        Self {
            size: core_layout.size(),
            align: core_layout.align(),
            phase: None,
            nocross: None,
            min: None,
            max: None,
        }
    }
}
