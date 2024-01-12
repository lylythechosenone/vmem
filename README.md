# What is this?
Vmem is a resource management system theorized by Jeff Bonwick and Jonathan
Adams in *[Magazines and Vmem: Extending the Slab Allocator to Many CPUs and
Arbitrary Resources][1]*. It provides O(1) allocation and deallocation of any
opaque numerical "resource," such as a block of memory or a process ID.

This particular implementation provides a safe vmem allocator for use inside of
my custom kernel, `velvet`. I am additionally submitting it as my AP Computer
Science Principles Create Task. It aims to conform exactly to the spec laid out
in the aformentioned paper, however, some changes may have been made for pure
practicality.

# What's missing?
Quantum caches were left out of this implementation because they would be more
easily implemented inside of a more specific heap allocator. However, it is
still recommended to cache allocations, especially on arenas which are used as
sources.

Additionally, constrained allocations with [`AllocPolicy::NextFit`] are not
supported, simply because this is not incredibly useful, despite taking a
non-trivial amount of work to implement.

# Crate features
- `nightly` - enables an implementation of [`alloc::Allocator`] for all types
  that also implement [`core::alloc::Allocator`].
- `std` - enables an implementation of [`lock::Lock`] for [`std::sync::Mutex`]
- `spin` - enables an implementation of [`lock::Lock`] for [`spin::Mutex`]

# References
This crate was written with reference to [xvanc's Rust implementation][2], as
well as the NetBSD C implementation it references. No code was directly copied,
and any found issues were corrected. Both of the above implementations were
designed to be placed inside of the kernel that they were written for. In
contrast, this implementation is designed to work in nearly any environment (it
even works in userspace, as seen in the tests!)

# Reporting issues
If you find any issues with this crate, including bugs, memory leaks, panics
(other than the one listed for [`xalloc`](Arena::xalloc) below), or undefined
behavior, please open an issue on the [GitHub
repository](https://github.com/lylythechosenone/vmem).

# Licensing
This crate is licensed under your choice of either of the MIT or Apache 2.0 licenses.

[1]:
    https://www.usenix.org/legacy/event/usenix01/full_papers/bonwick/bonwick.pdf
[2]: https://github.com/xvanc/vmem/tree/main