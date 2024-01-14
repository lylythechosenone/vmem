//! Error types used across the crate.

use core::fmt::Display;

/// [`core::result::Result`] with [`Error`] as the error type.
pub type Result<T> = core::result::Result<T, Error>;

#[derive(PartialEq, Eq, Debug)]
/// An error returned from a function in this crate.
pub enum Error {
    /// The specified quantum value was not a power of two.
    InvalidQuantum,
    /// The allocator returned an error.
    AllocatorError,
    /// The operation could not be performed because the arena has no space
    /// available.
    Empty,
    /// The block could not be freed because it was never allocated, or it was
    /// already removed.
    NoSuchAllocation,
    /// Space could not be imported because there was no source to import from.
    NoSource,
    /// The span would wrap around the address space.
    WrappingSpan,
    /// The span was not aligned to the quantum.
    UnalignedSpan,
    /// Attempted to allocate a zero-sized block.
    AllocZeroSize,
    /// Unknown error, returned by the source.
    Other(&'static str),
}
impl Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidQuantum => write!(f, "the specified quantum was not a power of two"),
            Self::AllocatorError => write!(f, "the allocator returned an error"),
            Self::Empty => write!(f, "empty"),
            Self::NoSuchAllocation => write!(f, "no such allocation"),
            Self::NoSource => write!(f, "no source"),
            Self::WrappingSpan => write!(f, "invalid span"),
            Self::UnalignedSpan => write!(f, "this span would wrap around the address space"),
            Self::AllocZeroSize => write!(f, "attempted to allocate a zero-sized block"),
            Self::Other(s) => write!(f, "{}", s),
        }
    }
}
