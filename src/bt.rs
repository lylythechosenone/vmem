use core::{
    fmt::{Debug, Display},
    ptr::NonNull,
};

use crate::layout::Layout;

/// A boundary tag.
///
/// The actual contents is irrelevant. This type should not be
/// directly manipulated. It is only provided to facilitate implementations of
/// the [`Allocator`](crate::alloc::Allocator) trait.
pub struct Bt {
    pub(crate) link: Link,
    pub(crate) base: usize,
    pub(crate) len: usize,
    pub(crate) special: Link,
    pub(crate) ty: Type,
}
impl Bt {
    pub(crate) fn is_span(&self) -> bool {
        self.ty == Type::Span || self.ty == Type::Borrowed
    }

    pub(crate) fn satisfies_layout(&self, layout: &Layout) -> Option<usize> {
        let mut aligned_base = if self.base % layout.align() == 0 {
            if self.len < layout.size() {
                return None;
            }
            self.base + layout.phase().unwrap_or(0)
        } else {
            let aligned_base =
                self.base.next_multiple_of(layout.align()) + layout.phase().unwrap_or(0);
            if aligned_base + layout.size() > self.base + self.len {
                return None;
            }
            aligned_base
        };
        let end = aligned_base + layout.size();

        match (layout.min(), layout.max()) {
            (Some(min), Some(max)) if aligned_base < min || aligned_base > max => return None,
            (Some(min), None) if aligned_base < min => return None,
            (None, Some(max)) if aligned_base > max => return None,
            _ => {}
        }

        match layout.nocross() {
            Some(nocross) if (aligned_base ^ end) & nocross.wrapping_neg() != 0 => {
                aligned_base = aligned_base.next_multiple_of(nocross);
                if aligned_base + layout.size() > self.base + self.len {
                    return None;
                }
            }
            _ => {}
        }

        Some(aligned_base - self.base)
    }
}
impl Debug for Bt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} from {:#x} to {:#x} (len: {:#x})",
            self.ty,
            self.base,
            self.base + self.len,
            self.len
        )
    }
}

pub struct Link {
    pub prev: Option<NonNull<Bt>>,
    pub next: Option<NonNull<Bt>>,
}
impl Link {
    pub const UNLINKED: Self = Link {
        prev: None,
        next: None,
    };
}

#[derive(PartialEq, Eq)]
pub enum Type {
    Free,
    Allocated,
    Span,
    Borrowed,
}
impl Display for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Free => write!(f, "Free"),
            Self::Allocated => write!(f, "Allocated"),
            Self::Span => write!(f, "Span"),
            Self::Borrowed => write!(f, "Borrowed"),
        }
    }
}
