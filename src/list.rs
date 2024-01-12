use core::ptr::NonNull;

use crate::bt::{Bt, Link};

pub struct SegmentList {
    root: Link,
}
impl SegmentList {
    pub const EMPTY: Self = Self {
        root: Link::UNLINKED,
    };

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.    
    pub unsafe fn insertion_point(
        &mut self,
        base: usize,
    ) -> (Option<NonNull<Bt>>, Option<NonNull<Bt>>) {
        let mut prev = None;
        let mut next = self.root.next;
        while let Some(bt) = next {
            if bt.as_ref().base > base {
                break;
            }
            prev = next;
            next = bt.as_ref().link.next;
        }
        (prev, next)
    }

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    pub unsafe fn insert_between(
        &mut self,
        mut bt: NonNull<Bt>,
        prev: Option<NonNull<Bt>>,
        next: Option<NonNull<Bt>>,
    ) {
        bt.as_mut().link.prev = prev;
        bt.as_mut().link.next = next;
        if let Some(mut prev) = prev {
            prev.as_mut().link.next = Some(bt);
        } else {
            self.root.next = Some(bt);
        }
        if let Some(mut next) = next {
            next.as_mut().link.prev = Some(bt);
        } else {
            self.root.prev = Some(bt);
        }
    }

    // # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    /// Both supplied bts must also be valid.
    pub unsafe fn insert_after(&mut self, bt: NonNull<Bt>, prev: NonNull<Bt>) {
        let next = prev.as_ref().link.next;
        self.insert_between(bt, Some(prev), next);
    }

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    pub unsafe fn remove(&mut self, mut bt: NonNull<Bt>) {
        if let Some(mut prev) = bt.as_ref().link.prev {
            prev.as_mut().link.next = bt.as_ref().link.next;
        } else {
            self.root.next = bt.as_ref().link.next;
        }
        if let Some(mut next) = bt.as_ref().link.next {
            next.as_mut().link.prev = bt.as_ref().link.prev;
        } else {
            self.root.prev = bt.as_ref().link.prev;
        }
        bt.as_mut().link.prev = None;
        bt.as_mut().link.next = None;
    }

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    pub unsafe fn iter(&self) -> SegmentListIter {
        SegmentListIter {
            next: self.root.next,
        }
    }
}
impl Default for SegmentList {
    fn default() -> Self {
        Self::EMPTY
    }
}

pub struct SegmentListIter {
    next: Option<NonNull<Bt>>,
}
impl Iterator for SegmentListIter {
    type Item = NonNull<Bt>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next;
        if let Some(next) = next {
            self.next = unsafe { next.as_ref().link.next };
        }
        next
    }
}

pub struct SpecialList {
    link: Link,
}
impl SpecialList {
    pub const EMPTY: Self = Self {
        link: Link::UNLINKED,
    };

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    /// The supplied bt must also be valid.
    pub unsafe fn insert(&mut self, mut bt: NonNull<Bt>) {
        bt.as_mut().special.prev = None;
        bt.as_mut().special.next = self.link.next;
        if let Some(mut next) = self.link.next {
            next.as_mut().special.prev = Some(bt);
        }
        self.link.next = Some(bt);
    }

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    pub unsafe fn remove(&mut self, mut bt: NonNull<Bt>) {
        if let Some(mut prev) = bt.as_ref().special.prev {
            prev.as_mut().special.next = bt.as_ref().special.next;
        } else {
            self.link.next = bt.as_ref().special.next;
        }
        if let Some(mut next) = bt.as_ref().special.next {
            next.as_mut().special.prev = bt.as_ref().special.prev;
        }
        bt.as_mut().special.prev = None;
        bt.as_mut().special.next = None;
    }

    /// # Safety
    /// No bt in the list may be currently in use, but all must be valid.
    pub unsafe fn pop(&mut self) -> Option<NonNull<Bt>> {
        let next = self.link.next;
        if let Some(mut next) = next {
            self.link.next = next.as_ref().special.next;
            if let Some(mut next) = next.as_ref().special.next {
                next.as_mut().special.prev = None;
            }
            next.as_mut().special = Link::UNLINKED;
        }
        next
    }

    /// # Safety
    /// No bt in the list may have a current mutable reference,
    /// but all must be valid.
    pub unsafe fn iter(&self) -> SpecialListIter {
        SpecialListIter {
            next: self.link.next,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.link.next.is_none()
    }
}
impl Default for SpecialList {
    fn default() -> Self {
        Self::EMPTY
    }
}

pub struct SpecialListIter {
    next: Option<NonNull<Bt>>,
}
impl Iterator for SpecialListIter {
    type Item = NonNull<Bt>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.next;
        if let Some(next) = next {
            self.next = unsafe { next.as_ref().special.next };
        }
        next
    }
}
