use core::{hash::Hasher, ptr::NonNull};

use rustc_hash::FxHasher;

use crate::{bt::Bt, list::SpecialList};

pub const NUM_BUCKETS: usize = 64;

pub struct AllocationTable {
    buckets: [SpecialList; NUM_BUCKETS],
}
impl AllocationTable {
    pub const fn new() -> Self {
        Self {
            buckets: [SpecialList::EMPTY; NUM_BUCKETS],
        }
    }

    /// # Safety
    /// No bt in any of the contained lists may be currently in use,
    /// but all must be valid. The supplied bt must also be valid.
    pub unsafe fn insert(&mut self, bt: NonNull<Bt>) {
        let base = bt.as_ref().base;
        let mut hasher = FxHasher::default();
        hasher.write_usize(base);
        let hash = hasher.finish() as usize;
        self.buckets[hash % NUM_BUCKETS].insert(bt);
    }

    /// # Safety
    /// No bt in any of the contained lists may be currently in use,
    /// but all must be valid.
    pub unsafe fn remove(&mut self, base: usize) -> Option<NonNull<Bt>> {
        let mut hasher = FxHasher::default();
        hasher.write_usize(base);
        let hash = hasher.finish() as usize;
        let bucket = &mut self.buckets[hash % NUM_BUCKETS];
        for bt in bucket.iter() {
            if bt.as_ref().base == base {
                bucket.remove(bt);
                return Some(bt);
            }
        }
        None
    }
}
