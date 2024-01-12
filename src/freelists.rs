use crate::list::SpecialList;

pub const NUM_FREELISTS: usize = usize::BITS as usize;

pub struct Freelists {
    freelists: [SpecialList; NUM_FREELISTS],
}
impl Freelists {
    pub const fn new() -> Self {
        Self {
            freelists: [SpecialList::EMPTY; NUM_FREELISTS],
        }
    }

    pub fn list_for_mut(&mut self, min_size: usize) -> &mut SpecialList {
        let index = min_size.trailing_zeros() as usize;
        &mut self.freelists[index]
    }

    pub fn list_of_mut(&mut self, size: usize) -> &mut SpecialList {
        let index = NUM_FREELISTS - size.leading_zeros() as usize - 1;
        &mut self.freelists[index]
    }
}
impl Default for Freelists {
    fn default() -> Self {
        Self::new()
    }
}
