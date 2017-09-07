/// This module provides a simple yet memory efficient allocator for micro-controllers.
///
/// The smallest payload's size allocatable is equivalent to the alignment size.
/// The smallest block's size is equivalent to the smallest payload plus the header.
/// This allocator uses a double linked list stored in the header of each block using two
/// 15bit fields to store the previous block's size and the current block's size.
/// The block's size do not include the header size.
/// Two additional 1 bit wide fields are used to respectively store the allocation state for the
/// block and mark the last block in the list.
/// Thus the maximum allocatable block is (2^15-1)*(alignment_size).
///
/// A size of 0 means 'no previous block'.

#[cfg(not(test))]
use core::cmp::min;
#[cfg(not(test))]
use core::mem::size_of;
#[cfg(not(test))]
use core::ptr;


#[cfg(test)]
use std::cmp::min;
#[cfg(test)]
use std::mem::size_of;
#[cfg(test)]
use std::ptr;

/// Defines the minimum block size excluding header in platform's alignment unit.
pub const MIN_PAYLOAD_SIZE: usize = 1;

/// Defines the maximum block size excluding header in platform's alignment unit.
pub const MAX_PAYLOAD_SIZE: usize = 0x7FFF;

const FLAG_ALLOCATED: u16 = 0x8000;
const FLAG_LAST: u16 = 0x8000;

#[derive(Debug, PartialEq)]
pub enum BlockError {
    NotEnoughMemory,
}

#[derive(Debug,PartialEq)]
pub struct Block {
    /// previous block size in alignment unit. MSB is `is_last` flag.
    prev_size: u16,
    /// this Block size in alignment unit. MSB is `is_allocated` flag.
    size: u16
}

impl Block {
    /// Initialize a buffer of raw memory with Block headers.
    /// Returns the number of block initialized or a `BlockError`.
    pub fn init<'a>(heap: *mut u8, size: usize) -> Result<(usize, &'a mut Block), BlockError> {
        let mut heap_size = size >> Block::alignment().trailing_zeros();

        if heap_size < (Block::hdr_csize() + MIN_PAYLOAD_SIZE) {
            return Err(BlockError::NotEnoughMemory)
        }

        let mut counter = 0;
        let mut prev_size = 0;
        let mut b = unsafe { &mut *(heap as *mut Block) };
        loop {
            let size = min(heap_size - Block::hdr_csize(), MAX_PAYLOAD_SIZE);
            b.prev_size = prev_size as u16;
            b.size = size as u16;

            counter += 1;

            prev_size = size;
            heap_size -= Block::hdr_csize() + size;
            if heap_size < (Block::hdr_csize() + MIN_PAYLOAD_SIZE) {
                break;
            }

            b = b.next().unwrap();
        }
        b.prev_size |= FLAG_LAST;
        Ok((counter, unsafe { &mut *(heap as *mut Block) }))
    }

    /// Returns the alignment supported by the Blocks.
    #[inline]
    pub fn alignment() -> usize { size_of::<usize>() }

    /// Align the given usize to the closest bigger alignment point.
    #[inline]
    pub fn align(size: usize) -> usize {
        (size + Block::alignment() - MIN_PAYLOAD_SIZE) >> Block::alignment().trailing_zeros()
    }

    #[inline]
    pub fn hdr_csize() -> usize { Block::align(size_of::<Block>()) }

    #[inline]
    pub fn size(&self) -> usize {
        (self.size & !FLAG_ALLOCATED) as usize
    }

    #[inline]
    pub fn prev_size(&self) -> usize { (self.prev_size & !FLAG_LAST) as usize }

    #[inline]
    pub fn is_allocated(&self) -> bool { (self.size & FLAG_ALLOCATED) == FLAG_ALLOCATED }
    #[inline]
    pub fn set_is_allocated(&mut self, allocated: bool) {
        if allocated {
            self.size |= FLAG_ALLOCATED;
        } else {
            self.size &= !FLAG_ALLOCATED;
        }
    }

    #[inline]
    pub fn is_last(&self) -> bool { (self.prev_size & FLAG_LAST) == FLAG_LAST }

    /// Returns a ptr to the first byte of the payload from this block.
    pub fn as_mut_ptr<T>(&self) -> *mut T {
        unsafe {
            (self as *const Block as *const usize).offset(Block::hdr_csize() as isize) as *mut T
        }
    }

    /// Returns the block header associated to this object.
    /// * Warning : * This object must have been allocated. Any other use may corrupt the whole
    ///               memory.
    pub fn from_ptr<'a, T>(ptr: *const T) -> &'a mut Block {
        unsafe {
            &mut *((ptr as *const usize).offset(-(Block::hdr_csize() as isize)) as *mut Block)
        }
    }

    /// Returns the block header of the previous block.
    pub fn previous<'a, 'b>(&'a self) -> Option<&'b mut Block> {
        if self.prev_size() == 0 {
            return None
        }

        let ptr = self as *const Block as *mut usize;
        let offset = (self.prev_size() + Block::hdr_csize()) as isize;
        Some(unsafe { &mut *(ptr.offset(-offset) as *mut Block) })
    }

    pub fn next<'a, 'b>(&'a self) -> Option<&'b mut Block> {
        if self.is_last() {
            return None
        }

        let ptr = self as *const Block as *mut usize;
        let offset = (self.size() + Block::hdr_csize()) as isize;
        Some(unsafe { &mut *(ptr.offset(offset) as *mut Block) })
    }

    pub fn grow(&mut self) -> bool {
        // cant grow in place if no next block.
        let b1 = match self.next() {
            Some(b) => b,
            None => return false
        };

        if self.is_allocated() && b1.is_allocated() {
            return false
        }

        let new_size = self.size() + Block::hdr_csize() + b1.size();
        if new_size > MAX_PAYLOAD_SIZE {
            return false
        }

        // set new size & copy allocation flag
        self.size = (new_size as u16) | (self.size & FLAG_ALLOCATED) | (b1.size & FLAG_ALLOCATED);
        self.prev_size = self.prev_size | (b1.prev_size & FLAG_LAST);

        // eventually update next's next block's prev_size field.
        if let Some(b2) = self.next() {
            b2.prev_size = (new_size as u16) | (b2.prev_size & FLAG_LAST);
        }

        // if b1 had data, move them here
        if b1.is_allocated() {
            unsafe {
                ptr::copy::<usize>(b1.as_mut_ptr(), self.as_mut_ptr(),
                                   b1.size() * Block::alignment())
            }
        }
        true
    }

    pub fn shrink<'b>(&mut self, csize: usize) -> Option<&'b mut Block> {
        // if we have no room to create a new block return None
        if (csize < MIN_PAYLOAD_SIZE) || (self.size() < (csize + Block::hdr_csize() + MIN_PAYLOAD_SIZE)) {
            return None
        }

        // compute the future block's size.
        let b1_size = self.size() - (Block::hdr_csize() + csize);

        // get the current next block.
        let b2 = self.next();

        // set the new size & clean last block flag.
        self.size = (csize as u16) | (self.size & FLAG_ALLOCATED);
        self.prev_size &= !FLAG_LAST;

        // b1 cannot be None.
        let b1 = self.next().unwrap();
        b1.size = b1_size as u16; // the new block is not allocated
        b1.prev_size = csize as u16;

        if let Some(b2) = b2 {
            b2.prev_size = b1_size as u16;
        } else {
            // if next was not Some(_) then self was the last
            b1.prev_size |= FLAG_LAST;
        }

        Some(b1)
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;
    use super::{Block, BlockError, MIN_PAYLOAD_SIZE, MAX_PAYLOAD_SIZE, FLAG_LAST, FLAG_ALLOCATED};

    /// defines a work load of a bit more than 10MiB
    const WORK_LOAD: usize = 10*1024*1024+23125;

    fn setup(cap: usize) -> Vec<u8> {
        let mut v = Vec::with_capacity(cap);
        v.resize(cap, 0);
        v
    }

    fn first_block<'a, 'b>(v: &'a mut [u8]) -> &'b mut Block {
        unsafe { &mut *(v.as_mut_ptr() as *mut Block) }
    }

    fn check_init(v: &mut Vec<u8>, load_size: usize, expect_err: Option<BlockError>) {
        v.resize(load_size, 0);
        let alignment_items = load_size / Block::alignment();
        let max_block_size = Block::hdr_csize() + MAX_PAYLOAD_SIZE;
        let mut count = alignment_items / max_block_size;

        if (alignment_items - (count * max_block_size)) > (Block::hdr_csize() + MIN_PAYLOAD_SIZE) {
            count += 1;
        }
        let result = Block::init((v).as_mut_slice().as_mut_ptr(), load_size);

        if let Some(err) = expect_err {
            assert_eq!(Err(err), result);
        } else {
            assert_eq!(Ok((count, first_block(v))), result);
        }
    }

    #[test]
    fn test_init() {
        let mut v: Vec<u8> = Vec::with_capacity(Block::hdr_csize()* Block::alignment() - 1);
        check_init(&mut v, 0, Some(BlockError::NotEnoughMemory));
        check_init(&mut v, Block::hdr_csize() + MAX_PAYLOAD_SIZE /2, None);
        check_init(&mut v, WORK_LOAD / 2, None);
        check_init(&mut v, WORK_LOAD, None);
    }

    #[test]
    fn test_to_csize() {
        let mut size = 0;
        assert_eq!(Block::align(size), (size + Block::alignment() - MIN_PAYLOAD_SIZE) / Block::alignment());

        size = 235;
        assert_eq!(Block::align(size), (size + Block::alignment() - MIN_PAYLOAD_SIZE) / Block::alignment());

        size = MAX_PAYLOAD_SIZE;
        assert_eq!(Block::align(size), (size + Block::alignment() - MIN_PAYLOAD_SIZE) / Block::alignment());
    }

    #[test]
    fn test_next_offset() {
        let mut vec = setup(WORK_LOAD);
        let b0 = first_block(vec.as_mut_slice());
        let b0_size = 5;
        b0.size = b0_size;
        let b1 = b0.next();
        assert!(b1.is_some());

        let b1 = b1.unwrap();
        assert_eq!((Block::hdr_csize() + (b0_size as usize)) * Block::alignment(),
                   (b1 as *mut Block as usize) - (b0 as *mut Block as usize));

        let b0_size = 25;
        b0.size = b0_size;
        let b1 = b0.next();
        assert!(b1.is_some());

        let b1 = b1.unwrap();
        assert_eq!((Block::hdr_csize() + (b0_size as usize)) * Block::alignment(),
                   (b1 as *mut Block as usize) - (b0 as *mut Block as usize));
    }

    #[test]
    fn test_previous_offset() {
        let mut vec = setup(WORK_LOAD);
        let b0_size = 25;
        let b0 = first_block(vec.as_mut_slice());
        b0.size = b0_size;
        let b1 = b0.next();
        assert!(b1.is_some());
        let b1 = b1.unwrap();
        b1.prev_size = b0_size;

        let b0_bis = b1.previous();
        assert!(b0_bis.is_some());
        let b0_bis = b0_bis.unwrap();
        assert_eq!((Block::hdr_csize() + (b0_size as usize)) * Block::alignment(),
                   (b1 as *mut Block as usize) - (b0_bis as *mut Block as usize));
    }

    fn dont_grow_if_the_result_is_too_big(heap_size: usize, b0_size: usize, b1_size: usize) {
        let mut vec = setup(heap_size * Block::alignment());
        let b0 = first_block(vec.as_mut_slice());
        b0.size = b0_size as u16;
        let b1 = b0.next().unwrap();
        b1.size = b1_size as u16;
        b1.prev_size = b0_size as u16 | FLAG_LAST;

        // check prerequisite
        assert_eq!(b0_size, b0.size());
        assert_eq!(false, b0.is_allocated());
        assert_eq!(false, b0.is_last());
        assert_eq!(b1_size, b1.size());
        assert_eq!(false, b1.is_allocated());
        assert_eq!(true, b1.is_last());

        // check result
        assert_eq!(false, b0.grow());
        assert_eq!(b0_size, b0.size());
        assert_eq!(false, b0.is_allocated());
        assert_eq!(false, b0.is_last());
        assert_eq!(b1_size, b1.size());
        assert_eq!(false, b1.is_allocated());
        assert_eq!(true, b1.is_last());
    }

    #[test]
    fn test_dont_grow_if_the_result_is_too_big() {
        dont_grow_if_the_result_is_too_big(
            Block::hdr_csize() * 2 + MIN_PAYLOAD_SIZE + MAX_PAYLOAD_SIZE,
            MAX_PAYLOAD_SIZE,
            MIN_PAYLOAD_SIZE
        );
        dont_grow_if_the_result_is_too_big(
            Block::hdr_csize() * 2 + MIN_PAYLOAD_SIZE + MAX_PAYLOAD_SIZE,
            MIN_PAYLOAD_SIZE,
            MAX_PAYLOAD_SIZE
        );
        dont_grow_if_the_result_is_too_big(
            Block::hdr_csize() * 2 + MAX_PAYLOAD_SIZE + 1,
            MAX_PAYLOAD_SIZE / 2,
            MAX_PAYLOAD_SIZE / 2 + 1
        );
    }

    #[test]
    fn test_dont_grow_if_both_are_allocated() {
        let mut vec = setup((Block::hdr_csize() * 2 +
            MIN_PAYLOAD_SIZE +
            MIN_PAYLOAD_SIZE) * Block::alignment());
        let b0 = first_block(vec.as_mut_slice());
        b0.size = (MIN_PAYLOAD_SIZE as u16) | FLAG_ALLOCATED;
        let b1 = b0.next().unwrap();
        b1.size = (MIN_PAYLOAD_SIZE as u16) | FLAG_ALLOCATED;
        b1.prev_size = (MIN_PAYLOAD_SIZE as u16) | FLAG_LAST;

        assert_eq!(false, b0.grow());
    }

    #[test]
    fn test_grow_propagates_last_block_flag() {
        let mut vec = setup((Block::hdr_csize() * 2 +
            MIN_PAYLOAD_SIZE +
            MIN_PAYLOAD_SIZE) * Block::alignment());
        let b0 = first_block(vec.as_mut_slice());
        b0.size = MIN_PAYLOAD_SIZE as u16;
        let b1 = b0.next().unwrap();
        b1.size = MIN_PAYLOAD_SIZE as u16;
        b1.prev_size = (MIN_PAYLOAD_SIZE as u16) | FLAG_LAST;

        assert_eq!(true, b0.grow());
        assert_eq!(2* MIN_PAYLOAD_SIZE + Block::hdr_csize(), b0.size());
        assert_eq!(true, b0.is_last());
        assert_eq!(false, b0.is_allocated());
    }

    #[test]
    fn test_grow_propagates_allocated_block_flag() {
        { // propagates from first block
            let mut vec = setup((Block::hdr_csize() + MIN_PAYLOAD_SIZE) * 2 * Block::alignment());
            let b0 = first_block(vec.as_mut_slice());
            b0.size = (MIN_PAYLOAD_SIZE as u16) | FLAG_ALLOCATED;
            let b1 = b0.next().unwrap();
            b1.size = MIN_PAYLOAD_SIZE as u16;
            b1.prev_size = MIN_PAYLOAD_SIZE as u16;

            assert_eq!(true, b0.grow());
            assert_eq!(2 * MIN_PAYLOAD_SIZE + Block::hdr_csize(), b0.size());
            assert_eq!(false, b0.is_last());
            assert_eq!(true, b0.is_allocated());
        }
        { // propagates from second block
            let mut vec = setup((Block::hdr_csize() + MIN_PAYLOAD_SIZE) * 2 * Block::alignment());
            let b0 = first_block(vec.as_mut_slice());
            b0.size = MIN_PAYLOAD_SIZE as u16;
            let b1 = b0.next().unwrap();
            b1.size = (MIN_PAYLOAD_SIZE as u16) | FLAG_ALLOCATED;
            b1.prev_size = MIN_PAYLOAD_SIZE as u16;

            assert_eq!(true, b0.grow());
            assert_eq!(2 * MIN_PAYLOAD_SIZE + Block::hdr_csize(), b0.size());
            assert_eq!(false, b0.is_last());
            assert_eq!(true, b0.is_allocated());
        }
    }

    #[test]
    fn test_dont_shrink_if_the_result_is_too_small() {
        let mut vec = setup((Block::hdr_csize() + MIN_PAYLOAD_SIZE) * 2 * Block::alignment());
        let b0 = first_block(vec.as_mut_slice());
        b0.size = (Block::hdr_csize() + MIN_PAYLOAD_SIZE * 2) as u16;
        b0.prev_size = 0 | FLAG_LAST;

        assert_eq!(None, b0.shrink(0));
        assert_eq!(Block::hdr_csize() + MIN_PAYLOAD_SIZE * 2, b0.size());
        assert_eq!(true, b0.is_last());
        assert_eq!(false, b0.is_allocated());
    }

    #[test]
    fn test_dont_shrink_if_source_is_too_small() {
        { // source is already at MIN_PAYLOAD_LEN
            let mut vec = setup((Block::hdr_csize() + MIN_PAYLOAD_SIZE) * Block::alignment());
            let b0 = first_block(vec.as_mut_slice());
            b0.size = MIN_PAYLOAD_SIZE as u16;
            b0.prev_size = 0 | FLAG_LAST;

            assert_eq!(None, b0.shrink(MIN_PAYLOAD_SIZE));
            assert_eq!(MIN_PAYLOAD_SIZE, b0.size());
            assert_eq!(true, b0.is_last());
            assert_eq!(false, b0.is_allocated());
        }
        { // source can not be splitted to another block
            let mut vec = setup((Block::hdr_csize() + MIN_PAYLOAD_SIZE * 2) * Block::alignment());
            let b0 = first_block(vec.as_mut_slice());
            b0.size = (MIN_PAYLOAD_SIZE as u16) * 2;
            b0.prev_size = 0 | FLAG_LAST;

            assert_eq!(None, b0.shrink(MIN_PAYLOAD_SIZE));
            assert_eq!(MIN_PAYLOAD_SIZE * 2, b0.size());
            assert_eq!(true, b0.is_last());
            assert_eq!(false, b0.is_allocated());
        }
    }

    #[test]
    fn test_shrink_moves_last_flag() {
        let mut vec = setup((Block::hdr_csize() + MAX_PAYLOAD_SIZE) * Block::alignment());
        let b0 = first_block(vec.as_mut_slice());
        b0.size = MAX_PAYLOAD_SIZE as u16;
        b0.prev_size = 0 | FLAG_LAST;

        let opt_b1 = b0.shrink(MIN_PAYLOAD_SIZE);
        assert_eq!(true, opt_b1.is_some());
        let b1 = opt_b1.unwrap();

        assert_eq!(MIN_PAYLOAD_SIZE, b0.size());
        assert_eq!(false, b0.is_last());
        assert_eq!(false, b0.is_allocated());

        assert_eq!(MAX_PAYLOAD_SIZE - (MIN_PAYLOAD_SIZE + Block::hdr_csize()), b1.size());
        assert_eq!(true, b1.is_last());
        assert_eq!(false, b1.is_allocated());
    }
    #[test]
    fn test_shrink_keeps_allocated_flag() {
        let mut vec = setup((Block::hdr_csize() + MAX_PAYLOAD_SIZE) * Block::alignment());
        let b0 = first_block(vec.as_mut_slice());
        b0.size = (MAX_PAYLOAD_SIZE as u16) | FLAG_ALLOCATED;
        b0.prev_size = 0;

        let opt_b1 = b0.shrink(MIN_PAYLOAD_SIZE);
        assert_eq!(true, opt_b1.is_some());
        let b1 = opt_b1.unwrap();

        assert_eq!(MIN_PAYLOAD_SIZE, b0.size());
        assert_eq!(false, b0.is_last());
        assert_eq!(true, b0.is_allocated());

        assert_eq!(MAX_PAYLOAD_SIZE - (MIN_PAYLOAD_SIZE + Block::hdr_csize()), b1.size());
        assert_eq!(false, b1.is_last());
        assert_eq!(false, b1.is_allocated());
    }
}