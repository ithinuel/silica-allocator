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

#[cfg(test)]
use std::cmp::min;
#[cfg(test)]
use std::mem::size_of;
#[cfg(test)]
use std::fmt::{Debug, Formatter, self};

use ::ptr::{self, Unique};

#[cfg(not(feature = "huge-blocks"))]
type BlockSize = u16;
#[cfg(feature = "huge-blocks")]
type BlockSize = u32;

/// Defines the minimum block size excluding header in platform's alignment unit.
pub const MIN_PAYLOAD_SIZE: usize = 1;

/// Defines the maximum block size excluding header in platform's alignment unit.
pub const MAX_PAYLOAD_SIZE: usize = (1 << (size_of::<BlockSize>()*8 - 1)) - 1;

const FLAG: BlockSize = 1 << (size_of::<BlockSize>()*8 -1);
const FLAG_ALLOCATED: BlockSize = FLAG;
const FLAG_LAST: BlockSize = FLAG;

pub trait IBlock: Sized {    
    unsafe fn init(heap: *mut u8, size: usize) -> Result<Unique<Self>, &'static str>;
    // Alignment methods {{{
    /// Returns the alignment supported by the Selfs.
    fn alignment() -> usize;

    /// Align the given usize to the closest bigger alignment point.
    fn align(size: usize) -> usize;

    /// Gives the block header's size in unit of alignment.
    fn hdr_csize() -> usize { Self::align(size_of::<Self>()) }
    // }}}
    // attributes {{{
    /// Returns the size of this block in unit of alignment.
    fn size(&self) -> usize;
    /// Returns previous block's size in unit of alignment.
    fn prev_size(&self) -> usize;
    /// Returns `true` if this block is allocated or not.
    fn is_allocated(&self) -> bool;
    /// Sets the allocation status of this block.
    fn set_is_allocated(&mut self, allocated: bool);
    /// Returns `true` if this block is the last of the block chain.
    fn is_last(&self) -> bool;
    // }}}
    // navigation {{{
    /// Returns a Unique<Block> to previous block.
    fn previous(&self) -> Option<Unique<Self>>;
    /// Returns a Unique<Block> the next block;
    fn next(&self) -> Option<Unique<Self>>;
    // }}}
    // from & to {{{
    // conversion from & to Ptr
    /// Returns a ptr to the first byte of the payload from this block.
    fn as_mut_ptr<T>(&self) -> *mut T;
    /// Returns the block header associated to this object.
    /// * Warning : * This object must have been allocated. Any other use may corrupt the whole
    ///               memory.
    unsafe fn from_mut_ptr<T>(ptr: *mut T) -> Unique<Self>;
    // }}}
    // grow & shrink {{{
    unsafe fn grow(&mut self) -> bool;
    unsafe fn try_shrink(&mut self, csize: usize) -> Option<Unique<Self>>;
    // }}}
}

#[derive(PartialEq)]
pub struct Block {
    /// previous block size in alignment unit. MSB is `is_last` flag
    prev_size: BlockSize,
    /// this Block size in alignment unit. MSB is `is_allocated` flag.
    size: BlockSize
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockHeader {
    pub prev_size: usize,
    pub size: usize,
    pub is_allocated: bool,
    pub is_last: bool
}

impl<'a, B: IBlock> From<&'a B> for BlockHeader {
    fn from(block: &'a B) -> BlockHeader {
        BlockHeader {
            prev_size: block.prev_size(),
            size: block.size(),
            is_allocated: block.is_allocated(),
            is_last: block.is_last()
        }
    }
}

#[cfg(test)]
impl Debug for Block {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Block {{ prev_size: {}, size: {}, is_allocated: {}, is_last: {} }}",
               self.prev_size(), self.size(), self.is_allocated(), self.is_last())
    }
}

impl IBlock for Block {
    // init func {{{
    /// Initialize a buffer of raw memory with Block headers.
    /// This may fail if it cannot create at least 1 block of MIN_PAYLOAD_SIZE.
    unsafe fn init(heap: *mut u8, size: usize) -> Result<Unique<Block>, &'static str> {
        let mask = Block::alignment() - 1;
        let aligned_heap = ((heap as usize) + mask) & !mask;
       
        let mut heap_size = {
            let diff = aligned_heap - (heap as usize);
            let size = size.saturating_sub(diff);
            size >> Block::alignment().trailing_zeros()
        };
        if heap_size < (Block::hdr_csize() + MIN_PAYLOAD_SIZE) {
            return Err("The given heap is too small to contain at least a minimal aligned block.")
        }

        let mut prev_size = 0;
        // not sure that Unique is the best here as heap might be null yet a valid memory address.
        let mut b = Unique::new_unchecked(aligned_heap as *mut Block);
        loop {
            let size = min(heap_size - Block::hdr_csize(), MAX_PAYLOAD_SIZE);
            b.as_mut().prev_size = prev_size as BlockSize;
            b.as_mut().size = size as BlockSize;

            prev_size = size;
            heap_size -= Block::hdr_csize() + size;

            #[test]
            debug!("b={:x} prev_size={} size={} | heap_size={}",
                   b.as_ptr() as usize, b.as_ref().prev_size, b.as_ref().size, heap_size);

            if heap_size < (Block::hdr_csize() + MIN_PAYLOAD_SIZE) {
                break;
            }

            b = b.as_ref().next().unwrap();
        }

        b.as_mut().prev_size |= FLAG_LAST;
        Ok(Unique::new_unchecked(aligned_heap as *mut Block))
    } 
    // }}} 
    // Alignment methods {{{
    /// Returns the alignment supported by the Blocks.
    fn alignment() -> usize { size_of::<usize>() }

    /// Align the given usize to the closest bigger alignment point.
    fn align(size: usize) -> usize {
        (size + Block::alignment() - MIN_PAYLOAD_SIZE) >> Block::alignment().trailing_zeros()
    }

    /// Gives the block header's size in unit of alignment.
    fn hdr_csize() -> usize { Block::align(size_of::<Block>()) }
    // }}}
    // attributes {{{
    /// Returns the size of this block in unit of alignment.
    fn size(&self) -> usize {
        (self.size & !FLAG_ALLOCATED) as usize
    }

    /// Returns previous block's size in unit of alignment.
    fn prev_size(&self) -> usize { (self.prev_size & !FLAG_LAST) as usize }

    /// Returns `true` if this block is allocated or not.
    fn is_allocated(&self) -> bool { (self.size & FLAG_ALLOCATED) == FLAG_ALLOCATED }

    /// Sets the allocation status of this block.
    fn set_is_allocated(&mut self, allocated: bool) {
        if allocated {
            self.size |= FLAG_ALLOCATED;
        } else {
            self.size &= !FLAG_ALLOCATED;
        }
    }

    /// Returns `true` if this block is the last of the block chain.
    fn is_last(&self) -> bool { (self.prev_size & FLAG_LAST) == FLAG_LAST }
    // }}}
    // navigation {{{
    /// Returns the block header of the previous block.
    fn previous(&self) -> Option<Unique<Self>> {
        if self.prev_size() == 0 {
            return None
        }

        let ptr = self as *const Self as *mut usize;
        let offset = (self.prev_size() + Self::hdr_csize()) as isize;
        Some(unsafe { Unique::new_unchecked(ptr.offset(-offset) as *mut Self) })
    }

    fn next(&self) -> Option<Unique<Self>> {
        if self.is_last() {
            return None
        }

        let ptr = self as *const Self as *mut usize;
        let offset = (self.size() + Self::hdr_csize()) as isize;
        Some(unsafe { Unique::new_unchecked(ptr.offset(offset) as *mut Self) })
    }
    // }}}
    // from & to {{{
    // conversion from & to Ptr
    /// Returns a ptr to the first byte of the payload from this block.
    fn as_mut_ptr<T>(&self) -> *mut T {
        unsafe {
            (self as *const Self as *const usize).offset(Self::hdr_csize() as isize) as *mut T
        }
    }

    /// Returns the block header associated to this object.
    /// * Warning : * This object must have been allocated. Any other use may corrupt the whole
    ///               memory.
    unsafe fn from_mut_ptr<T>(ptr: *mut T) -> Unique<Self> {
        Unique::new_unchecked((ptr as *const usize).offset(-(Self::hdr_csize() as isize)) as *mut Self)
    }
    // }}}
    // grow & shrink {{{
    unsafe fn grow(&mut self) -> bool {
        // cant grow in place if no next block.
        let b1 = match self.next() {
            Some(b) => b,
            None => return false
        };

        let b1 = b1.as_ref();
        if self.is_allocated() && b1.is_allocated() {
            return false
        }

        let new_size = self.size() + Block::hdr_csize() + b1.size();
        if new_size > MAX_PAYLOAD_SIZE {
            return false
        }

        // set new size & copy allocation flag
        self.size = (new_size as BlockSize) | (self.size & FLAG_ALLOCATED) | (b1.size & FLAG_ALLOCATED);
        self.prev_size = self.prev_size | (b1.prev_size & FLAG_LAST);

        // eventually update next's next block's prev_size field.
        if let Some(mut b2) = self.next() {
            let b2 = b2.as_mut();
            b2.prev_size &= FLAG_LAST;
            b2.prev_size |= new_size as BlockSize;
        }

        // if b1 had data, move them here
        if b1.is_allocated() {
            ptr::copy::<usize>(b1.as_mut_ptr(), self.as_mut_ptr(),
            b1.size() * Block::alignment())
        }
        true
    }

    unsafe fn try_shrink(&mut self, csize: usize) -> Option<Unique<Block>> {
        // if we have no room to create a new block return None
        if (csize < MIN_PAYLOAD_SIZE) || (self.size() < (csize + Block::hdr_csize() + MIN_PAYLOAD_SIZE)) {
            return None 
        }

        // compute the future block's size.
        let b1_size = self.size() - (Block::hdr_csize() + csize);

        // get the current next block.
        let b2 = self.next();

        // set the new size & clear last block flag.
        self.size = (csize as BlockSize) | (self.size & FLAG_ALLOCATED);
        self.prev_size &= !FLAG_LAST;

        // b1 cannot be None.
        let mut b1 = self.next().unwrap();
        b1.as_mut().size = b1_size as BlockSize; // the new block is not allocated
        b1.as_mut().prev_size = csize as BlockSize;

        // update next's prev_size or set b1 as last block
        if let Some(mut b2) = b2 {
            let b2_ref = b2.as_mut();
            b2_ref.prev_size = b1_size as BlockSize | (b2_ref.prev_size & FLAG_LAST) ;
        } else {
            // if next was not Some(_) then self was the last
            b1.as_mut().prev_size |= FLAG_LAST;
        }

        Some(b1)
    }
    // }}}
}

// Block Iterator {{{
pub struct BlockIterator<B: IBlock> {
    current: Option<Unique<B>>
}

impl<B: IBlock> BlockIterator<B> {
    pub fn new(start: Unique<B>) -> BlockIterator<B> {
        BlockIterator { current: Some(start) }
    }
}

impl<B: IBlock> Iterator for BlockIterator<B> {
    type Item = Unique<B>;
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current;
        if let Some(ref current) = current {
            self.current = unsafe { current.as_ref().next() };
        }
        current
    }
}
// }}}

// Tests {{{
#[cfg(test)]
pub mod tests {
    use std::vec::Vec;
    use std::ptr::Unique;
    use std::slice;
    use super::{BlockSize, IBlock, Block, BlockHeader, BlockIterator};
    use super::{MIN_PAYLOAD_SIZE, MAX_PAYLOAD_SIZE, FLAG_LAST, FLAG_ALLOCATED};

    // utility functions {{{
    #[derive(Debug)]
    pub enum MemoryTestPattern {
        Block(usize, bool)
    }

    /// initialize array with given pattern (block sizes' & states)
    pub unsafe fn with_vec(pattern: &Vec<MemoryTestPattern>) -> (Vec<u8>, Unique<Block>) {
        let buf_sz = pattern.iter().map(
            |chunk| {
                match chunk {
                    &MemoryTestPattern::Block(size, _) => (size + Block::hdr_csize())*Block::alignment()
                }
            }).sum();
        
        println!();
        println!("Block::hdc_csize()={}", Block::hdr_csize());
        println!("Block::alignment()={}", Block::alignment());

        println!("{:?}=>{}", pattern, buf_sz);
        let mut vec: Vec<u8> = Vec::with_capacity(buf_sz);
        vec.resize(0, 0u8);

        // TODO: This is only possible because of the unsafe block line +11
        let mut prev_block: Option<Unique<Block>> = None;
        let first_block = {
            let start = ((vec.as_mut_ptr() as usize) + Block::alignment() - 1) & !(Block::alignment() - 1);
            Unique::new_unchecked(start as *mut Block)
        };
        let mut block = first_block;
        for item in pattern {
            match item {
                &MemoryTestPattern::Block(size, allocated) => {
                    println!("ptr={:x}", block.as_ptr() as usize);
                    let bref = block.as_mut();
                    println!("size={} as BlockSize={}", size, size as BlockSize);

                    bref.size = size as BlockSize;
                    bref.prev_size = prev_block.map_or(0, |b| b.as_ref().size & !FLAG_ALLOCATED);
                    if allocated {
                        bref.size |= FLAG_ALLOCATED;
                    }
                    println!("bref={:?}", BlockHeader::from(&*bref));
                    prev_block = Some(block);
                    block = Unique::new_unchecked((block.as_ptr() as *mut usize)
                            .offset((Block::hdr_csize() + size) as isize) as *mut Block);
                }
            }
        }

        if let Some(mut b) = prev_block {
            b.as_mut().prev_size |= FLAG_LAST;
        }

        (vec, first_block)
    }

    // }}}
    // check constants {{{
    #[test]
    #[cfg(not(feature = "huge-blocks"))]
    fn test_flag() {
        assert_eq!(FLAG_ALLOCATED, 0x8000);
        assert_eq!(FLAG_LAST, 0x8000);
    }
    #[test]
    #[cfg(feature = "huge-blocks")]
    fn test_flag() {
        assert_eq!(FLAG_ALLOCATED, 0x80000000);
        assert_eq!(FLAG_LAST, 0x80000000);
    }
    // }}}
    // test BlockHeader conversion {{{
    #[test]
    fn test_blockheader_from_block() {
        let b = Block {
            size: 12 | FLAG_ALLOCATED,
            prev_size: 192 | FLAG_LAST,
        };
        let bh = BlockHeader::from(&b);
        assert_eq!(bh, BlockHeader {
            size: 12,
            prev_size: 192,
            is_allocated: true,
            is_last: true
        });
    }
    // }}}
    // test aligment tools {{{
    #[test]
    fn test_to_csize() {
        let mut size = 0;
        assert_eq!(Block::align(size), (size + Block::alignment() - MIN_PAYLOAD_SIZE) / Block::alignment());

        size = 235;
        assert_eq!(Block::align(size), (size + Block::alignment() - MIN_PAYLOAD_SIZE) / Block::alignment());

        size = MAX_PAYLOAD_SIZE;
        assert_eq!(Block::align(size), (size + Block::alignment() - MIN_PAYLOAD_SIZE) / Block::alignment());
    }
    // }}}
    // test navigation functions {{{
    #[test]
    fn test_next_offset() {
        let pattern = vec![
            MemoryTestPattern::Block(5, false),
            MemoryTestPattern::Block(20, true)
        ];
        let (vec, b0) = unsafe { with_vec(&pattern) };
        unsafe {
            let b0_ref = b0.as_ref();
            let b1 = b0_ref.next();
            assert!(b1.is_some());
            let b1 = b1.unwrap();
            let b1_ref = b1.as_ref();
            assert!(b1_ref.next().is_none());

            assert_eq!(BlockHeader::from(b0_ref),
                BlockHeader {
                    size: 5,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: false
                });
            assert_eq!(BlockHeader::from(b1_ref),
                BlockHeader {
                    size: 20,
                    prev_size: 5,
                    is_allocated: true,
                    is_last: true
                });
            assert_eq!((Block::hdr_csize() + 5) * Block::alignment(),
                       (b1.as_ptr() as usize) - (b0.as_ptr() as usize));
        }
        drop(vec); // forces nll to keep vec
    }
    #[test]
    fn test_previous_offset() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
            MemoryTestPattern::Block(5, false)
        ];
        
        unsafe {
            let (vec, b0) = with_vec(&pattern);
            let b1 = b0.as_ref().next();

            assert!(b0.as_ref().previous().is_none());
            assert!(b1.is_some());

            let b0_bis = b1.unwrap().as_ref().previous();
            assert!(b0_bis.is_some());
            assert_eq!(b0_bis.unwrap().as_ptr(), b0.as_ptr());
            drop(vec); // forces nll to keep vec
        }
    }
    #[test]
    fn test_block_iterator() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
            MemoryTestPattern::Block(5, true),
            MemoryTestPattern::Block(22, true),
            MemoryTestPattern::Block(12, false),
            MemoryTestPattern::Block(46, true),
            MemoryTestPattern::Block(2, false),
        ];
        unsafe {
            let (vec, b0) = with_vec(&pattern);
            let res: Vec<BlockHeader> = BlockIterator::new(b0).map(|b| BlockHeader::from(b.as_ref())).collect();
            assert_eq!(res, vec![
                BlockHeader {size: 2, prev_size: 0, is_allocated: false, is_last: false},
                BlockHeader {size: 5, prev_size: 2, is_allocated: true, is_last: false},
                BlockHeader {size: 22, prev_size: 5, is_allocated: true, is_last: false},
                BlockHeader {size: 12, prev_size: 22, is_allocated: false, is_last: false},
                BlockHeader {size: 46, prev_size: 12, is_allocated: true, is_last: false},
                BlockHeader {size: 2, prev_size: 46, is_allocated: false, is_last: true},
            ]);
            drop(vec);
        }
    }
    // }}}
    // test ptr conversions {{{
    #[test]
    fn test_to_ptr() {
        let pattern = vec![MemoryTestPattern::Block(2, false)];
        unsafe {
            let (vec, b0) = with_vec(&pattern);
            let expect = vec.as_slice().as_ptr().offset((Block::hdr_csize() * Block::alignment()) as isize);
            assert_eq!(b0.as_ref().as_mut_ptr() as *const _, expect);
            drop(vec);
        }
    }
    #[test]
    fn test_from_ptr() {
        let pattern = vec![MemoryTestPattern::Block(2, false)];
        unsafe {
            let (vec, expect) = with_vec(&pattern);
            let b0data: *mut u8 = expect.as_ref().as_mut_ptr();
            let b0 = Block::from_mut_ptr(b0data);

            assert_eq!(b0.as_ref(), expect.as_ref());
            
            drop(vec);
        }
    }
    // }}}
    // test block growth {{{
    #[test]
    fn test_grow_transfers_last_flag() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
            MemoryTestPattern::Block(5, false)
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            assert!(b0_ref.grow());
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 7 + Block::hdr_csize(),
                    prev_size: 0,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_grow_keeps_previous_unchanged() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
            MemoryTestPattern::Block(5, false),
            MemoryTestPattern::Block(12, true),
        ];
        unsafe {
            let (vec, b0) = with_vec(&pattern);
            let mut b1 = b0.as_ref().next().unwrap();
            let b1_ref = b1.as_mut();
            assert!(b1_ref.grow());
            assert_eq!(BlockHeader::from(b0.as_ref()),
                BlockHeader {
                    size: 2,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: false
                });
            assert_eq!(BlockHeader::from(&*b1_ref),
                BlockHeader {
                    size: 17 + Block::hdr_csize(),
                    prev_size: 2,
                    is_allocated: true,
                    is_last: true 
                });
            drop(vec);
        }
    }
    #[test]
    fn test_grow_updates_next_next() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
            MemoryTestPattern::Block(5, false),
            MemoryTestPattern::Block(12, true),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            assert!(b0.as_mut().grow());

            let b1 = b0.as_mut().next().unwrap();
            let b1_ref = b1.as_ref();
            assert_eq!(BlockHeader::from(b0.as_ref()),
                BlockHeader {
                    size: 7 + Block::hdr_csize(),
                    prev_size: 0,
                    is_allocated: false,
                    is_last: false
                });
            assert_eq!(BlockHeader::from(b1_ref),
                BlockHeader {
                    size: 12,
                    prev_size: 7 + Block::hdr_csize(),
                    is_allocated: true,
                    is_last: true 
                });
            drop(vec);
        }
    }
    #[test]
    #[cfg_attr(feature = "huge-blocks", ignore)]
    fn test_grow_fails_if_result_would_be_too_big() {
        let pattern = vec![
            MemoryTestPattern::Block(MAX_PAYLOAD_SIZE, false),
            MemoryTestPattern::Block(1, false)
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            assert!(!b0.as_mut().grow());
            assert_eq!(BlockHeader::from(b0.as_ref()),
                BlockHeader {
                    size: MAX_PAYLOAD_SIZE,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: false
                });
            let b1 = b0.as_ref().next();
            assert!(b1.is_some());
            let b1 = b1.unwrap();
            let b1_ref = b1.as_ref();
            assert_eq!(BlockHeader::from(b1_ref),
                BlockHeader {
                    size: 1,
                    prev_size: MAX_PAYLOAD_SIZE,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_grow_keeps_source_data_on_allocated_block() {
        let pattern = vec![
            MemoryTestPattern::Block(2, true),
            MemoryTestPattern::Block(5, false)
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            let expect = {
                let data = b0_ref.as_mut_ptr() as *mut u8;
                let s = slice::from_raw_parts_mut(data, (2 - Block::hdr_csize())*Block::alignment());
                println!("s.len() == {:?}", s);
                for i in 0..s.len() {
                    s[i] = i as u8;
                }
                s.to_vec()
            };

            assert!(b0_ref.grow());
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 7 + Block::hdr_csize(),
                    prev_size: 0,
                    is_allocated: true,
                    is_last: true
                });
            let s = slice::from_raw_parts(b0_ref.as_mut_ptr() as *mut u8, expect.len());
            assert_eq!(s, expect.as_slice());
            drop(vec);
        }
    }
    #[test]
    fn test_grow_moves_data_from_next_block_if_allocated() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
            MemoryTestPattern::Block(5, true)
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            let expect = {
                let mut b1 = b0_ref.next().unwrap();
                let b1_ref = b1.as_mut();
                let data = b1_ref.as_mut_ptr() as *mut u8;
                let s = slice::from_raw_parts_mut(data, (5 - Block::hdr_csize())*Block::alignment());
                println!("s.len() == {:?}", s);
                for i in 0..s.len() {
                    s[i] = i as u8;
                }
                s.to_vec()
            };

            assert!(b0_ref.grow());
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 7 + Block::hdr_csize(),
                    prev_size: 0,
                    is_allocated: true,
                    is_last: true
                });
            let s = slice::from_raw_parts(b0_ref.as_mut_ptr() as *mut u8, expect.len());
            assert_eq!(s, expect.as_slice());
            drop(vec);
        }
    }
    #[test]
    fn test_grow_fails_on_last_block() {
        let pattern = vec![
            MemoryTestPattern::Block(2, false),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            assert!(!b0_ref.grow());
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 2,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    // }}}
    // test block shrink {{{
    #[test]
    fn test_shrink_fails_if_requested_size_is_less_than_minimal() {
        let pattern = vec![
            MemoryTestPattern::Block(10, false),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            assert!(b0_ref.try_shrink(MIN_PAYLOAD_SIZE - 1).is_none());
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 10,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_shrink_transfers_last_flag() {
        let pattern = vec![
            MemoryTestPattern::Block(10 + Block::hdr_csize(), false),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            let res = b0_ref.try_shrink(5);
            assert!(res.is_some());
            let b1 = res.unwrap();
           
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 5,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: false
                });
            assert_eq!(BlockHeader::from(b1.as_ref()),
                BlockHeader {
                    size: 5,
                    prev_size: 5,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_shrink_creates_a_free_block() {
        let pattern = vec![
            MemoryTestPattern::Block(10 + Block::hdr_csize(), true),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            let res = b0_ref.try_shrink(5);
            assert!(res.is_some());
            let b1 = res.unwrap();
            
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 5,
                    prev_size: 0,
                    is_allocated: true,
                    is_last: false
                });
            assert_eq!(BlockHeader::from(b1.as_ref()),
                BlockHeader {
                    size: 5,
                    prev_size: 5,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_shrink_fails_if_it_would_create_a_block_smaller_than_minimal_size() {
        let pattern = vec![
            MemoryTestPattern::Block(10, false),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b0_ref = b0.as_mut();
            assert!(b0_ref.try_shrink(10 - (MIN_PAYLOAD_SIZE + Block::hdr_csize()) / 2).is_none());
            assert_eq!(BlockHeader::from(&*b0_ref),
                BlockHeader {
                    size: 10,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_shrink_preserves_previous_size() {
        let pattern = vec![
            MemoryTestPattern::Block(3, false),
            MemoryTestPattern::Block(10+Block::hdr_csize(), false),
        ];
        unsafe {
            let (vec, b0) = with_vec(&pattern);
            let mut b1 = b0.as_ref().next().unwrap();
            let b1_ref = b1.as_mut();
            let b2 = b1_ref.try_shrink(5);
            assert!(b2.is_some());
            assert_eq!(BlockHeader::from(b0.as_ref()),
                BlockHeader {
                    size: 3,
                    prev_size: 0,
                    is_allocated: false,
                    is_last: false
                });
            assert_eq!(BlockHeader::from(&*b1_ref),
                BlockHeader {
                    size: 5,
                    prev_size: 3,
                    is_allocated: false,
                    is_last: false
                });
            let b2 = b2.unwrap();
            assert_eq!(BlockHeader::from(b2.as_ref()),
                BlockHeader {
                    size: 5,
                    prev_size: 5,
                    is_allocated: false,
                    is_last: true
                });
            drop(vec);
        }
    }
    #[test]
    fn test_shrink_updates_next_next_next() {
        let pattern = vec![
            MemoryTestPattern::Block(10+Block::hdr_csize(), true),
            MemoryTestPattern::Block(3, true),
        ];
        unsafe {
            let (vec, mut b0) = with_vec(&pattern);
            let b1 = b0.as_mut().try_shrink(5);
            assert!(b1.is_some());
            let result: Vec<BlockHeader> = BlockIterator::new(b0).map(|b| BlockHeader::from(b.as_ref())).collect();
            assert_eq!(result, vec![
            BlockHeader {
                size: 5,
                prev_size: 0,
                is_allocated: true,
                is_last: false
            },
            BlockHeader {
                size: 5,
                prev_size: 5,
                is_allocated: false,
                is_last: false
            },
            BlockHeader {
                size: 3,
                prev_size: 5,
                is_allocated: true,
                is_last: true
            }]);
            drop(vec);
        }
    }
    // }}}
    // test init function {{{
    #[cfg_attr(not(feature = "huge-blocks"), test)]
    fn test_init() {
        let mut vec = vec![0; (12*(MAX_PAYLOAD_SIZE+Block::hdr_csize())+Block::hdr_csize()+8)*Block::alignment()];
        let ptr = vec.as_mut_slice().as_mut_ptr();
        let mut expect = vec![BlockHeader { size: MAX_PAYLOAD_SIZE, prev_size: MAX_PAYLOAD_SIZE, is_allocated: false, is_last: false}; 12];
        expect[0].prev_size = 0;
        expect.push(BlockHeader {
            size: 8,
            prev_size: MAX_PAYLOAD_SIZE,
            is_allocated: false,
            is_last: true
        });
        
        unsafe {
            let res = Block::init(ptr, vec.len());
            assert!(res.is_ok());
            let first_block = res.unwrap();
            let result: Vec<BlockHeader> = BlockIterator::new(first_block).map(|b| BlockHeader::from(b.as_ref())).collect();
            assert_eq!(result, expect);
        }
    }
    #[test]
    fn test_init_fails_if_memory_is_too_small() {
        let mut vec = vec![0; (Block::hdr_csize()+MIN_PAYLOAD_SIZE)*Block::alignment() - 1];
        let ptr = vec.as_mut_slice().as_mut_ptr();
        unsafe {
            let res = Block::init(ptr, vec.len());
            assert!(res.is_err());
            assert_eq!(res.err().unwrap(),
                       "The given heap is too small to contain at least a minimal aligned block.");
            assert_eq!(vec, vec![0; vec.len()]);
        }
    }
    #[test]
    fn test_init_fails_if_it_cannot_align_the_first_block() {
        let mut vec = vec![0; (1+Block::hdr_csize()+MIN_PAYLOAD_SIZE)*Block::alignment()];
        let ptr = vec.as_mut_slice().as_mut_ptr();
        unsafe {
            let test_ptr = (ptr as usize) + Block::alignment()/2;
            let res = Block::init(test_ptr as *mut u8, vec.len() - Block::alignment());
            assert!(res.is_err());
            assert_eq!(res.err().unwrap(),
                       "The given heap is too small to contain at least a minimal aligned block.");
            assert_eq!(vec, vec![0; vec.len()]);
        }
    }
    // }}}
}

