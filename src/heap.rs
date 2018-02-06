use ::block::{IBlock, Block, BlockIterator};
use ::{Layout, Alloc, AllocErr, ptr::{self, Unique}, vec};

use sync::CriticalSection;

#[cfg(test)]
use ::block::BlockHeader;

#[cfg(test)]
use std::fmt::{self, Debug, Formatter};

pub struct Heap<B: IBlock=Block> {
    /// first free block of the list
    start: Unique<B>,
    /// Number of blocks (regardless of their allocation status).
    count: usize,
/*    /// Total memory size in byte.
    capacity: usize,
    /// Number of allocated blocks.
    allocated_blocks: usize,
    /// Allocated memory in byte.
    len: usize,
*/}

/// This allows to fetch basic usage statistics on memory.
/// They can be used to analyse & optimize allocations
pub struct HeapStatistics {

}

#[cfg(test)]
impl<B: IBlock+Debug> Debug for Heap<B> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.count == 0 {
            write!(f, "Heap {{ start: empty, count: }}")
        } else {
            write!(f, "Heap {{ start: {:?}, count: {} }}",
                   unsafe { self.start.as_ref() } , self.count)
        }
    }
}

impl<B: IBlock> Heap<B> {
    pub const fn new() -> Heap<B> {
        Heap {
            start: unsafe { Unique::new_unchecked(ptr::null_mut()) /* Unique::empty is not const */ },
            count: 0/*,
            capacity: 0,
            len: 0,
            allocated_blocks: 0*/
        }
    }

    pub fn init(&mut self, heap_start: usize, heap_size: usize) -> Result<(), &'static str> {
        let cs = CriticalSection::new();
        if self.count != 0 {
            return Err("This heap is already initialized.")
        }

        // this is fine, we are given a valid heap_start
        let res = unsafe {
            B::init(heap_start as *const u8 as *mut u8, heap_size).and_then(|first_block| {
                    self.start = first_block;
                    self.count = BlockIterator::new(first_block).count();
                    Ok(())
                })
        };

        drop(cs);
        res
    }

    pub fn dump(&self, _out: &mut vec::Vec<(usize, bool)>) {
        unimplemented!()
    }

    pub fn get_statistics() -> HeapStatistics {
        unimplemented!()
    }
}

unsafe impl<B: IBlock+Into<::block::BlockHeader>> Alloc for Heap<B> {
    unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, AllocErr> {
        if layout.align() > Block::alignment() {
            return Err(AllocErr::invalid_input("Cannot align to more than the system's register size."))
        }
        if layout.align().count_ones() != 1 {
            return Err(AllocErr::invalid_input("Alignment must be a power of 2."))
        }

        let size = Block::align(layout.size());

        #[cfg(test)]
        println!("layout={:?} size={}", &layout, size);

        let cs = CriticalSection::new();
        let first_fit = BlockIterator::new(self.start).find(|b| {
            let block = b.as_ref();
            !block.is_allocated() && block.size() >= size
        });

        let result = match first_fit {
            None => Err(AllocErr::Exhausted { request: layout }),
            Some(mut block) => {
                #[cfg(test)]
                {
                    let bh: BlockHeader = block.as_ref().into();
                    println!("found block: @{:x}={:?}", block.as_ptr() as usize, bh);
                }

                let b = block.as_mut();
                b.set_is_allocated(true);

                if b.try_shrink(Block::align(layout.size())).is_some() {
                    self.count += 1;
                }
                Ok(b.as_mut_ptr())
            }
        };
        drop(cs);
        result
    }

    unsafe fn dealloc(&mut self, _ptr: *mut u8, _layout: Layout) {
        unimplemented!()
    }
}

#[cfg(test)]
pub mod tests {
    use ::block::IBlock;
    use ::ptr::Unique;
    use super::Heap;
    use std::sync::atomic::{AtomicU32, Ordering};

    static mut CS: AtomicU32 = AtomicU32::new(0);

    #[no_mangle]
    pub fn critical_section_enter() {
        unsafe { CS.fetch_add(1, Ordering::SeqCst); }
    }
    #[no_mangle]
    pub fn critical_section_exit() {
        let prev = unsafe { CS.fetch_sub(1, Ordering::SeqCst) };
        assert!(prev > 0); 
    }

    #[test]
    fn test_init_forwards_err_msg_on_failure() {
        unsafe { CS.store(0, Ordering::SeqCst); }
        struct MockBlock {}
        impl IBlock for MockBlock {
            unsafe fn init(heap: *mut u8, size: usize) -> Result<Unique<Self>, &'static str> { 
                assert_eq!((heap, size), (0x23 as *mut u8, 23));
                Err("error message")
            }
            // Alignment methods {{{
            /// Align the given usize to the closest bigger alignment point.
            fn align(_: usize) -> usize { unimplemented!() }
            /// Returns the alignment supported by the Selfs.
            fn alignment() -> usize { unimplemented!() }
            // }}}
            // attributes {{{ 
            /// Returns the size of this block in unit of alignment.
            fn size(&self) -> usize { unimplemented!() }
            /// Returns previous block's size in unit of alignment.
            fn prev_size(&self) -> usize { unimplemented!() }
            /// Returns `true` if this block is allocated or not.
            fn is_allocated(&self) -> bool { unimplemented!() }
            /// Sets the allocation status of this block.
            fn set_is_allocated(&mut self, _: bool) { unimplemented!() }
            /// Returns `true` if this block is the last of the block chain.
            fn is_last(&self) -> bool { unimplemented!() }
            // }}}
            // navigation {{{
            /// Returns a Unique<Block> to previous block.
            fn previous(&self) -> Option<Unique<Self>> { unimplemented!() }
            /// Returns a Unique<Block> the next block;
            fn next(&self) -> Option<Unique<Self>> { unimplemented!() }
             // }}}
            // from & to {{{
            // conversion from & to Ptr
            /// Returns a ptr to the first byte of the payload from this block.
            fn as_mut_ptr<T>(&self) -> *mut T { unimplemented!() }
            /// Returns the block header associated to this object.
            /// * Warning : * This object must have been allocated. Any other use may corrupt the whole
            ///               memory.
            unsafe fn from_mut_ptr<T>(_: *mut T) -> Unique<Self> { unimplemented!() }
            // }}}
            // grow & shrink {{{
            unsafe fn grow(&mut self) -> bool { unimplemented!() }
            unsafe fn try_shrink(&mut self, _: usize) -> Option<Unique<Self>> { unimplemented!() }
            // }}} 
        }

        let mut h = Heap::<MockBlock>::new();
        assert_eq!(h.init(0x23, 23), Err("error message"));
        assert_eq!(unsafe { CS.load(Ordering::SeqCst) }, 0);
    }
    #[test]
    fn test_init_initializes_statistics_on_success() {
        unsafe { CS.store(0, Ordering::SeqCst); }
        struct MockBlock {
            id: u32
        }
        impl MockBlock {
            fn new(id: u32) -> MockBlock {
                MockBlock { id: id }
            }
        }

        static mut V: Option<Vec<MockBlock>> = None;
        
        unsafe {
            V = Some((0..5).map(|n| MockBlock::new(n)).collect::<Vec<_>>());
        }

        impl IBlock for MockBlock {
            unsafe fn init(_: *mut u8, _: usize) -> Result<Unique<Self>, &'static str> { 
                let ptr = V.as_mut().unwrap().as_mut_ptr();
                Ok(Unique::new(ptr).unwrap())
            }
            // Alignment methods {{{
            /// Align the given usize to the closest bigger alignment point.
            fn align(_: usize) -> usize { unimplemented!() }
            /// Returns the alignment supported by the Selfs.
            fn alignment() -> usize { unimplemented!() }
            // }}}
            // attributes {{{ 
            /// Returns the size of this block in unit of alignment.
            fn size(&self) -> usize { unimplemented!() }
            /// Returns previous block's size in unit of alignment.
            fn prev_size(&self) -> usize { unimplemented!() }
            /// Returns `true` if this block is allocated or not.
            fn is_allocated(&self) -> bool { unimplemented!() }
            /// Sets the allocation status of this block.
            fn set_is_allocated(&mut self, _: bool) { unimplemented!() }
            /// Returns `true` if this block is the last of the block chain.
            fn is_last(&self) -> bool { unimplemented!() }
             // }}}
            // navigation {{{
            /// Returns a Unique<Block> to previous block.
            fn previous(&self) -> Option<Unique<Self>> { unimplemented!() }
            /// Returns a Unique<Block> the next block;
            fn next(&self) -> Option<Unique<Self>> {
                if self.id != 4 {
                    Some(Unique::new(unsafe {
                        (self as *const MockBlock).offset(1) as *mut _
                    }).unwrap())
                } else {
                    None
                }
            }
             // }}}
            // from & to {{{
            // conversion from & to Ptr
            /// Returns a ptr to the first byte of the payload from this block.
            fn as_mut_ptr<T>(&self) -> *mut T { unimplemented!() }
            /// Returns the block header associated to this object.
            /// * Warning : * This object must have been allocated. Any other use may corrupt the whole
            ///               memory.
            unsafe fn from_mut_ptr<T>(_: *mut T) -> Unique<Self> { unimplemented!() }
            // }}}
            // grow & shrink {{{
            unsafe fn grow(&mut self) -> bool { unimplemented!() }
            unsafe fn try_shrink(&mut self, _: usize) -> Option<Unique<Self>> { unimplemented!() }
            // }}} 
        }

        let mut h = Heap::<MockBlock>::new();
        assert_eq!(h.init(0x23, 23), Ok(()));
        assert_eq!(h.count, 5);
        assert_eq!(unsafe { CS.load(Ordering::SeqCst) }, 0);
    }
    /*
    use super::{Heap, Layout, AllocErr, Alloc};
    use ::block::{Block, MIN_PAYLOAD_SIZE, MAX_PAYLOAD_SIZE};
    use ::block::tests::with_vec;

    /// we return the vector here so it is not dropped when this method returns
    fn new_heap(offset: usize, size: usize) -> Result<(Vec<u8>, Heap, *mut Block), &'static str> {

        debug!("offset={} size={}", offset, size);

        let mut vec: Vec<u8> = Vec::with_capacity(size);
        vec.resize(size, 0);
        let start = vec.as_mut_slice().as_mut_ptr() as usize + offset;

        let mut h = Heap::new();
        let res = h.init(start, size-offset);
        if let Err(err) = res {
            Err(err)
        } else {
            let start = vec.as_mut_slice().as_mut_ptr() as usize + offset;
            let mask = Block::alignment() - 1;
            let aligned_start = ((start + mask) & !mask) as *mut Block;

            debug!("start=0x{:x} aligned_start={:?}", start, aligned_start);

            Ok((vec, h, aligned_start))
        }
    }

    fn heap_size(max_size_block: usize, min_size_block: usize, spare: usize) -> usize {
        (
            (max_size_block * (MAX_PAYLOAD_SIZE + Block::hdr_csize())) +
            (min_size_block * (MIN_PAYLOAD_SIZE + Block::hdr_csize()))
        ) * Block::alignment() + spare
    }

    #[test]
    fn test_init_heap_is_too_small_to_align() {
        let res = new_heap(3, heap_size(0, 0, 5));
        assert_eq!("Cannot align the heap.", res.err().unwrap());
    }

    #[test]
    fn test_init_heap_is_too_small() {
        let res = new_heap(3, Block::alignment() + (Block::hdr_csize()*Block::alignment()) - 1);
        assert_eq!("This heap is too small.", res.err().unwrap());
    }

    #[test]
    fn test_init_heap_cannot_be_initialized_twice() {
        let (vec, mut h, _) = new_heap(3, heap_size(0, 1, Block::alignment()))
            .ok().unwrap();
        assert_eq!(Err("This heap is already initialized."),
                   h.init(1234, 567890));
        drop(vec); /* explicit drop to ensure it is not optimized out */
    }

    #[test]
    fn test_init_heap_with_minimal_size() {
        let res = new_heap(3, heap_size(0, 1, Block::alignment()));
        let (vec, h, first_block) = res.ok().unwrap();

        assert_eq!(1, h.count);
        assert_eq!(first_block, h.start);
        drop(vec); /* explicit drop to ensure it is not optimized out */
    }

    #[test]
    fn test_init_heap_with_a_bit_more_than_max_block_size() {
        let (vec, h, first_block) = new_heap(3, heap_size(1, 0, Block::alignment())).ok().unwrap();
        assert_eq!(1, h.count);
        assert_eq!(first_block, h.start);
        drop(vec); /* explicit drop to ensure it is not optimized out */
    }

    #[test]
    fn test_alloc_cannot_aligned_more_than_machine_alignment() {
        let (vec, mut h, _) = new_heap(3, heap_size(4, 0, Block::alignment())).ok().unwrap();
        unsafe {
            let layout = Layout::from_size_align_unchecked(3, Block::alignment() * 2);
            assert_eq!(Err(AllocErr::invalid_input("Cannot align to more than the system's register size.")),
                       h.alloc(layout));
        }
        assert_eq!(4, h.count);
        drop(vec);
    }

    #[test]
    fn test_alloc_only_supports_power_of_two_alignment() {
        let (vec, mut h, _) = new_heap(3, heap_size(4, 0, Block::alignment())).ok().unwrap();
        unsafe {
            let layout = Layout::from_size_align_unchecked(3, 3);
            assert_eq!(Err(AllocErr::invalid_input("Alignment must be a power of 2.")),
                       h.alloc(layout));
        }
        assert_eq!(4, h.count);
        drop(vec);
    }

    #[test]
    fn test_alloc_fails_if_there_is_no_more_room_for_it() {
        let (vec, mut h, _) = new_heap(3, heap_size(1, 0, Block::alignment())).ok().unwrap();
        let layout = Layout::from_size_align((MAX_PAYLOAD_SIZE+1)*Block::alignment(),
                                             Block::alignment()).unwrap();
        assert_eq!(Err(AllocErr::Exhausted { request: layout.clone() }),
                   unsafe { h.alloc(layout) });
        assert_eq!(1, h.count);
        drop(vec);
    }

    #[test]
    fn test_alloc_find_the_first_fitting_block() {
        let (vec, mut h, _) = new_heap(3, heap_size(1, 0, Block::alignment())).ok().unwrap();
        let start_pattern = vec![(3, false), (5, true), (3, true), (12, false)];
        (&mut h, &start_pattern);
        unimplemented!();
        // a = alloc 5
        // b = alloc 5
        // free a
        // c = alloc 3 (at a's address)
        // d = alloc 10
        // free b
        // e = alloc 7
        drop(vec)
    }

    #[test]
    fn test_alloc_splits_the_block_if_it_is_big_enough() {
        let (vec, mut h, _) = new_heap(3, heap_size(1, 0, Block::alignment())).ok().unwrap();
        let layout = Layout::new::<usize>();

        let res = unsafe { h.alloc(layout) };
        debug!("test\tres={:?}", res);
        let ptr = res.ok().unwrap();
        debug!("test\tptr={:x}", ptr as usize);
        assert_eq!(h.start as usize, (ptr as usize) - Block::hdr_csize()*Block::alignment());
        assert!((unsafe { &mut *h.start }).is_allocated());
        assert_eq!(2, h.count);
        drop(vec);
    }

    #[test]
    fn test_() {
        unimplemented!()
    }
    */
}
