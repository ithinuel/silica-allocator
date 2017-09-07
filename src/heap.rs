use ::block::{Block, BlockError};
use ::{Layout, Alloc, AllocErr};


#[derive(Debug)]
pub struct Heap {
    first_block: Option<*mut Block>,
    block_count: usize
}

impl Heap {
    pub const fn new() -> Heap {
        Heap {
            first_block: None,
            block_count: 0
        }
    }

    pub fn init(&mut self, heap_start: usize, heap_size: usize) -> Result<(), &'static str> {
        if self.first_block.is_some() {
            return Err("This heap is already initialized.")
        }

        // first make sure we are aligned
        let mask = Block::alignment() - 1;
        let start = (heap_start + mask) & !mask;

        if heap_size <= (start - heap_start) {
            return Err("Cannot align the heap.")
        }

        debug_assert!(start > heap_start);
        debug_assert!(heap_size > (start - heap_start));

        let size = heap_size - (start - heap_start);

        #[test]
        println!("heap_start={:x} start={:x} size={}", heap_start, start, size);

        let res = Block::init(start as *const u8 as *mut u8, size);

        #[test]
        println!("Block::init(start={:x}, size={})={:?}", start, size, res);

        if let Err(err) = res {
            return Err(match err {
                BlockError::NotEnoughMemory => "This heap is too small."
            })
        }

        let (block_count, first_block) = res.unwrap();
        self.first_block = Some(first_block);
        self.block_count = block_count;

        Ok(())
    }
}

unsafe impl<'a> Alloc for &'a Heap {
    unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, AllocErr> {
        if layout.align() > Block::alignment() {
            return Err(AllocErr::invalid_input("Cannot align to more than the system's register size."))
        }
        if layout.align().count_ones() != 1 {
            return Err(AllocErr::invalid_input("Alignment must be a power of 2."))
        }

        Err(AllocErr::Exhausted { request: layout })
    }
    unsafe fn dealloc(&mut self, _ptr: *mut u8, _layout: Layout) {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::{Heap, Layout, AllocErr, Alloc};
    use ::block::{Block, MIN_PAYLOAD_SIZE, MAX_PAYLOAD_SIZE};

    /// we return the vector here so it is not dropped when this method returns
    fn new_heap(offset: usize, size: usize) -> Result<(Vec<u8>, Heap, *mut Block), &'static str> {
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

            println!("0x{:x}!={:?}", start, aligned_start);

            Ok((vec, h, aligned_start))
        }
    }

    #[test]
    fn test_heap_is_too_small_to_align() {
        let res = new_heap(3, 5);
        assert_eq!("Cannot align the heap.", res.err().unwrap());
    }

    #[test]
    fn test_heap_is_too_small() {
        let res = new_heap(3, (Block::hdr_csize() + 1) * Block::alignment());
        assert_eq!("This heap is too small.", res.err().unwrap());
    }

    #[test]
    fn test_heap_cannot_be_initialized_twice() {
        let (vec, mut h, _) = new_heap(3, (Block::hdr_csize() + MIN_PAYLOAD_SIZE + 1) * Block::alignment())
            .ok().unwrap();
        assert_eq!(Err("This heap is already initialized."),
                   h.init(1234, 567890));
        drop(vec); /* explicit drop to ensure it is not optimized out */
    }

    #[test]
    fn test_heap_init_with_minimal_size() {
        let res = new_heap(3, (Block::hdr_csize() + MIN_PAYLOAD_SIZE + 1) * Block::alignment());
        let (vec, h, first_block) = res.ok().unwrap();

        assert_eq!(1, h.block_count);
        assert_eq!(Some(first_block), h.first_block);
        drop(vec); /* explicit drop to ensure it is not optimized out */
    }

    #[test]
    fn test_heap_init_with_a_bit_more_than_max_block_size() {
        let (vec, h, first_block) =
            new_heap(3, (Block::hdr_csize() + MAX_PAYLOAD_SIZE)* Block::alignment() + 3)
            .ok().unwrap();
        assert_eq!(1, h.block_count);
        assert_eq!(Some(first_block), h.first_block);
        drop(vec); /* explicit drop to ensure it is not optimized out */
    }

    #[test]
    fn test_alloc_cannot_aligned_more_than_machine_alignment() {
        let (vec, h, _) = new_heap(3, (Block::hdr_csize() + MAX_PAYLOAD_SIZE) * 4 + 3).ok().unwrap();
        unsafe {
            let layout = Layout::from_size_align_unchecked(3, Block::alignment() * 2);
            assert_eq!(Err(AllocErr::invalid_input("Cannot align to more than the system's register size.")),
                       (&h).alloc(layout));
        }
        assert_eq!(1, h.block_count);
        drop(vec);
    }

    #[test]
    fn test_alloc_only_supports_power_of_two_alignment() {
        let (vec, h, _) = new_heap(3, (Block::hdr_csize() + MAX_PAYLOAD_SIZE) * 4 + 3).ok().unwrap();
        unsafe {
            let layout = Layout::from_size_align_unchecked(3, 3);
            assert_eq!(Err(AllocErr::invalid_input("Alignment must be a power of 2.")),
                       (&h).alloc(layout));
        }
        assert_eq!(1, h.block_count);
        drop(vec);
    }

    #[test]
    fn test_alloc_fails_if_there_is_no_more_room_for_it() {
        unimplemented!()
    }

    #[test]
    fn test_alloc_find_the_first_fitting_block() {
        unimplemented!()
    }

    #[test]
    fn test_alloc_splits_the_block_if_it_is_big_enough() {
        unimplemented!()
    }
/*
    #[test]
    fn test_() {
        unimplemented!()
    }
*/
}