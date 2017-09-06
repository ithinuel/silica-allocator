use ::block::{Block, BlockError, MIN_PAYLOAD_LEN};


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

#[cfg(test)]
mod tests {
    use super::Heap;
    use ::block::{Block, MIN_PAYLOAD_LEN};

    #[test]
    fn test_heap_is_too_small_to_align() {
        let offset = 3;
        let size = 2 + offset;

        let mut vec: Vec<u8> = Vec::with_capacity(size);
        vec.resize(size, 0);
        let start = vec.as_mut_slice().as_mut_ptr() as usize + offset;

        let mut h = Heap::new();

        assert_eq!(Err("Cannot align the heap."), h.init(start, size-offset));
    }

    #[test]
    fn test_heap_is_too_small() {
        let offset = 3;
        let size = (Block::hdr_csize() + 1) * Block::alignment(); // the +1 here is for alignment purposes

        let mut vec: Vec<u8> = Vec::with_capacity(size);
        vec.resize(size, 0);
        let start = vec.as_mut_slice().as_mut_ptr() as usize + offset;

        let mut h = Heap::new();

        assert_eq!(Err("This heap is too small."), h.init(start, size-offset));
    }

    #[test]
    fn test_heap_cannot_be_initialized_twice() {
        let offset = 3;
        let size = (Block::hdr_csize() + MIN_PAYLOAD_LEN + 1) * Block::alignment(); // the +1 here is for alignment purposes

        let mut vec: Vec<u8> = Vec::with_capacity(size);
        vec.resize(size, 0);
        let start = vec.as_mut_slice().as_mut_ptr() as usize + offset;

        let mut h = Heap::new();
        h.init(start, size - offset);

        assert_eq!(Err("This heap is already initialized."), h.init(start, size - offset));
    }

    #[test]
    fn test_heap_init_with_minimal_size() {
        let offset = 3;
        let size = (Block::hdr_csize() + MIN_PAYLOAD_LEN + 1) * Block::alignment(); // the +1 here is for alignment purposes

        let mut vec: Vec<u8> = Vec::with_capacity(size);
        vec.resize(size, 0);
        let start = vec.as_mut_slice().as_mut_ptr() as usize + offset;

        let mask = Block::alignment() - 1;
        let aligned_start = ((start + mask) & !mask) as *mut Block;

        println!("0x{:x}!={:?}", start, aligned_start);

        let mut h = Heap::new();
        assert_eq!(Ok(()), h.init(start, size - offset));
        assert_eq!(1, h.block_count);
        assert_eq!(Some(aligned_start), h.first_block);
    }
}