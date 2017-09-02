#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), feature(alloc))]
#![feature(allocator_api)]
#![cfg_attr(not(test), feature(global_allocator))]

#[cfg(not(test))]
extern crate alloc;
#[cfg(not(test))]
use alloc::heap::{Alloc, AllocErr, Layout};
#[cfg(not(test))]
use core::marker;

#[cfg(test)]
use std::heap::{Alloc, AllocErr, Layout};
#[cfg(test)]
use std::marker;

mod block;
pub use block::{Block};

extern "C" {
    static heap_start: usize;
    static heap_size: usize;
}

extern {
    fn critical_section_enter();
    fn critical_section_exit();
}

pub struct Heap {
    first_block: Option<*mut Block>,
    block_count: usize
}

unsafe impl marker::Sync for Heap {}

unsafe impl<'a> Alloc for &'a Heap {
    unsafe fn alloc(&mut self, _layout: Layout) -> Result<*mut u8, AllocErr> {

        Ok(0 as *mut u8)
    }
    unsafe fn dealloc(&mut self, _ptr: *mut u8, _layout: Layout) {
    }
}

impl Heap {
    pub unsafe fn init<'a>() -> Result<(), &'static str> {
        critical_section_enter();

        if ALLOCATOR.first_block.is_some() {
            critical_section_exit();
            return Err("Heap is already initialized.");
        }


        // first make sure we are aligned
        let mask = Block::alignment() - 1;
        let start = (heap_start + mask) & !mask;
        let size = heap_size - (start - heap_start);

        #[test]
        println!("heap_start={:x} start={:x} size={}", heap_start, start, size);

        let res = Block::init(start as *const u8 as *mut u8,
                              size);

        #[test]
        println!("Block::init(start={:x}, size={})={:?}", start, size, res);

        if res.is_err() {
            critical_section_exit();
            return Err("Memory initialization failure.");
        }

        let (block_count, first_block) = res.unwrap();
        ALLOCATOR.first_block = Some(first_block);
        ALLOCATOR.block_count = block_count;

        critical_section_exit();
        Ok(())
    }
}

#[cfg_attr(not(test), global_allocator)]
static mut ALLOCATOR: Heap = Heap { first_block: None, block_count: 0 };

#[cfg(test)]
pub mod tests {
    use std::vec::Vec;
    use std::mem::forget;
    use super::{Heap, ALLOCATOR};

    #[no_mangle]
    #[allow(non_upper_case_globals)]
    pub static mut heap_size: usize = 1024;
    #[no_mangle]
    #[allow(non_upper_case_globals)]
    pub static mut heap_start: usize = 0;

    #[no_mangle]
    pub fn critical_section_enter() {}
    #[no_mangle]
    pub fn critical_section_exit() {}

    #[test]
    fn test_init() {
        let size = 2048;
        unsafe {
            let mut vec: Vec<u8> = Vec::with_capacity(size);
            vec.resize(size, 0);

            heap_start = vec.as_mut_slice().as_mut_ptr() as usize + 3;
            heap_size = size;
            forget(vec);
        }
        let res = unsafe { Heap::init() };
        assert_eq!(Ok(()), res);
        assert_eq!(1, unsafe { ALLOCATOR.block_count } );
    }
}

/*
use chunks::Chunk;
use core::ptr;
use core::intrinsics::write_bytes;


pub enum HeapError {
    NotEnoughMemory
}


impl Heap {
    pub fn new<'a>(heap: &'a mut u8) -> Result<Heap, HeapError> {
        let mut h = Heap {
            heap: heap.as_ptr(),
            chunk_count: 0
        };

        let mut alignment_unit_count = h.heap.len() / Chunk::alignment();
        if alignment_unit_count < (MIN_PAYLOAD_LEN) {
            return Err(HeapError::NotEnoughMemory)
        }

        let mut prev_size = 0;
        let mut c = h.first_chunk();
        loop {
            let size = min(alignment_unit_count, MAX_PAYLOAD_LEN);
            c.set_prev_size(prev_size);
            c.set_size(size);
            c.set_is_allocated(false);
            c.set_is_last(false);

            h.chunk_count += 1;

            prev_size = size;
            alignment_unit_count -= size;
            if alignment_unit_count < MIN_PAYLOAD_LEN {
                break;
            }

            c = c.next().unwrap();
        }
        c.set_is_last(true);

         h
    }

    pub fn chunk_count(&self) -> usize {
        self.chunk_count
    }

    pub fn first_chunk<'b>(&self) -> &'b mut Chunk {
        unsafe { &mut *(self.heap as *mut Chunk) }
    }

    fn find<'b>(&mut self, size: usize) -> Option<&'b mut Chunk> {
        let mut c = self.first_chunk();
        while c.size() < size || c.is_allocated() {
            c = match c.next() {
                Some(chunk) => chunk,
                None => return None
            }
        }

        Some(c)
    }
}

#[unstable(feature = "allocator_api", issue = "32838")]
unsafe impl Alloc for Heap {
    #[inline]
    unsafe fn alloc(&mut self, layout: Layout) -> Result<*mut u8, AllocErr> {
        if layout.align() > Chunk::alignment() ||
            !usize::is_power_of_two(_align) {
            panic!("Aligment only supported up to Chunk::alignment() and must be a power of 2");
        }

        if layout.size == 0 {
            panic!("Unsupported zero sized allocation.");
        }

        // panic if asked too big
        let chunk_size = Chunk::to_csize(layout.size());
        if chunk_size > Chunk::max_size() {
            panic!("Allocations are limited to Chunk::max_size()");
        }

        unsafe { critical_section_enter() };

        let h = self.heap.unwrap();
        // find first free big enough
        let mut c0 = match h.find(chunk_size) {
            None => {

                unsafe { critical_section_exit() };
                return Err(AllocErr::Exhausted { request: layout })
            },
            Some(chunk) => chunk
        };

        //  try to split at the wanted size
        //  if split successful and the new chunk has a follower and the follower is not allocated
        if let Some(c1) = h.split(c0, chunk_size) {
            if let Some(c2) = c1.next() {
                // do not change c2 if it is allocated as it may lead to a dangling pointer
                if !c2.is_allocated() {
                    // try to merge the new chunk with the following one
                    h.absorb_next(c1);
                }
            }
        }

        //  mark chunk as allocated
        c0.set_is_allocated(true);

        /*
        used += c0.size();
        if high_watermark < used {
            high_watermark = used;
        }
        */

        // unlock
        unsafe { critical_section_exit() };
        Ok(h.to_ptr(c0))
    }

    #[inline]
    fn usable_size(&self, layout: &Layout) -> (usize, usize) {
        let guaranteed_size = Chunk::to_padded_csize(layout.size());
        (guaranteed_size, guaranteed_size)
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: *mut u8, _layout: Layout) {
        unsafe { critical_section_enter() };

        let h = self.heap.unwrap();

        let c1 = h.from_ptr(ptr);
        /*
            used -= c1.size();
        */
        c1.set_is_allocated(false);
        if let Some(c2) = c1.next() {
            if !c2.is_allocated() {
                drop(c2);
                h.absorb_next(c1);
            }
        }
        if let Some(c0) = c1.previous() {
            if !c0.is_allocated() {
                h.absorb_next(c0);
            }
        }
        // unLock
        unsafe { critical_section_exit() };
    }

    #[inline]
    unsafe fn realloc(&mut self,
                      ptr: *mut u8,
                      old_layout: Layout,
                      new_layout: Layout) -> Result<*mut u8, AllocErr> {
        if new_layout.size() == 0 {
            return Err(AllocErr::Unsupported {
                details: "cannot allocated 0 bytes",
            })
        }

        let csize = Chunk::to_csize(new_layout.size());
        if csize > Chunk::max_size() {
            return Err(AllocErr::Unsupported {
                details: "allocations are limited to `Chunk::max_size()`",
            })
        }

        if old_layout.align() != new_layout.align() {
            return Err(AllocErr::Unsupported {
                details: "cannot change alignment on `realloc`",
            })
        }

        if ptr == ptr::null_mut() {
            return self.alloc(new_layout)
        }

        unsafe { critical_section_enter() };

        let h = self.heap.unwrap();

        let mut c1 = h.from_ptr(ptr);
        // we have to grow ?
        if csize > c1.size() {
            // read neighborhood's sizes.
            let opt_c0 = c1.previous();
            let opt_c2 = c1.next();

            let c0_csize = match opt_c0 {
                Some(ref c0) => c0.size(),
                None => 0
            };
            let c1_csize = c1.size();
            let c2_csize = match opt_c2 {
                Some(ref c2) => c2.size(),
                None => 0
            };

            /*
            used -= c1.size();
            */
            if csize <= (c1_csize + c2_csize) {
                h.absorb_next(c1);
            } else if csize <= (c0_csize + c1_csize) {
                c1 = opt_c0.unwrap();
                h.absorb_next(c1);
            } else if csize <= (c0_csize + c1_csize + c2_csize) {
                h.absorb_next(c1);
                c1 = opt_c0.unwrap();
                h.absorb_next(c1);
            }
            /*
            used += c1.size();
            */
        }

        if csize > c1.size() {
            let out = self.alloc(new_layout);
            if out == ptr::null_mut() {
                // unlock
                return ptr::null_mut()
            }
            unsafe { ptr::copy::<usize>(out, h.to_ptr(c1), size) }
            self.dealloc(h.to_ptr(c1), old_layout);
            c1 = h.from_ptr(out);
        } else {
            if let Some(c2) = h.split(c1, csize) {
                /*
                // c2.size() is now free
                used -= c2.size();
                */
                if let Some(c3) = c2.next() {
                    if !c3.is_allocated() {
                        h.absorb_next(c2);
                    }
                }
            }
            /*
            if high_watermark < used {
                high_watermark = used;
            }
            */
        }
        // unlock
        unsafe { critical_section_exit() };
        Ok(h.to_ptr(c1))
    }

    unsafe fn grow_in_place(&mut self,
                            ptr: *mut u8,
                            layout: Layout,
                            new_layout: Layout) -> Result<(), CannotReallocInPlace> {
        // check if we can absorb next
        unsafe { critical_section_enter() };

        let h = self.heap.unwrap();

        let mut c1 = h.from_ptr(ptr);
        // we have to grow ?
        if csize > c1.size() {
            // read neighborhood's sizes.
            let opt_c0 = c1.previous();
            let opt_c2 = c1.next();

            let c0_csize = match opt_c0 {
                Some(ref c0) => c0.size(),
                None => 0
            };
            let c1_csize = c1.size();
            let c2_csize = match opt_c2 {
                Some(ref c2) => c2.size(),
                None => 0
            };

            /*
            used -= c1.size();
            */
            if csize <= (c1_csize + c2_csize) {
                h.absorb_next(c1);
            } else if csize <= (c0_csize + c1_csize) {
                c1 = opt_c0.unwrap();
                h.absorb_next(c1);
            } else if csize <= (c0_csize + c1_csize + c2_csize) {
                h.absorb_next(c1);
                c1 = opt_c0.unwrap();
                h.absorb_next(c1);
            }
            /*
            used += c1.size();
            */
            unsafe { critical_section_exit() };
            Ok(())
        }



        let _ = ptr; // this default implementation doesn't care about the actual address.
        debug_assert!(new_layout.size >= layout.size);
        debug_assert!(new_layout.align == layout.align);
        let (_l, u) = self.usable_size(&layout);
        // _l <= layout.size()                       [guaranteed by usable_size()]
        //       layout.size() <= new_layout.size()  [required by this method]
        if new_layout.size <= u {
            return Ok(());
        } else {
            return Err(CannotReallocInPlace);
        }
    }

    unsafe fn shrink_in_place(&mut self,
                              ptr: *mut u8,
                              layout: Layout,
                              new_layout: Layout) -> Result<(), CannotReallocInPlace> {
        // check if we can split

        let _ = ptr; // this default implementation doesn't care about the actual address.
        debug_assert!(new_layout.size <= layout.size);
        debug_assert!(new_layout.align == layout.align);
        let (l, _u) = self.usable_size(&layout);
        //                      layout.size() <= _u  [guaranteed by usable_size()]
        // new_layout.size() <= layout.size()        [required by this method]
        if l <= new_layout.size {
            return Ok(());
        } else {
            return Err(CannotReallocInPlace);
        }
    }

    fn oom(&mut self, err: AllocErr) -> ! {
        use core::fmt::{self, Write};

        // Print a message to the reset cause buffer before resetting to assist with
        // debugging. It is critical that this code does not allocate any
        // memory since we are in an OOM situation. Any errors are ignored
        // while printing since there's nothing we can do about them and we
        // are about to exit anyways.
        drop(writeln!(ResetCauseBuffer, "fatal runtime error: {}", err));
        unsafe {
            ::core::intrinsics::abort();
        }

        struct ResetCauseBuffer;
        impl Write for ResetCauseBuffer {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                Ok(())
            }
        }
    }
}

pub fn init() {
    unsafe {
        let start = &heap_start as *const usize as *mut u8;
        let size = &heap_size as *const usize as usize;

        let mut mem: &'static mut [u8] = core::slice::from_raw_parts_mut(start, size);

        critical_section_enter();
        HEAP = Some(Heap::new(mem));
        critical_section_exit();
    }
}

#[allow(unused_variables)]
#[no_mangle]
pub extern fn __rust_reallocate_inplace(_ptr: *mut u8, old_size: usize,
                                        _size: usize, _align: usize) -> usize {
    let sz = Chunk::to_padded_csize(_size) * Chunk::alignment();
    if _size <= sz && Chunk::to_csize(_size) <= Chunk::max_size() {
        __rust_reallocate(_ptr, old_size, _size, _align);
        _size
    } else {
        old_size
    }
}

#[no_mangle]
pub extern fn __rust_usable_size(size: usize, _align: usize) -> usize {
    Chunk::to_padded_csize(size) * Chunk::alignment()
}
*/