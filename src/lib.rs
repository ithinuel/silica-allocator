#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), feature(global_allocator, alloc))]
#![feature(allocator_api)]
#![feature(const_fn)]

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
mod heap;

pub use block::Block;
use heap::Heap;
/*
extern "C" {
    #[allow(non_upper_case_globals)]
    static heap_start: usize;
    #[allow(non_upper_case_globals)]
    static heap_size: usize;
}

extern {
    fn critical_section_enter();
    fn critical_section_exit();
}*/

#[derive(Debug)]
pub struct SafeHeap {
    inner: Heap
}

unsafe impl marker::Sync for SafeHeap {}

unsafe impl<'a> Alloc for &'a SafeHeap {
    unsafe fn alloc(&mut self, _layout: Layout) -> Result<*mut u8, AllocErr> {
        unimplemented!()
    }
    unsafe fn dealloc(&mut self, _ptr: *mut u8, _layout: Layout) {
        unimplemented!()
    }
}


/// Initializes the heap.
///
/// **This must be called prior to any use of dynamically allocated memory.**
///
/// # Arguments :
///
/// * `heap_start` -  heap start address.
/// * `heap_size` - heap size.
/// ```
///
pub unsafe fn init<'a>() -> Result<(), &'static str> {
    unimplemented!()
}

#[cfg_attr(not(test), global_allocator)]
pub static mut ALLOCATOR: SafeHeap = SafeHeap { inner: Heap::new() };

/*
#[cfg(test)]
extern crate test;

#[cfg(test)]
pub mod tests {
    use std::vec::Vec;
    use std::mem::forget;
    use std::heap::{Alloc, AllocErr, Layout};
    use super::{Heap, ALLOCATOR};
    use test::{Bencher, black_box};

    #[no_mangle]
    #[allow(non_upper_case_globals)]
    pub static mut heap_size: usize = 1024;
    #[no_mangle]
    #[allow(non_upper_case_globals)]
    pub static mut heap_start: usize = 0;

    static mut CRITICAL_SECTION: usize = 0;
    #[no_mangle]
    pub fn critical_section_enter() {
        unsafe {
            assert_eq!(0, CRITICAL_SECTION);
            CRITICAL_SECTION += 1;
        }
    }
    #[no_mangle]
    pub fn critical_section_exit() {
        unsafe {
            assert_eq!(1, CRITICAL_SECTION);
            CRITICAL_SECTION -= 1;
        }
    }

    /// # Arguments :
    ///
    /// * `size -` Heap size to initialize.
    fn setup(size: usize) -> (Vec<u8>, Heap) {
        let mut heap = Heap { first_block: None, block_count: 0 };
//
//        let mut vec: Vec<u8> = Vec::with_capacity(size + 3);
//        vec.resize(size + 3, 0);
//
//        let start = vec.as_mut_slice().as_mut_ptr() as usize + 3;
//
//        assert_eq!(Ok(()), unsafe { heap.init(start, size+3) });
//        (vec, heap)
        (Vec::new(), heap)
    }

    /// # Arguments :
    ///
    /// * `cnt -` expected block count.
    ///
    fn tear_down(heap: Heap, cnt: usize) {
    }

    #[test]
    fn test_cant_init_if_heap_is_too_small() {
        // setup ALLOCATOR



        // cleanup ALLOCATOR
    }

    fn add(i: u64) -> u64 {
        i + i + 1
    }

    #[bench]
    #[cfg(bench)]
    fn bench_random_alloc_and_free(b: &mut Bencher) {
        b.iter(|| {
            let n = black_box(100000);
            let mut i = 0;
            for _ in 0..n { i = add(i) }
        });
    }

    // dealloc
    // realloc
    // grow_in_place
    // shrink_in_place
    // oom

}
*/
/*
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