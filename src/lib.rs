#![feature(compiler_builtins_lib)]
#![feature(allocator)]
#![allocator]
#![no_std]

extern crate silica_chunks as chunks;
extern crate compiler_builtins;

use chunks::*;
use core::ptr;

extern "C" {
    static heap_start: usize;
    static heap_size: usize;
}
extern {
    fn critical_section_enter();
    fn critical_section_exit();
}

static mut HEAP: Option<Heap<'static >> = Option::None;

pub fn init()
{
    unsafe {
        let a = &heap_start;
        let b = a as *const usize;
        let c = b as *mut u8;

        let d = &heap_size;
        let e = d as *const usize;
        let f = e as usize;

        let mut mem: &'static mut [u8] = core::slice::from_raw_parts_mut(c, f);
        HEAP = Some(Heap::new(mem));
    }
}

#[no_mangle]
pub extern fn __rust_allocate(size: usize, _align: usize) -> *mut u8 {
    if _align > Chunk::alignment() ||
       !usize::is_power_of_two(_align) {
        panic!("Aligment only supported up to Chunk::alignment() and must be a power of 2");
    }

    if size == 0 {
        panic!("Unsupported zerosized allocation.");
    }

    // panic if asked too big
    let chunk_size = Chunk::to_csize(size);
    if chunk_size > Chunk::max_size() {
        panic!("Allocations are limited to Chunk::max_size()");
    }

    let mut h = unsafe {
        match HEAP {
            None => panic!("Allocator is not initialized"),
            Some(ref mut h) => h
        }
    };

    unsafe { critical_section_enter() };

    // find first free big enough
    let mut c0 = match h.find(chunk_size) {
        None => return ptr::null_mut(),
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
    h.to_ptr(c0)
}

#[no_mangle]
pub extern fn __rust_deallocate(ptr: *mut u8, _old_size: usize, _align: usize) {
    let mut h = unsafe {
        match HEAP {
            None => panic!("Allocator is not initialized"),
            Some(ref mut h) => h
        }
    };

    unsafe { critical_section_enter() };
    let c1 = h.from_ptr(ptr);
    /*
        used -= c1.size();
    */
    c1.set_is_allocated(false);
    h.absorb_next(c1);

    if let Some(c0) = c1.previous() {
        h.absorb_next(c0);
    }
    // unLock
    unsafe { critical_section_exit() };
}

#[allow(unused_variables)]
#[no_mangle]
pub extern fn __rust_reallocate(ptr: *mut u8, _old_size: usize, size: usize,
                                _align: usize) -> *mut u8 {

    if size == 0 {
        panic!("Unsupported 0 sized allocation")
    }

    let csize = Chunk::to_csize(size);
    if csize > Chunk::max_size() {
        panic!("Allocations are limited to Chunk::max_size()");
    }

    if ptr == ptr::null_mut() {
        return __rust_allocate(size, _align)
    }

    let h = unsafe {
        match HEAP {
            None => panic!("Allocator is not initialized"),
            Some(ref mut h) => h
        }
    };

    unsafe { critical_section_enter() };

    let mut c1 = h.from_ptr(ptr);
    if csize > c1.size() {
        let optc0 = c1.previous();
        let optc2 = c1.next();

        let c0_csize = match optc0 {
            Some(ref c0) => c0.size(),
            None => 0
        };
        let c1_csize = c1.size();
        let c2_csize = match optc2 {
            Some(ref c2) => c2.size(),
            None => 0
        };

        /*
        used -= c1.size();
        */
        if csize <= (c1_csize + c2_csize) {
            h.absorb_next(c1);
        } else if csize <= (c0_csize + c1_csize) {
            c1 = optc0.unwrap();
            h.absorb_next(c1);
        } else if csize <= (c0_csize + c1_csize + c2_csize) {
            h.absorb_next(c1);
            c1 = optc0.unwrap();
            h.absorb_next(c1);
        }
        /*
        used += c1.size();
        */
    }

    if csize > c1.size() {
        let out = __rust_allocate(size, _align) as *mut usize;
        if out == ptr::null_mut() {
            // unlock
            return ptr::null_mut()
        }
        unsafe { ptr::copy::<usize>(out, h.to_ptr(c1), size) }
        __rust_deallocate(h.to_ptr(c1) as *mut u8, 0, 0);
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
    h.to_ptr(c1)
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
