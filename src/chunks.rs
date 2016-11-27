use core::mem::size_of;
use core::cmp::min;
use core::ptr;

/// Defines the minimum payload of a chunk excluding the header size as number of platform's alignment unit.
pub const MIN_PAYLOAD_LEN: usize = 1;

/// Defines the maximum chunk size including header & payload in platform's alignment unit.
pub const MAX_CHUNK_SIZE: usize = 0x7FFF;

const FLAG_ALLOCATED: u16 = 0x8000;
const FLAG_LAST: u16 = 0x8000;

#[derive(Debug,PartialEq)]
pub struct Chunk {
    /// previous chunk size in alignment unit.
    prev_size: u16,
    /// this Chunk size in alignment unit.
    size: u16
}

impl Chunk {

    pub fn alignment() -> usize {
        size_of::<usize>()
    }

    pub fn to_padded_csize(size: usize) -> usize {
        (size + Chunk::alignment() - 1) / Chunk::alignment()
    }

    pub fn to_csize(size: usize) -> usize {
        Chunk::hdr_csize() + Chunk::to_padded_csize(size)
    }

    pub fn hdr_csize() -> usize {
        Chunk::to_padded_csize(size_of::<Chunk>())
    }

    pub fn min_size() -> usize {
        Chunk::hdr_csize() + MIN_PAYLOAD_LEN
    }

    pub fn max_size() -> usize {
        MAX_CHUNK_SIZE
    }

    pub fn size(&self) -> usize {
        (self.size & !FLAG_ALLOCATED) as usize
    }
    pub fn set_size(&mut self, size: usize) {
        if  size < Chunk::min_size() || Chunk::max_size() < size {
            panic!("size must be in Chunk::min_size()...Chunk::max_size()");
        }

        let size = size as u16;
        self.size = (size & !FLAG_ALLOCATED) | (self.size & FLAG_ALLOCATED);
    }

    pub fn prev_size(&self) -> usize {
        (self.prev_size & !FLAG_LAST) as usize
    }
    pub fn set_prev_size(&mut self, prev_size: usize) {
        // what about prev_size on first chunk ??
        if prev_size != 0 &&
           (prev_size < Chunk::min_size() || Chunk::max_size() < prev_size) {
            panic!("prev_size must be in Chunk::min_size()...Chunk::max_size()");
        }

        let prev_size = prev_size as u16;
        self.prev_size = (prev_size & !FLAG_LAST) | (self.prev_size & FLAG_LAST);
    }

    pub fn is_allocated(&self) -> bool {
        (self.size & FLAG_ALLOCATED) == FLAG_ALLOCATED
    }
    pub fn set_is_allocated(&mut self, allocated: bool) {
        if allocated {
            self.size = self.size | FLAG_ALLOCATED;
        } else {
            self.size = self.size & !FLAG_ALLOCATED;
        }
    }

    pub fn is_last(&self) -> bool {
        (self.prev_size & FLAG_LAST) == FLAG_LAST
    }
    pub fn set_is_last(&mut self, is_last: bool) {
        if is_last {
            self.prev_size = self.prev_size | FLAG_LAST;
        } else {
            self.prev_size = self.prev_size & !FLAG_LAST;
        }
    }

    pub fn previous<'a, 'b>(&'a self) -> Option<&'b mut Chunk> {
        if self.prev_size() == 0 {
            return None
        }

        let ptr = self as *const Chunk as *mut usize;
        Some(unsafe { &mut *(ptr.offset(-(self.prev_size() as isize)) as *mut Chunk) })
    }

    pub fn next<'a, 'b>(&'a self) -> Option<&'b mut Chunk> {
        if self.is_last() {
            return None
        }

        let ptr = self as *const Chunk as *mut usize;
        Some(unsafe { &mut *(ptr.offset(self.size() as isize) as *mut Chunk) })
    }
}

pub struct Heap<'a> {
    heap: &'a mut [u8],
    chunk_count: usize
}

impl<'a> Heap<'a> {
    pub fn new(heap: &'a mut [u8]) -> Heap {
        let mut h = Heap {
            heap: heap,
            chunk_count: 0
        };

        let mut alignment_unit_count = h.heap.len() / Chunk::alignment();
        if alignment_unit_count < Chunk::min_size() {
            panic!("heap must contain at least {} alignment unit", Chunk::min_size());
        }

        let mut prev_size = 0;
        let mut c = h.first_chunk();
        loop {
            let size = min(alignment_unit_count, Chunk::max_size());
            c.set_prev_size(prev_size);
            c.set_size(size);
            c.set_is_allocated(false);
            c.set_is_last(false);

            h.chunk_count += 1;

            prev_size = size;
            alignment_unit_count -= size;
            if alignment_unit_count < Chunk::min_size() {
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
        unsafe { &mut *(self.heap.as_ptr() as *mut Chunk) }
    }

    pub fn to_ptr<T>(&self, c0: &Chunk) -> *mut T {
        unsafe {
            (c0 as *const Chunk as *const usize).offset(Chunk::hdr_csize() as isize) as *mut T
        }
    }

    pub fn from_ptr<'b, T>(&self, ptr: *const T) -> &'b mut Chunk {
        unsafe { &mut *((ptr as *const usize).offset(-(Chunk::hdr_csize() as isize)) as *mut Chunk) }
    }

    pub fn absorb_next(&mut self, c0: &mut Chunk) {
        let c1 = match c0.next() {
            Some(c) => c,
            None => return
        };

        if c0.is_allocated() && c1.is_allocated() {
            panic!("Chunks must not be both allocated");
        }

        let new_size = c0.size() + c1.size();
        // would overflow, do nothing.
        if new_size > Chunk::max_size() {
            return
        }

        self.chunk_count -= 1;
        c0.set_size(new_size);
        c0.set_is_last(c1.is_last());
        let new_is_allocated = c0.is_allocated() || c1.is_allocated();
        c0.set_is_allocated(new_is_allocated);

        if let Some(c) = c0.next() {
            c.set_prev_size(c0.size());
        }

        if c1.is_allocated() {
            unsafe { ptr::copy::<usize>(self.to_ptr(c1), self.to_ptr(c0), (c1.size() - Chunk::hdr_csize()) * Chunk::alignment()) };
        }
    }

    pub fn split<'b>(&mut self, c0: &mut Chunk, size: usize) -> Option<&'b mut Chunk> {
        let new_size = c0.size() - size;
        if  new_size < Chunk::min_size() ||
            size < Chunk::min_size() {
            return None
        }

        self.chunk_count += 1;
        let c2 = c0.next();
        c0.set_size(size);
        c0.set_is_last(false);

        // here we are sure that next will not be None
        let c1 = c0.next().unwrap();
        c1.set_size(new_size);
        c1.set_prev_size(size);
        c1.set_is_allocated(false);

        if let Some(c2) = c2 {
            c2.set_prev_size(new_size);
            c1.set_is_last(false);
        } else {
            // if next was not Some(_) then self was the last
            c1.set_is_last(true);
        }

        Some(c1)
    }

    pub fn find<'b>(&mut self, size: usize) -> Option<&'b mut Chunk> {
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
