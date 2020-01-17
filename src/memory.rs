use std::collections::HashMap;
use std::collections::BTreeMap;

/// Represents the main memory.
/// It can be implemented by any structure which can handle loads and stores.
///
/// Using a trait enables us to implement direct-mapped memory, RAM with MMU,
/// or any other kind of memory interface.
pub trait Memory {
    fn get_8(&self, addr:usize) -> u8;
    fn get_16(&self, addr:usize) -> u16 {
        let low = self.get_8(addr) as u16;
        let high = self.get_8(addr.wrapping_add(1)) as u16;
        (high << 8) | low
    }

    fn get_32(&self, addr:usize) -> u32 {
        let low = self.get_16(addr) as u32;
        let high = self.get_16(addr.wrapping_add(2)) as u32;
        (high << 16) | low
    }
    fn set_8(&mut self, addr:usize, value:u8);
    fn set_16(&mut self, addr:usize, value:u16) {
        self.set_8(addr, (value & 0xFF) as u8);
        self.set_8(addr.wrapping_add(1), ((value >> 8) & 0xFF) as u8)
    }

    fn set_32(&mut self, addr:usize, value:u32) {
        self.set_16(addr, (value & 0xFFFF) as u16);
        self.set_16(addr.wrapping_add(2), ((value >> 16) & 0xFFFF) as u16)
    }

    fn allocate_at(&mut self, start:usize, size:usize) -> bool;
}

/// Simple Memory implementation for [u8] slices
impl<'a> Memory for &'a mut [u8] {
    fn get_8(&self, addr:usize) -> u8 {
        self[addr]
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        self[addr] = value
    }

    fn allocate_at(&mut self, _start:usize, _size:usize) -> bool {
        false
    }
}

/// Simple Memory implementation for u8 dynamic arrays (Vec<u8>)
impl Memory for Vec<u8> {
    fn get_8(&self, addr:usize) -> u8 {
        self[addr]
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        self[addr] = value
    }

    fn allocate_at(&mut self, start:usize, size:usize) -> bool {
        if start + size >= self.len() {
            self.resize(start + size, 0);
        }
        true
    }
}

/// Simple Memory implementation for u32 dynamic arrays (Vec<u32>)
impl Memory for Vec<u32> {
    fn get_8(&self, addr:usize) -> u8 {
        (self[addr / 4] >> ((3 - addr % 4) * 8)) as u8
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        let x = &mut self[addr / 4];
        *x = match addr % 4 {
            0 => (*x & 0x00FFFFFF) | ((value as u32) << 24),
            1 => (*x & 0xFF00FFFF) | ((value as u32) << 16),
            2 => (*x & 0xFFFF00FF) | ((value as u32) << 8),
            _ => (*x & 0xFFFFFF00) | (value as u32),
        }
    }

    fn allocate_at(&mut self, start:usize, size:usize) -> bool {
        if start + size >= self.len() * 4 {
            self.resize((start + size + 3) / 4, 0);
        }
        true
    }
}

impl Memory for HashMap<usize, u32> {
    fn get_8(&self, addr:usize) -> u8 {
        let addr32 = addr - (addr % 4);
        self.get(&addr32).map_or_else(
            || panic!("HashMap<usize, u32>::get_8(0x{:x})", addr),
            
            | x | {
            ((x >> (8 * (3 - addr % 4))) & 0xFF) as u8
        })
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        let addr32 = addr - (addr % 4);
        match self.get_mut(&addr32) {
            Some(x) => {
                match addr % 4 {
                    0 => *x = (*x & 0x00FFFFFF) | ((value as u32) << 24),
                    1 => *x = (*x & 0xFF00FFFF) | ((value as u32) << 16),
                    2 => *x = (*x & 0xFFFF00FF) | ((value as u32) << 8),
                    _ => *x = (*x & 0xFFFFFF00) | ((value as u32) << 0),
                }
            },
            None => { 
                /*self.insert(addr32, (value as u32) << (8 * (3 - addr % 4)));*/
                panic!("HashMap<usize, u32>::set_8(0x{:x}, {})", addr, value)
            }
        }
    }
    
    fn allocate_at(&mut self, start:usize, size:usize) -> bool {
        let mut norm_start = start - (start % 4);
        let mut i = 0;
        while i < size {
            if let None = self.get(&norm_start) {
                self.insert(norm_start, 0);
            }
            i += 4;
            norm_start = norm_start.wrapping_add(4);
        }
        true
    }
}

impl Memory for BTreeMap<usize, [u8;4096] > {
    fn get_8(&self, addr:usize) -> u8 {
        let chunk_id = addr / 4096;
        let byte_offset = addr % 4096;
        if let Some(chunk) = self.get(&chunk_id) {
            chunk[byte_offset]
        } else {
            panic!("BTreeMap<usize, [u8;4096]>::get_8(0x{:x})", addr)
        }
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        let chunk_id = addr / 4096;
        let byte_offset = addr % 4096;
        if let Some(chunk) = self.get_mut(&chunk_id) {
            chunk[byte_offset] = value;
        } else {
            panic!("BTreeMap<usize, [u8;4096]>::set_8(0x{:x}, {})", addr, value)
        }
    }

    fn allocate_at(&mut self, start:usize, size:usize) -> bool {
        let mut allocated : isize = - ((start % 4096) as isize);
        let mut current_id = start / 4096;
        while allocated < (size as isize) {
            //println!("allocate from {:x} to {:x}",
            //    current_id << 12, (current_id+1) << 12);
            if !self.contains_key(&current_id) {
                self.insert(current_id, [0;4096]);
            }

            current_id = (current_id + 1) % (std::usize::MAX / 4096);
            allocated += 4096
        }

        true
    }
}

