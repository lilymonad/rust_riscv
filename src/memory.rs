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

    fn get_16(&self, addr:usize) -> u16 {
        let low = self.get_8(addr) as u16;
        let high = self.get_8(addr + 1) as u16;
        (high << 8) | low
    }

    fn get_32(&self, addr:usize) -> u32 {
        let low = self.get_16(addr) as u32;
        let high = self.get_16(addr + 2) as u32;
        (high << 16) | low
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        self[addr] = value
    }

    fn set_16(&mut self, addr:usize, value:u16) {
        self.set_8(addr, (value & 0xFF) as u8);
        self.set_8(addr + 1, ((value >> 8) & 0xFF) as u8)
    }

    fn set_32(&mut self, addr:usize, value:u32) {
        self.set_16(addr, (value & 0xFFFF) as u16);
        self.set_16(addr + 2, ((value >> 16) & 0xFFFF) as u16)
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
            || panic!("HashMap<usize, u32>::get_8"),
            
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
        let mut norm_start = start;
        let mut i = 0;
        while i < size {
            if let None = self.get(&norm_start) {
                println!("inserting 0x{:x}", norm_start);
                self.insert(norm_start, 0);
            }
            i += 4;
            norm_start = norm_start.wrapping_add(4);
        }
        true
    }
}

enum SearchRes {
    Fusion(usize, Vec<usize>),
    Fail,
}

fn overlap(aleft:usize,aright:usize,bleft:usize,bright:usize) -> bool {
    aleft <= bright && bleft <= aright
}

impl Memory for BTreeMap<usize, Vec<u32> > {
    fn get_8(&self, addr:usize) -> u8 {
        for (start, chunk) in self {
            let end = start.wrapping_add(chunk.len() * 4);
            if addr >= *start && (addr < end || end < *start) {
                return chunk.get_8(addr - start)
            }
        }

        panic!("BTreeMap<usize, Vec<u32>>::get_8(0x{:x})", addr)
    }

    fn set_8(&mut self, addr:usize, value:u8) {
        for (start, chunk) in self.iter_mut() {
            let end = start.wrapping_add(chunk.len() * 4);
            if addr >= *start && (addr < end || end < *start) {
                chunk.set_8(addr - start, value);
                return
            }
        }

        panic!("BTreeMap<usize, Vec<u32>>::set_8(0x{:x}, {})", addr, value)
    }

    fn allocate_at(&mut self, start:usize, size:usize) -> bool {

        // Check whether we are overflowing the `usize` range
        let start = start - (start % 4);
        let size = size + (start % 4);
        let (wrapped_end, overflow) = start.overflowing_add(size);
        let saturated_end = start.saturating_add(size);
        if overflow {
            return self.allocate_at(start, saturated_end - start)
                && self.allocate_at(0, wrapped_end)
        }

        let mut result = SearchRes::Fail;
        let mut iter = self.iter_mut();

        let mut iter_res = iter.next();
        // If we are not overflowing, we check it we are empty
        if let Some((chunk_addr, _)) = iter_res {
            // If even the first chunk is far after our new chunk
            // Just create an empty chunk
            if *chunk_addr > wrapped_end {
                let mut chunk = Vec::new();
                chunk.allocate_at(0, size);
                self.insert(start, chunk);
                return true
            }

            // we need to gather chunks which need to be fusionned
            let mut fusion_vec = Vec::new();
            let mut first_chunk_id = start;

            // try gathering chunks [0..]
            'search: while let Some((chunk_start, chunk)) = iter_res {
                let current_end = chunk_start.saturating_add(chunk.len() * 4);
                if overlap(*chunk_start, current_end, start, wrapped_end) {
                    println!("{:x}-{:x} and {:x}-{:x} overlap",start, wrapped_end, *chunk_start, current_end);
                    // when we have our first overlapping chunk, we test for
                    // which chunk comes first
                    if first_chunk_id > *chunk_start {
                        first_chunk_id = *chunk_start
                    } else {
                        fusion_vec.push(*chunk_start)
                    }

                    // if we overlap AND overflow, gather every other chunk
                    if wrapped_end > current_end {
                        while let Some((next_start, _)) = iter.next() {
                            if *next_start < wrapped_end {
                                fusion_vec.push(*next_start);
                            } else {
                                break
                            }
                        }

                        result = SearchRes::Fusion(first_chunk_id, fusion_vec);
                        break 'search
                    }
                }

                iter_res = iter.next();
            }

            // If we need to fusion, we need the first chunk to be fusionned
            // in order to have our first
            match result {
                SearchRes::Fusion(id1, ids) => {
                    if !self.contains_key(&id1) {
                        self.insert(id1, Vec::new());
                    }
                    for id2 in ids.iter() {
                        let chunk2 = self.get(&id2).unwrap().clone();
                        let chunk = self.get_mut(&id1).unwrap();
                        chunk.allocate_at(0, id2 - id1);
                        chunk.extend(chunk2.iter());
                        self.remove(&id2);
                    }
                    self.get_mut(&id1).unwrap().allocate_at(start - id1, size);
                },
                SearchRes::Fail => {
                    let mut chunk = Vec::with_capacity(size / 4 + 1);
                    chunk.allocate_at(0, size);
                    self.insert(start, chunk);
                },
            }
            return true           
        } else {
            // If we are empty, we just create the first chunk
            let mut chunk = Vec::new();
            chunk.allocate_at(0, size);
            self.insert(start, chunk);
            return true
        }
    }
}

