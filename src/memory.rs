use std::collections::HashMap;

/// Represents the main memory.
/// It can be implemented by any structure which can handle loads and stores.
///
/// Using a trait enables us to implement direct-mapped memory, RAM with MMU,
/// or any other kind of memory interface.
pub trait Memory {
    fn get_8(&self, addr:usize) -> u8;
    fn get_16(&self, addr:usize) -> u16;
    fn get_32(&self, addr:usize) -> u32;

    fn set_8(&mut self, addr:usize, value:u8);
    fn set_16(&mut self, addr:usize, value:u16);
    fn set_32(&mut self, addr:usize, value:u32);
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
}

/// Simple Memory implementation for u8 dynamic arrays (Vec<u8>)
impl Memory for Vec<u8> {
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
}

/// Simple Memory implementation for u32 dynamic arrays (Vec<u32>)
impl Memory for Vec<u32> {
    fn get_8(&self, addr:usize) -> u8 {
        (self[addr / 4] >> ((3 - addr % 4) * 8)) as u8
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
        let x = &mut self[addr / 4];
        *x = match addr % 4 {
            0 => (*x & 0x00FFFFFF) | ((value as u32) << 24),
            1 => (*x & 0xFF00FFFF) | ((value as u32) << 16),
            2 => (*x & 0xFFFF00FF) | ((value as u32) << 8),
            _ => (*x & 0xFFFFFF00) | (value as u32),
        }
    }

    fn set_16(&mut self, addr:usize, value:u16) {
        self.set_8(addr, (value & 0xff) as u8);
        self.set_8(addr + 1, ((value >> 8) & 0xff) as u8)
    }

    fn set_32(&mut self, addr:usize, value:u32) {
        self.set_16(addr, (value & 0xffff) as u16);
        self.set_16(addr + 2, ((value >> 16) & 0xffff) as u16)
    }
}

impl Memory for HashMap<usize, u32> {
    fn get_8(&self, addr:usize) -> u8 {
        let addr32 = addr / 4;
        self.get(&addr32).map_or(0, | x | {
            ((x >> (8 * (3 - addr % 4))) & 0xFF) as u8
        })
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
        let addr32 = addr / 4;
        match self.get_mut(&addr32) {
            Some(x) => {
                match addr % 4 {
                    0 => *x = (*x & 0x00FFFFFF) | ((value as u32) << 24),
                    1 => *x = (*x & 0xFF00FFFF) | ((value as u32) << 16),
                    2 => *x = (*x & 0xFFFF00FF) | ((value as u32) << 8),
                    _ => *x = (*x & 0xFFFFFF00) | ((value as u32) << 0),
                }
            },
            None => { self.insert(addr32, (value as u32) << (8 * (3 - addr % 4))); }
        }
    }

    fn set_16(&mut self, addr:usize, value:u16) {
        self.set_8(addr, (value & 0xff) as u8);
        self.set_8(addr + 1, ((value >> 8) & 0xff) as u8)
    }

    fn set_32(&mut self, addr:usize, value:u32) {
        self.set_16(addr, (value & 0xffff) as u16);
        self.set_16(addr + 2, ((value >> 16) & 0xffff) as u16)
    }
}
