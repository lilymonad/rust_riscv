use std::ops::*;

pub trait MachineInteger
: Sized +
  Copy +
  Clone +
  PartialEq +
  Eq +
  Shr<u32,Output=Self> + // MI >> u32
  Shl<u32,Output=Self> + // MI << u32
  BitAnd<Output=Self> +  // MI & MI
  BitOr<Output=Self> +   // MI | MI
  From<i32>
{
    const XLEN : u32;
    fn bit_slice(&self, i:usize, j:usize) -> Self;

    fn slice_mask(a:usize, b:usize) -> Self {
        let all_ones = Self::all_set();
        all_ones.bit_slice(a, b) << (b as u32)
    }

    fn all_set() -> Self;
    fn zero() -> Self { Self::from(0) }
}

impl MachineInteger for i32 {
    const XLEN : u32 = 32;
    fn bit_slice(&self, i:usize, j:usize) -> i32 {
        (self >> j) & ((1 << (i-j)) - 1)
    }

    fn all_set() -> Self { -1 }
}

impl MachineInteger for i64 {
    const XLEN : u32 = 64;
    fn bit_slice(&self, i:usize, j:usize) -> i64 {
        (self >> j) & ((1 << (i-j)) - 1)
    }

    fn all_set() -> Self { -1 }
}
impl MachineInteger for i128 {
    const XLEN : u32 = 128;
    fn bit_slice(&self, i:usize, j:usize) -> i128 {
        (self >> j) & ((1 << (i-j)) - 1)
    }

    fn all_set() -> Self { -1 }
}

pub trait MachineFloat
: Sized +
  Copy +
  Clone +
  PartialEq +
  From<f32>
{
    const FLEN : u32;
}

impl MachineFloat for f32 {
    const FLEN :u32 = 32;
}
impl MachineFloat for f64 {
    const FLEN : u32 = 64;
}

pub trait BitSet {
    const SIZE : u32;
    fn set(&mut self, id:usize);
    fn unset(&mut self, id:usize);
    fn at(&self, id:usize) -> bool;
    fn singleton(id:usize) -> Self;
    fn any(&self) -> bool;
    fn none(&self) -> bool;
}

impl BitSet for u32 {
    const SIZE : u32 = 32;
    fn set(&mut self, id:usize) { *self |= 1 << id }
    fn unset(&mut self, id:usize) { *self &= !(1 << id) }
    fn at(&self, id:usize) -> bool { (*self & (1 << id)) != 0 }
    fn singleton(id:usize) -> Self { 1 << id }
    fn any(&self) -> bool { *self != 0 }
    fn none(&self) -> bool { *self == 0 }
}
impl BitSet for u64 {
    const SIZE : u32 = 64;
    fn set(&mut self, id:usize) { *self |= 1 << id }
    fn unset(&mut self, id:usize) { *self &= !(1 << id) }
    fn at(&self, id:usize) -> bool { (*self & (1 << id)) != 0 }
    fn singleton(id:usize) -> Self { 1 << id }
    fn any(&self) -> bool { *self != 0 }
    fn none(&self) -> bool { *self == 0 }
}
impl BitSet for u128 {
    const SIZE : u32 = 128;
    fn set(&mut self, id:usize) { *self |= 1 << id }
    fn unset(&mut self, id:usize) { *self &= !(1 << id) }
    fn at(&self, id:usize) -> bool { (*self & (1 << id)) != 0 }
    fn singleton(id:usize) -> Self { 1 << id }
    fn any(&self) -> bool { *self != 0 }
    fn none(&self) -> bool { *self == 0 }
}
