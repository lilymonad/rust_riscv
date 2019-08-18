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
}

impl MachineInteger for i32 {
    const XLEN : u32 = 32;
}
impl MachineInteger for i64 {
    const XLEN : u32 = 64;
}
impl MachineInteger for i128 {
    const XLEN : u32 = 128;
}
