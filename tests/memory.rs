extern crate riscv_sandbox;

use std::collections::HashMap;
use riscv_sandbox::memory::Memory;
use riscv_sandbox::isa::{self, Instruction};

#[test]
fn vec_memory_impl() {
    let i = Instruction::create_i(isa::OpCode::OPIMM, 1, 1, 128, 0);
    let mut mem : Vec<u8> = vec![0, 0, 0, 0];

    mem.set_32(0, i.0);
    assert_eq!(mem.get_32(0), i.0)
}

#[test]
#[should_panic]
fn vec_memory_out_of_bound() {
    let mut mem : Vec<u8> = vec![0, 0, 0];
    mem.set_32(0, 128)
}

#[test]
fn is_little_endian_vec_u32() {
    let mut mem : Vec<u32> = Vec::new();
    mem.resize(2, 0);
    
    mem.set_32(0, 0x00112233);
    mem.set_32(4, 0x44556677);

    assert_eq!(mem.get_16(0), 0x2233);
    assert_eq!(mem.get_16(1), 0x1122);
    assert_eq!(mem.get_16(2), 0x0011);
    assert_eq!(mem.get_16(3), 0x7700);

    assert_eq!(mem.get_32(0), 0x00112233);
    assert_eq!(mem.get_32(1), 0x77001122);
    assert_eq!(mem.get_32(2), 0x66770011);
    assert_eq!(mem.get_32(3), 0x55667700);
}

#[test]
fn is_little_endian_vec_u8() {
    let mut mem : Vec<u8> = Vec::new();
    mem.resize(8, 0);
    
    mem.set_32(0, 0x00112233);
    mem.set_32(4, 0x44556677);

    assert_eq!(mem.get_16(0), 0x2233);
    assert_eq!(mem.get_16(1), 0x1122);
    assert_eq!(mem.get_16(2), 0x0011);
    assert_eq!(mem.get_16(3), 0x7700);

    assert_eq!(mem.get_32(0), 0x00112233);
    assert_eq!(mem.get_32(1), 0x77001122);
    assert_eq!(mem.get_32(2), 0x66770011);
    assert_eq!(mem.get_32(3), 0x55667700);
}

#[test]
fn is_little_endian_hashmap() {
    let mut mem : HashMap<usize, u32> = HashMap::new();
    
    mem.set_32(0, 0x00112233);
    mem.set_32(4, 0x44556677);

    assert_eq!(mem.get_16(0), 0x2233);
    assert_eq!(mem.get_16(1), 0x1122);
    assert_eq!(mem.get_16(2), 0x0011);
    assert_eq!(mem.get_16(3), 0x7700);

    assert_eq!(mem.get_32(0), 0x00112233);
    assert_eq!(mem.get_32(1), 0x77001122);
    assert_eq!(mem.get_32(2), 0x66770011);
    assert_eq!(mem.get_32(3), 0x55667700);
}
