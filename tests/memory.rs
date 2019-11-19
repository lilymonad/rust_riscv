extern crate riscv_sandbox;

use std::collections::{HashMap, BTreeMap};
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
    mem.allocate_at(0, 128);
    
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
fn is_little_endian_btree_chunk() {
    let mut mem : BTreeMap<usize, Vec<u32>> = BTreeMap::new();
    mem.allocate_at(0, 128);
    
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
fn memory_chunk_fusion() {
    let mut mem = BTreeMap::new();

    // chunk alone
    mem.allocate_at(0, 128);

    // close chunks
    mem.allocate_at(256, 128);
    mem.allocate_at(256 + 128 + 16, 128);
    mem.allocate_at(256 + 128 + 16 + 128 + 16, 128);

    // fusionning chunk
    mem.allocate_at(256 + 64, 128 + 16 + 128 + 16);

    // chunk alone
    mem.allocate_at(2048, 128);
    

    let mut it = mem.iter();

    let alone1 = it.next().unwrap();
    assert_eq!(*alone1.0, 0);
    assert_eq!(alone1.1.len() * 4, 128);

    let fusion = it.next().unwrap();
    assert_eq!(*fusion.0, 256);
    assert_eq!(fusion.1.len() * 4, 128 * 3 + 16 * 2);

    let alone2 = it.next().unwrap();
    assert_eq!(*alone2.0, 2048);
    assert_eq!(alone2.1.len() * 4, 128);

    assert_eq!(it.next(), None);
}
