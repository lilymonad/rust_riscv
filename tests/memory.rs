extern crate riscv_sandbox;

use riscv_sandbox::memory::Memory;
use riscv_sandbox::isa::{self, Instruction};

#[test]
fn vec_memory_impl() {
    let i = Instruction::create_i(isa::OpCode::OPIMM as u8, 1, 1, 128, 0);
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
