extern crate riscv;

use riscv::memory::Memory;
use riscv::isa::{self, Instruction};

#[test]
fn instruction_insertion() {
    let i = Instruction::create_i(isa::OpCode::OPIMM as u8, 1, 1, 128, 0);
    let mut mem = vec![0, 0, 0, 0];

    mem.set_32(0, i.0);
    assert_eq!(mem.get_32(0), i.0);
}
