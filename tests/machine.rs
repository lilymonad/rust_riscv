extern crate riscv;

use riscv::memory::Memory;
use riscv::machine;
use riscv::isa::{Instruction, OpCode};

#[test]
fn registers() {
    let mut proc = machine::RV32IMachine::new(Box::new(vec![]));

    for i in 0..31 {
        assert_eq!(proc.get_register(i as usize), 0);
        proc.set_register(i as usize, i+1);
    }

    assert_eq!(proc.get_register(0), 0);
    for i in 1..31 {
        assert_eq!(proc.get_register(i as usize), i+1);
    }
}

#[test]
fn test_add() {
    let mut memory : Vec<u8> = vec![0,0,0,0];
    let add = Instruction::i(OpCode::OPIMM as u8, 1, 1, 1023, 0);

    memory.set_32(0, add.0 as u32);

    let mut machine = machine::RV32IMachine::new(Box::new(memory));

    machine.cycle();
    machine.cycle();
    machine.cycle();
    machine.cycle();
    machine.cycle();

    assert_eq!(machine.get_register(1), 1023);
}
