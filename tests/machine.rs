extern crate riscv;

use riscv::machine;
use riscv::isa::{Instruction, OpCode};

#[test]
fn registers() {
    let mut proc = machine::RV32IMachine::new();

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
    let add = Instruction::i(OpCode::REGIMM, 1, 1, 1023, 0);
    let mut machine = machine::RV32IMachine::new(Box::new(&mut [0..1023]));

    machine.cycle();
}
