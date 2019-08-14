extern crate riscv_sandbox;

use riscv_sandbox::memory::Memory;
use riscv_sandbox::machine;
use riscv_sandbox::isa::{Instruction, OpCode};

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
    let add = Instruction::create_i(OpCode::OPIMM as u8, 1, 1, 1023, 0);

    memory.set_32(0, add.0 as u32);

    let mut machine = machine::RV32IMachine::new(Box::new(memory));

    // perform a whole instruction cycle
    machine.cycle(); // fetch
    machine.cycle(); // decode
    machine.cycle(); // exec
    machine.cycle(); // mem
    machine.cycle(); // writeback

    assert_eq!(machine.get_register(1), 1023);
}
