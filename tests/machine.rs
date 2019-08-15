extern crate riscv_sandbox;

use riscv_sandbox::memory::Memory;
use riscv_sandbox::machine;
use riscv_sandbox::isa::{Instruction, OpCode};

#[test]
fn registers() {
    let mut mem : Vec<u8> = Vec::new();
    let mut proc = machine::RV32IMachine::new(Box::new(mem));

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
fn execute_addi() {
    let mut memory : Vec<u32> = vec![0,0,0,0,0,0,0,0];
    let add = Instruction::create_i(OpCode::OPIMM as u8, 1, 1, 0x7FF, 0);

    memory.set_32(0, add.0);

    let mut machine = machine::RV32IMachine::new(Box::new(memory));

    // perform a whole instruction cycle
    machine.cycle(); // fetch
    machine.cycle(); // decode
    machine.cycle(); // exec
    machine.cycle(); // mem
    machine.cycle(); // writeback

    assert_eq!(machine.get_register(1), 0x7FF);
}

#[test]
fn simple_math() {
    let mut memory : Vec<u32> = Vec::new();

    // load32 0x79ABCDEE r1
    memory.push(Instruction::create_u(OpCode::LUI as u8, 1, 0x79ABC000).0);
    memory.push(Instruction::create_i(OpCode::OPIMM as u8, 1, 1, 0x6F7, 0).0);
    memory.push(Instruction::create_i(OpCode::OPIMM as u8, 1, 1, 0x6F7, 0).0);

    // srli r2 r1 1 ; r2 = 0x3CD5E6F7
    memory.push(Instruction::create_i(OpCode::OPIMM as u8, 2, 1, 1, 0b101).0);

    // slli r2 r2 2 ; r2 = 0xF3579BDC
    memory.push(Instruction::create_i(OpCode::OPIMM as u8, 2, 2, 2, 0b001).0);

    // srai r2 r2 1 ; r2 = 0xF9ABCDEE
    memory.push(Instruction::create_i(OpCode::OPIMM as u8, 2, 2, 0x601, 0b101).0);

    // add r2 r1 r2 ; r2 = 0x73579BDC
    memory.push(Instruction::create_r(OpCode::OPREG as u8, 2, 1, 2, 0).0);

    // sub r1 r1 r2 ; r1 = 0x06543212
    memory.push(Instruction::create_r(OpCode::OPREG as u8, 1, 1, 2, 0x100).0);

    memory.push(0);
    memory.push(0);
    memory.push(0);
    memory.push(0);
    memory.push(0);

    let mut machine = machine::RV32IMachine::new(Box::new(memory));

    // start + lui
    machine.cycle();
    machine.cycle();
    machine.cycle();
    machine.cycle();
    assert_eq!(machine.get_register(1), 0x79ABC000);
    machine.cycle(); // addi 1
    machine.cycle(); // addi 2
    assert_eq!(machine.get_register(1), 0x79ABCDEE);
    machine.cycle(); // srli
    assert_eq!(machine.get_register(2), 0x3CD5E6F7);
    machine.cycle(); // slli
    assert_eq!(machine.get_register(2), 0xF3579BDC);
    machine.cycle(); // srai
    assert_eq!(machine.get_register(2), 0xF9ABCDEE);
    machine.cycle(); // add
    assert_eq!(machine.get_register(2), 0x73579BDC);
    machine.cycle(); // sub
    assert_eq!(machine.get_register(1), 0x06543212);
}

#[test]
fn simple_logic1() {
}
