extern crate riscv_sandbox;

use riscv_sandbox::memory::Memory;
use riscv_sandbox::machine::{self, rv32i::Machine as RV32I, rv32pthread::Machine as RV32Quad, *};
use riscv_sandbox::isa::{Instruction, OpCode};

use std::rc::Rc;
use std::cell::RefCell;

#[test]
fn registers() {
    let mut mem : Vec<u8> = Vec::new();
    let mut proc = RV32I::new(Rc::new(RefCell::new(mem)));

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
    let add = Instruction::create_i(OpCode::OPIMM, 1, 1, 0x7FF, 0);

    memory.set_32(0, add.0);

    let mut machine = RV32I::new(Rc::new(RefCell::new(memory)));

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
    memory.push(Instruction::create_u(OpCode::LUI, 1, 0x79ABC000u32 as i32).0);
    memory.push(Instruction::create_i(OpCode::OPIMM, 1, 1, 0x6F7, 0).0);
    memory.push(Instruction::create_i(OpCode::OPIMM, 1, 1, 0x6F7, 0).0);

    // srli r2 r1 1 ; r2 = 0x3CD5E6F7
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 1, 1, 0b101).0);

    // slli r2 r2 2 ; r2 = 0xF3579BDC
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 2, 2, 0b001).0);

    // srai r2 r2 1 ; r2 = 0xF9ABCDEE
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 2, 0x601, 0b101).0);

    // add r2 r1 r2 ; r2 = 0x73579BDC
    memory.push(Instruction::create_r(OpCode::OPREG, 2, 1, 2, 0).0);

    // sub r1 r1 r2 ; r1 = 0x06543212
    memory.push(Instruction::create_r(OpCode::OPREG, 1, 1, 2, 0x100).0);

    memory.push(0);
    memory.push(0);
    memory.push(0);
    memory.push(0);
    memory.push(0);

    let mut machine = RV32I::new(Rc::new(RefCell::new(memory)));

    // start + lui
    machine.cycle();
    machine.cycle();
    machine.cycle();
    machine.cycle();
    assert_eq!(machine.get_register(1), 0x79ABC000u32 as i32);
    machine.cycle(); // addi 1
    machine.cycle(); // addi 2
    assert_eq!(machine.get_register(1), 0x79ABCDEEu32 as i32);
    machine.cycle(); // srli
    assert_eq!(machine.get_register(2), 0x3CD5E6F7u32 as i32);
    machine.cycle(); // slli
    assert_eq!(machine.get_register(2), 0xF3579BDCu32 as i32);
    machine.cycle(); // srai
    assert_eq!(machine.get_register(2), 0xF9ABCDEEu32 as i32);
    machine.cycle(); // add
    assert_eq!(machine.get_register(2), 0x73579BDCu32 as i32);
    machine.cycle(); // sub
    assert_eq!(machine.get_register(1), 0x06543212u32 as i32);
}

#[test]
fn fibonacci() {
    let mut memory : Vec<u32> = Vec::new();
    let nop = Instruction::create_i(OpCode::OPIMM, 0, 0, 0, 0).0;
    // init logic registers (r1 - r3)
    memory.push(Instruction::create_i(OpCode::OPIMM, 1, 0, 0, 0).0); // 0
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 0, 1, 0).0); // 4

    // r4 = loop trip count
    memory.push(Instruction::create_i(OpCode::OPIMM, 4, 0, 0, 0).0); // 8
    // r5 = which term we want
    memory.push(Instruction::create_i(OpCode::OPIMM, 5, 0, 5, 0).0); // 12


    // the code
    memory.push(Instruction::create_b(OpCode::BRANCH, 4, 5, 32, 0).0); // 16
    memory.push(nop); // 20
    memory.push(nop); // 24
    memory.push(Instruction::create_r(OpCode::OPREG, 3, 1, 2, 0).0); // 28
    memory.push(Instruction::create_r(OpCode::OPREG, 1, 0, 2, 0).0); // 32
    memory.push(Instruction::create_r(OpCode::OPREG, 2, 0, 3, 0).0); // 36
    memory.push(Instruction::create_i(OpCode::OPIMM, 4, 4, 1, 0).0); // 40
    memory.push(Instruction::create_j(OpCode::JAL, 0, -28).0); // 44
    memory.push(nop); // 48
    memory.push(nop); // 52
    memory.push(nop); // 56
    memory.push(nop); // 60
    memory.push(nop); // 64

    let mut machine = RV32I::new(Rc::new(RefCell::new(memory)));

    while machine.get_pc() != 64 {
        machine.cycle();
    }

    assert_eq!(machine.get_register(1), 5);
    assert_eq!(machine.get_register(2), 8);
    assert_eq!(machine.get_register(3), 8);
    assert_eq!(machine.get_register(4), 5);
}
