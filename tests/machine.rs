extern crate elf as elflib;
extern crate riscv_sandbox;

use riscv_sandbox::memory::Memory;
use riscv_sandbox::machine::{rv32imc::Machine as RV32I
    //, rv32pthread::Machine as RV32Threaded
    , simtx::Machine as SIMTX
    , *};
use riscv_sandbox::isa::{Instruction, OpCode};
use riscv_sandbox::elf;

use std::collections::{HashMap, BTreeMap};

use std::fs::{self, *};
use std::io::{BufReader, BufRead};

#[test]
fn registers() {
    let mut proc = RV32I::new();

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

    memory.set_32(0, add.be());

    let mut machine = RV32I::new();

    // perform a whole instruction cycle
    machine.cycle(&mut memory); // fetch
    machine.cycle(&mut memory); // decode
    machine.cycle(&mut memory); // exec
    machine.cycle(&mut memory); // mem
    machine.cycle(&mut memory); // writeback

    assert_eq!(machine.get_register(1), 0x7FF);
}

#[test]
fn simple_math() {
    let mut memory : Vec<u32> = Vec::new();

    // load32 0x79ABCDEE r1
    memory.push(Instruction::create_u(OpCode::LUI, 1, 0x79ABC000u32 as i32).le());
    memory.push(Instruction::create_i(OpCode::OPIMM, 1, 1, 0x6F7, 0).le());
    memory.push(Instruction::create_i(OpCode::OPIMM, 1, 1, 0x6F7, 0).le());

    // srli r2 r1 1 ; r2 = 0x3CD5E6F7
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 1, 1, 0b101).le());

    // slli r2 r2 2 ; r2 = 0xF3579BDC
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 2, 2, 0b001).le());

    // srai r2 r2 1 ; r2 = 0xF9ABCDEE
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 2, 0x601, 0b101).le());

    // add r2 r1 r2 ; r2 = 0x73579BDC
    memory.push(Instruction::create_r(OpCode::OPREG, 2, 1, 2, 0).le());

    // sub r1 r1 r2 ; r1 = 0x06543212
    memory.push(Instruction::create_r(OpCode::OPREG, 1, 1, 2, 0x100).le());

    memory.push(0);
    memory.push(0);
    memory.push(0);
    memory.push(0);
    memory.push(0);

    let mut machine = RV32I::new();

    // start + lui
    machine.cycle(&mut memory);
    machine.cycle(&mut memory);
    machine.cycle(&mut memory);
    machine.cycle(&mut memory);
    assert_eq!(machine.get_register(1), 0x79ABC000u32 as i32);
    machine.cycle(&mut memory); // addi 1
    machine.cycle(&mut memory); // addi 2
    assert_eq!(machine.get_register(1), 0x79ABCDEEu32 as i32);
    machine.cycle(&mut memory); // srli
    assert_eq!(machine.get_register(2), 0x3CD5E6F7u32 as i32);
    machine.cycle(&mut memory); // slli
    assert_eq!(machine.get_register(2), 0xF3579BDCu32 as i32);
    machine.cycle(&mut memory); // srai
    assert_eq!(machine.get_register(2), 0xF9ABCDEEu32 as i32);
    machine.cycle(&mut memory); // add
    assert_eq!(machine.get_register(2), 0x73579BDCu32 as i32);
    machine.cycle(&mut memory); // sub
    assert_eq!(machine.get_register(1), 0x06543212u32 as i32);
}

#[test]
fn fibonacci() {
    let mut memory : Vec<u32> = Vec::new();
    let nop = Instruction::create_i(OpCode::OPIMM, 0, 0, 0, 0).le();
    // init logic registers (r1 - r3)
    memory.push(Instruction::create_i(OpCode::OPIMM, 1, 0, 0, 0).le()); // 0
    memory.push(Instruction::create_i(OpCode::OPIMM, 2, 0, 1, 0).le()); // 4

    // r4 = loop trip count
    memory.push(Instruction::create_i(OpCode::OPIMM, 4, 0, 0, 0).le()); // 8
    // r5 = which term we want
    memory.push(Instruction::create_i(OpCode::OPIMM, 5, 0, 5, 0).le()); // 12


    // the code
    memory.push(Instruction::create_b(OpCode::BRANCH, 4, 5, 32, 0).le()); // 16
    memory.push(nop); // 20
    memory.push(nop); // 24
    memory.push(Instruction::create_r(OpCode::OPREG, 3, 1, 2, 0).le()); // 28
    memory.push(Instruction::create_r(OpCode::OPREG, 1, 0, 2, 0).le()); // 32
    memory.push(Instruction::create_r(OpCode::OPREG, 2, 0, 3, 0).le()); // 36
    memory.push(Instruction::create_i(OpCode::OPIMM, 4, 4, 1, 0).le()); // 40
    memory.push(Instruction::create_j(OpCode::JAL, 0, -28).le()); // 44
    memory.push(nop); // 48
    memory.push(nop); // 52
    memory.push(nop); // 56
    memory.push(nop); // 60
    memory.push(nop); // 64

    let mut machine = RV32I::new();

    while machine.get_pc() != 64 {
        machine.cycle(&mut memory);
    }

    assert_eq!(machine.get_register(1), 5);
    assert_eq!(machine.get_register(2), 8);
    assert_eq!(machine.get_register(3), 8);
    assert_eq!(machine.get_register(4), 5);
}

#[test]
fn real_world_tests_simtx() {
    let ex_dir = "resources/executables/";
    let res_dir = "resources/memory_snapshots/simtx/";
    let executables = fs::read_dir(ex_dir)
        .expect("Cannot read 'resources/executables' directory")
        .map(|entry| entry.map(|e| e.file_name()
                                         .into_string())
                          .expect("Entry doesn't exist")
                          .expect("Bad entry name format"));

    for exec_path in executables {
        let file = elflib::File::open_path(String::from(ex_dir) + &exec_path)
            .expect("ELF file not found");

        let calls = elf::get_plt_symbols(&file)
            .expect("No .plt section in the ELF");
        let pc = elf::get_main_pc(&file)
            .expect("This ELF file has no function named 'main'");

        // create some memory buffer to load instructions and rodata
        let mut memory= BTreeMap::new();
        assert!(elf::load_instructions(&file, &mut memory)
                , "This ELF file has no .text section");

        if !elf::load_rodata(&file, &mut memory) {
                println!("This ELF file has no .rodata section");
        }

        // create the machine and set it up
        let mut machine = SIMTX::new(4, 4, calls);
        println!("setting pc to 0x{:x}", pc as usize);
        machine.set_pc(pc);
        machine.set_i_register(1, 0);

        //memory.allocate_at((-1024*4*4) as usize, 1024 * 4 * 4);
        memory.allocate_at((-1024i32) as usize, 1024);

        // execute the program until its end
        loop {
            machine.cycle(&mut memory);

            if machine.finished() {
                break;
            }
        }

        let snapshot = File::open(String::from(res_dir) + &exec_path)
            .expect("Snapshot file not found");
        let buffer = BufReader::new(&snapshot);
        for line in buffer.lines() {
            if let Ok(l) = line {
                let mut linebuf = l.split_ascii_whitespace();
                let key : usize = linebuf.next().and_then(|s| s.parse().ok())
                    .expect("Snapshot bad format");
                let value : u32 = linebuf.next().and_then(|s| s.parse().ok())
                    .expect("Snapshot bad format");

                assert_eq!(memory.get_32(key), value.to_be());
            }
        }
    }
}
