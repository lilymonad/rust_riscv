extern crate elf as elflib;
extern crate riscv_sandbox;

use riscv_sandbox::elf;
use riscv_sandbox::machine::{IntegerMachine, MultiCoreIMachine, rv32pthread::Machine};
use riscv_sandbox::memory::Memory;
use std::collections::{HashMap, BTreeMap};
use std::env;
use std::sync::{Arc, Mutex};

fn main() {

    let mut args = env::args(); args.next();

    // get exec path and parse executable file
    let exec_path = args.next().expect("You need to give an executable");
    let file = elflib::File::open_path(&exec_path)
        .expect("ELF file not found");

    let calls = elf::get_plt_symbols(&file)
        .or(Some(HashMap::new()))
        .expect("No .plt section in the ELF");
    let pc = elf::get_main_pc(&file)
        .expect("This ELF file has no function named 'main'");

    // create some memory buffer to load instructions and rodata
    let mut memory : BTreeMap<usize, [u8;4096]> = BTreeMap::new();
    assert!(elf::load_instructions(&file, &mut memory).is_some()
            , "This ELF file has no .text section");

    if !elf::load_rodata(&file, &mut memory).is_some() {
            println!("This ELF file has no .rodata section");
    }

    memory.allocate_at((-1024i32) as usize, 1024);

    // create the machine and set it up
    let mut machine = Machine::new(calls);
    println!("setting pc to 0x{:x}", pc as usize);
    machine.set_pc(pc);
    machine.set_i_register(1, 0);
    let mut i = 0;

    let mem = Arc::new(Mutex::new(memory));

    // execute the program until its end
    loop {
        machine.step(mem.clone());
        //machine.cycle(&mut memory);
        i += 1;

        if IntegerMachine::finished(&machine) {
            break;
        }
    }

    println!("[SIM] program ended in {} cycles with value {}", i, machine.get_i_register(10))
}
