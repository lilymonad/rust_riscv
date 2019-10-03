extern crate elf as elflib;
extern crate riscv_sandbox;

use riscv_sandbox::elf::load_instructions;
use riscv_sandbox::machine::{IntegerMachine, rv32pthread::Machine};
use riscv_sandbox::memory::Memory;
use riscv_sandbox::isa::Instruction;

use std::cell::RefCell;
use std::rc::Rc;
use std::path::PathBuf;
use std::collections::HashMap;

fn main() {
    let path = PathBuf::from("resources/threaded2");
    let file = elflib::File::open_path(&path)
        .expect("ELF file not found");

    let symtab = file.get_section(".symtab")
        .expect("ELF file has no .symtab section");

    let symbols = file.get_symbols(symtab)
        .expect("Error while reading .symtab");

    let rodata = file.get_section(".rodata")
        .expect("ELF file has no .rodata section");

    let plt = file.get_section(".plt")
        .expect("ELF file has no .plt section");

    let mut calls : HashMap<i32, String> = HashMap::new();
    let mut pc = 0;
    for sym in symbols {
        if sym.name == "main" {
            pc = sym.value as i32
        } else if sym.value >= plt.shdr.addr && sym.value < plt.shdr.addr + plt.shdr.size {
            println!("{} is between {:x} and {:x}", sym.name, plt.shdr.addr, plt.shdr.addr+plt.shdr.size);
            calls.insert(sym.value as i32, sym.name);
        }
    }

    let mut code : HashMap<usize, u32> = HashMap::new();
    load_instructions(&file, &mut code);
    for i in 0..128 {
        code.insert(i, 0);
    }

    let mut rodata_i = rodata.shdr.addr as usize;
    for byte in &rodata.data {
        code.set_8(rodata_i, *byte);
        rodata_i += 1
    }

    let mut machine = Machine::new(Rc::new(RefCell::new(code)), calls);
    println!("setting pc to 0x{:x}", pc as usize);
    machine.set_pc(pc);
    machine.set_i_register(1, 0);
    let mut i = 0;
    //for i in 0..500 {
    loop {
        machine.cycle();
        i += 1;

        if i > 5 && machine.get_i_register(2) == 0 {
            break;
        }
    }

    println!("[SIM] program ended with value {}", machine.get_i_register(10))
}
