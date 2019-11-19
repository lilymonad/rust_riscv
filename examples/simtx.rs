extern crate elf as elflib;
extern crate riscv_sandbox;

use riscv_sandbox::elf;
use riscv_sandbox::machine::{IntegerMachine, simtx::Machine as SIMTX};
use riscv_sandbox::memory::Memory;

use std::collections::{HashMap, BTreeMap};
use std::env;

fn main() {

    let mut args = env::args(); args.next();

    // get threads per warp arg
    let tpw : usize = args.next().and_then(|s| s.parse().ok())
        .expect("You need to provide the number of threads per warp");

    // get number of warps arg
    let nb_warps : usize = args.next().and_then(|s| s.parse().ok())
        .expect("You need to provide the number of warps");

    // get exec path and parse executable file
    let exec_path = args.next().expect("You need to give an executable");
    let file = elflib::File::open_path(&exec_path)
        .expect("ELF file not found");

    let calls = elf::get_plt_symbols(&file)
        .expect("No .plt section in the ELF");
    let pc = elf::get_main_pc(&file)
        .expect("This ELF file has no function named 'main'");

    // create some memory buffer to load instructions and rodata
    let mut memory = BTreeMap::new();
    assert!(elf::load_instructions(&file, &mut memory)
            , "This ELF file has no .text section");

    if !elf::load_rodata(&file, &mut memory) {
            println!("This ELF file has no .rodata section");
    }

    // create the machine and set it up
    let mut machine = SIMTX::new(tpw, nb_warps, calls);
    println!("setting pc to 0x{:x}", pc as usize);
    machine.set_pc(pc);
    machine.set_i_register(1, 0);
    let mut i = 0;

    let nbth = tpw * nb_warps;
    //memory.allocate_at((-1024 * (nbth as i32)) as usize, 1024 * nbth);
    memory.allocate_at((-1024i32) as usize, 1024);

    // execute the program until its end
    loop {
        machine.cycle(&mut memory);
        i += 1;

        if machine.finished() {
            break;
        }
    }

    for (key, chunk) in memory.iter() {
        let mut k = *key;
        for v in chunk.iter() {
            println!("{} {}", k, v);
            k = k.wrapping_add(4)
        }
    }
    machine.print_stats();
    println!("[SIM] program ended in {} cycles with value {}", i, machine.get_i_register(10));
}
