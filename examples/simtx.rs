extern crate elf as elflib;
extern crate riscv_sandbox;

use riscv_sandbox::elf;
use riscv_sandbox::machine::{MultiCoreIMachine, simtx::Machine as SIMTX};
use riscv_sandbox::memory::Memory;

use std::collections::{HashMap, BTreeMap};
use std::env;
use std::sync::{Arc, Mutex};
use std::ops::DerefMut;

fn main() {

    let mut args = env::args(); args.next();

    // get threads per warp arg
    let tpw : usize = args.next().and_then(|s| s.parse().ok())
        .expect("You need to provide the number of threads per warp");

    // get number of warps arg
    let nb_warps : usize = args.next().and_then(|s| s.parse().ok())
        .expect("You need to provide the number of warps");

    let monitored_pc : Option<usize> = args.next().and_then(|s| { s.parse().ok() }).map(|v| {
        if v == 0 { None } else { Some(v) }
    }).expect("You need to provide a pc to monitor (0 to monitor all)");

    // get exec path and parse executable file
    let exec_path = args.next().expect("You need to give an executable");
    let file = elflib::File::open_path(&exec_path)
        .expect("ELF file not found");

    let calls = elf::get_plt_symbols(&file)
        .expect("No .plt section in the ELF");
    let pc = elf::get_main_pc(&file)
        .expect("This ELF file has no function named 'main'");

    // create some memory buffer to load instructions and rodata
    let memory = Arc::new(Mutex::new(BTreeMap::new()));
    let stacksize = 0x00200000;
    let stackstart = 0x0ff00000;
    let stackend = stackstart - stacksize;
    {
        let mut memory = memory.lock().unwrap();
        elf::load_program(&file, memory.deref_mut());
//        assert!(elf::load_instructions(&file, memory.deref_mut())
//                , "This ELF file has no .text section");
//
//        if !elf::load_rodata(&file, memory.deref_mut()) {
//                println!("This ELF file has no .rodata section");
//        }

        memory.allocate_at(stackend, stacksize);

//        if !elf::load_section(&file, ".bss", memory.deref_mut()) {
//            println!("This ELF file has no .bss section");
//        }

        if let Some(addr) = elf::get_symbol_address(&file, "stderr") {
            println!("Found stderr at {:x}, writing 2 at this address", addr);
            memory.set_32(addr as usize, 2);
        }
        if let Some(addr) = elf::get_symbol_address(&file, "stdout") {
            println!("Found stdout at {:x}, writing 2 at this address", addr);
            memory.set_32(addr as usize, 0);
        }
    }

    // create the machine and set it up
    let mut machine = SIMTX::new(tpw, nb_warps, calls);
    println!("setting pc to 0x{:x}", pc as usize);
    machine.set_pc_of(0, pc);
    machine.set_i_register_of(0, 1, 0);
    println!("Setting sp to 0x{:08x}", stackstart as i32 - 1);
    machine.set_i_register_of(0, 2, stackstart as i32 - 1);
    machine.set_i_register_of(0, 3, 0x1206c + 1940);

    {
        let mut memory = memory.lock().unwrap();
        let mut argc = 1;
        let mut argv = vec![exec_path.clone()];
        while let Some(s) = args.next() {
            argv.push(s);
            argc += 1;
        }

        machine.set_i_register_of(0, 10, argc);

        let mut first_ptr = 0x100;
        let mut ptrs = vec![first_ptr];
        let mut argvdata = String::new();
        for v in argv {
            ptrs.push(first_ptr);
            first_ptr += v.len() + 1;
            argvdata += &(v + "\0");
        }

        memory.allocate_at(0, 4096);
        let mut i = 0x100;
        for c in argvdata.bytes() {
            memory.set_8(i, c as u8);
            i += 1;
        }
        i = 0x10;
        for ptr in &ptrs {
            memory.set_32(i, *ptr as u32);
            i += 4;
        }
        machine.set_i_register_of(0, 11, 0x14);
    }

    let mut i = 0;

    // execute the program until its end
    loop {
        machine.step(memory.clone());
        i += 1;

        if machine.finished() {
            break;
        }
    }

    /*for (key, chunk) in memory.iter() {
        let mut k = *key;
        for v in chunk.iter() {
            println!("{} {}", k, v);
            k = k.wrapping_add(4)
        }
    }*/
    if let Some(pc) = monitored_pc {
        machine.print_stats_for_pc(pc);
    } else {
        machine.print_stats();
    }
    println!("[SIM] program ended in {} cycles with value {}", i, machine.get_i_register_of(0, 10));
}
