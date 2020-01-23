extern crate elf as elflib;
extern crate riscv_sandbox;
#[macro_use]
extern crate clap;

use clap::Values;

use riscv_sandbox::elf;
use riscv_sandbox::machine::{MultiCoreIMachine, simtx::Machine as SIMTX};
use riscv_sandbox::memory::Memory;

use std::collections::{HashMap, BTreeMap};
use std::env;
use std::sync::{Arc, Mutex};
use std::ops::DerefMut;

fn is_usize(s:String) -> Result<(), String> {
    s.parse::<usize>().map_err(|e| String::from("Must be a number")).map(|_| ())
}

fn main() {

    let conf = clap_app!(myapp =>
        (version: "1.0")
        (author: "Arthur Blanleuil")
        (about: "A simple example of clap usage")
        (@arg TPW: +required +takes_value {is_usize} "Sets the number of threads per warps")
        (@arg NBW: +required +takes_value {is_usize} "Sets the number of warps")
        (@arg monitored: -m --monitor [pc]... "Provide a list of pc to parse")
        (@arg command: * ... "The command to run")
    ).get_matches();

    let tpw : usize = conf.value_of("TPW").unwrap().parse()
        .expect("TPW must be a number");
    let nb_warps : usize = conf.value_of("NBW").unwrap().parse()
        .expect("NBW must be a number");

    let monitored_pc = conf.values_of("monitored")
        .or(Some(Values::default())).unwrap();

    let mut args = conf.values_of("command").unwrap();

    // get exec path and parse executable file
    let exec_path = args.next().unwrap();
    let file = elflib::File::open_path(&exec_path)
        .expect("[ERR] ELF file not found");

    let calls = elf::get_plt_symbols(&file)
        .unwrap_or(HashMap::new());
    let pc = elf::get_main_pc(&file)
        .expect("[ERR] This ELF file has no function named 'main'");

    let nb_th = tpw * nb_warps;

    // create some memory buffer to load instructions and rodata
    let memory = Arc::new(Mutex::new(BTreeMap::new()));
    let stacksize = 0x00200000;//0x800
    let stackstart;// = 0x0ff00000;
    let stackend;// = stackstart - stacksize;
    {
        let mut memory = memory.lock().unwrap();
        let (pbeg, pend) = elf::load_program(&file, memory.deref_mut()).unwrap();

        stackend = pend;
        stackstart = stackend + nb_th * stacksize;
        println!("[SIM] Program sits on memory range {:x}-{:x} ({} bytes).", pbeg, pend, pend - pbeg);
        println!("[SIM] Stack bottom sits at {:x}", stackstart);

        memory.allocate_at(stackstart - stacksize, stacksize);

        if let Some(addr) = elf::get_symbol_address(&file, "stderr") {
            println!("[SIM] Found stderr at {:x}, writing 2 at this address", addr);
            memory.set_32(addr as usize, 2);
        }
        if let Some(addr) = elf::get_symbol_address(&file, "stdout") {
            println!("[SIM] Found stdout at {:x}, writing 2 at this address", addr);
            memory.set_32(addr as usize, 0);
        }
    }

    // create the machine and set it up
    let mut machine = SIMTX::new(tpw, nb_warps, calls);
    println!("[SIM] Setting pc to 0x{:x}", pc as usize);

    {
        // Compute argc and argv
        let mut memory = memory.lock().unwrap();
        let mut argc = 1;
        let mut argv = vec![exec_path.clone()];
        while let Some(s) = args.next() {
            argv.push(s.into());
            argc += 1;
        }

        // compute argv byte per byte 
        let mut first_ptr = 0x100;
        let mut ptrs = vec![first_ptr];
        let mut argvdata = String::new();
        for v in argv {
            ptrs.push(first_ptr);
            first_ptr += v.len() + 1;
            argvdata += &(String::from(v) + "\0");
        }

        // allocate argv memory chunk
        // and store it at 0x10
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

        // setup core[0] registers
        let c = machine.pop_first_idle();
        machine.set_pc_of(c, pc);
        machine.set_i_register_of(c, 1, 0);
        machine.set_i_register_of(c, 2, stackstart as i32);
        machine.set_i_register_of(c, 3, 0x1206c + 1940);
        machine.set_i_register_of(c, 10, argc);
        machine.set_i_register_of(c, 11, 0x14);
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

    for pc in monitored_pc {
        machine.print_stats_for_pc(usize::from_str_radix(pc.into(), 16).unwrap());
    }

    println!("[SIM] program ended in {} cycles with value {}", i, machine.get_i_register_of(0, 10));
}
