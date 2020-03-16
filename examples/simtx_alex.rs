extern crate elf as elflib;
extern crate riscv_sandbox;
#[macro_use]
extern crate clap;

use clap::Values;

use riscv_sandbox::elf;
use riscv_sandbox::machine::{MultiCoreIMachine, simtx::Machine as SIMTX
    , simtx::scheduler::{LexicoScheduler, TimeShareScheduler}};
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
        (about: "SIMT-X simulator for rv32imc ISA")
        (@arg TPW: +required +takes_value {is_usize} "Number of threads per warps")
        (@arg NBW: +required +takes_value {is_usize} "Number of warps")
        (@arg monitored: -m --monitor [pc]... "Provide a list of pc to parse (e.g. 102a3f)")
        (@arg memdump: -d --dump [memory_range]... "Provide a list of memory range to dump (e.g. 0-3ff)")
        (@arg stacksize: -s --stack [size] "Sets the stack size of each thread")
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
    let exec_path = args.next().expect("You need to give an executable");
    let file = elflib::File::open_path(&exec_path)
        .expect("ELF file not found");

    let calls = elf::get_plt_symbols(&file)
        .unwrap_or(HashMap::new());
    let pc = elf::get_main_pc(&file)
        .expect("This ELF file has no function named 'main'");

    // number of threads
    let nb_th = tpw * nb_warps;

    // create some memory buffer to load instructions and rodata
    let memory = Arc::new(Mutex::new(BTreeMap::new()));
    let stacksize = conf.value_of("stacksize")
        .and_then(|v| v.parse().ok()).unwrap_or(0x00200000);//0x800
    let stackstart;
    let stackend;

    // Memory initialization
    {
        let mut memory = memory.lock().unwrap();
        let (pbeg, pend) = elf::load_program(&file, memory.deref_mut()).unwrap();

        stackend = pend;
        stackstart = stackend + nb_th * stacksize;
        println!("[SIM] Program sits on memory range {:x}-{:x} ({} bytes).", pbeg, pend, pend - pbeg);
        println!("[SIM] Stack bottom sits at {:x}", stackstart);

        memory.allocate_at(stackend, 32 * stacksize);

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
    let mut machine : SIMTX<TimeShareScheduler> = SIMTX::new(tpw, nb_warps, calls);
    machine.place_stack(stackend, stacksize);

    println!("[SIM] Setting pc to 0x{:x}", pc as usize);


    // Setup C specific argc/argv
    let mut argc = 1;
    let mut argv = vec![exec_path.clone()];
    {
        let mut memory = memory.lock().unwrap();
        while let Some(s) = args.next() {
            argv.push(s);
            argc += 1;
        }

        let mut first_ptr = 0x100;
        let mut ptrs = vec![first_ptr];
        let mut argvdata = String::new();
        for v in argv {
            ptrs.push(first_ptr);
            first_ptr += v.len() + 1;
            argvdata += &(String::from(v) + "\0");
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

        // Allocation for Alexandre's programs memory
        memory.allocate_at(0x10010000, 2048*4*2);
        memory.allocate_at(0x20000000, 0x100000);
    }

    // Setup SP/PC/argc/argv register for all cores
    for _i in 0..nb_th {
        let c = machine.pop_first_idle();
        machine.set_pc_of(c, pc);
        println!("[SIM] Setting sp of core {} to 0x{:08x}", c, (stackstart - c * stacksize) as i32);
        machine.set_i_register_of(c, 1, 0);    // must be 0
        machine.set_i_register_of(c, 2, (stackstart - c * stacksize) as i32); // sp
        machine.set_i_register_of(c, 3, 0x1206c + 1940);
        machine.set_i_register_of(c, 10, argc); // argc
        machine.set_i_register_of(c, 11, 0x14); // argv
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

//    for (key, chunk) in memory.iter() {
//      let mut k = *key;
//      for v in chunk.iter() {
//          println!("{} {}", k, v);
//          k = k.wrapping_add(4)
//      }

    for pc in monitored_pc {
        machine.print_stats_for_pc(usize::from_str_radix(pc.into(), 16).unwrap());
    }
machine.print_branch_stats();
    for range in conf.values_of("memdump").unwrap_or(Values::default()) {
        let mut iter = range.split("-").take(2);
        let beg = usize::from_str_radix(iter.next().unwrap(), 16).unwrap();
        let end = usize::from_str_radix(iter.next().unwrap(), 16).unwrap();

        for i in (beg..end).step_by(4) {
            println!("{:08x}: 0x{:08x}", i, memory.lock().unwrap().get_32(i));
        }
    }

    println!("[SIM] program ended in {} cycles with value {}", i, machine.get_i_register_of(0, 10));
}
