use machine::{MultiCoreIMachine, IntegerMachine};
use isa::{Instruction, OpCode, CsrField};
use memory::Memory;
use machine::rv32imc::{self, Machine as RV32I};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

pub struct Machine {
    cores : [ RV32I ; 4 ],
    joining : [ i32 ; 4 ],
    current_core : usize,
    //threads : Vec<ThreadData>,
    active_threads : usize,
    cycles : i32,
    plt_addresses : HashMap<i32, String>,
}

impl Machine {
    pub fn new(plt:HashMap<i32, String>) -> Machine {
        let mut ret = Machine {
            cores : [ RV32I::new(), RV32I::new()
                    , RV32I::new(), RV32I::new() ],
            joining : [ -1 ; 4 ],
            current_core : 0,
            active_threads : 1,
            cycles : 0,
            plt_addresses : plt,
        };

        let mut i = 0;
        for core in &mut ret.cores {
            core.set_csr_field(CsrField::HartID, i);
            i += 1;
        }

        ret
    }

    pub fn with_args(plt:HashMap<i32, String>,args:Vec<&str>,mem:&mut dyn Memory) -> Machine {
        let mut machine = Self::new(plt);
        let core = &mut machine.cores[0];

        core.set_i_register(10, args.len() as i32);
        core.set_i_register(11, -65536);
        
        let mut table_i = (-65536i32) as usize;
        let mut i = table_i + (4 * args.len());
        for arg in args {
            mem.set_32(table_i, i as u32);
            for byte in arg.bytes() {
                mem.set_8(i as usize, byte as u8);
                i += 1;
            }
            table_i += 4
        }

        machine
    }

    fn schedule_next_core(&mut self) {
        let mut i = (self.current_core + 1) % self.active_threads;
        let mut num = 0;
        while (self.joining[i] != -1 || self.cores[i].get_pc() == 0) && num < self.active_threads {
            i = (i + 1) % self.active_threads;
            num += 1
        }
        self.cycles = 0;
        self.current_core = i;
    }

    fn do_write_back(&mut self, core:usize) {
        self.cores[core].do_write_back()
    }

    fn do_mem(&mut self, core:usize, mem:&mut dyn Memory) {
        self.cores[core].do_mem(mem)
    }

    fn do_execute(&mut self, core:usize, mem:&mut dyn Memory) {
        let curr = core;
        let curr_pc = self.cores[curr].dc2ex.pc;
        let i = self.cores[curr].dc2ex.instruction;

        let (advance, i) = if i.is_compressed() {
            (2, i.uncompressed())
        } else {
            (4, i)
        };

        let address = curr_pc.wrapping_add(i.get_imm_j());

        println!("Core {}   0x{:x}: {}", core, curr_pc, i);
        if i.get_opcode() == OpCode::JAL.into() {
            //println!("jump addr = {:x}", address);
            if let Some(func_name) = self.plt_addresses.get(&address) {
                if func_name.contains("pthread_create") {
                    let i = self.active_threads as usize;
                    let npc = self.get_i_register_of(curr, 12);
                    self.active_threads += 1;
                    self.set_pc_of(i, npc);
                    self.set_i_register_of(i, 1, 0);

                    mem.allocate_at(((-1024i32) * (i+1) as i32) as usize, 1024);

                    self.set_i_register_of(i, 2, (-1024) * i as i32);
                    self.set_i_register_of(i, 8, (-1024) * i as i32);

                    mem.set_32(self.get_i_register_of(curr, 10) as usize, i as u32);
                    self.set_i_register_of(curr, 10, 0);
                    self.cores[curr].mem2wb = rv32imc::WriteBackData {
                        perform : false,
                        rd : 0,
                        value : 0,
                    };

                    //println!("[SIM] new thread on core {} at 0x{:x} (sp=s0={:x})", i, npc, (-1024) * i as i32)
                } else if func_name.contains("pthread_join") {
                    let to_wait = self.get_i_register_of(curr, 10);
                    self.joining[curr] = to_wait;
                    self.cores[curr].set_pc(curr_pc + advance);
                    self.cores[curr].if2dc.instruction = Instruction::nop();
                    self.cores[curr].dc2ex.instruction = Instruction::nop();
                    //println!("[SIM] thread {} waiting for {} to join", curr, to_wait)
                } else if func_name.contains("puts") {
                    let mut str_addr = self.get_i_register_of(curr, 10) as usize;
                    if str_addr != 0 {
                    let mut byte = mem.get_8(str_addr); let mut s = String::new();
                        while byte != 0 {
                            s.push(byte as char);
                            str_addr += 1;
                            byte = mem.get_8(str_addr);
                        }
                        println!("{}", s)
                    } else { panic!("[ERROR] BAD PUTS ON CORE {}", core) }
                } else if func_name.contains("GOMP_parallel") {
                } else if func_name.contains("omp_get_num_threads") {
                    let core = &mut self.cores[curr];
                    core.set_i_register(10, 4);
                } else if func_name.contains("omp_get_thread_num") {
                    let core = &mut self.cores[curr];
                    core.set_i_register(10, curr as i32);
                }

                self.cores[curr].ex2mem = rv32imc::MemData {
                    value: curr_pc.wrapping_add(advance),
                    pc: curr_pc,
                    wb_perform: true,
                    wb_rd: i.get_rd() as usize,
                    perform: None, addr: 0, size: rv32imc::WordSize::B,
                }
            } else {
                self.cores[curr].do_execute()
            }
        } else {
            self.cores[curr].do_execute()
        }
    }

    fn do_decode(&mut self, core:usize) {
        self.cores[core].do_decode()
    }

    fn do_fetch(&mut self, core:usize, mem:&mut dyn Memory) {

        if self.joining[core] != -1 {
            if self.cores[self.joining[core] as usize].finished() {
                self.joining[core] = -1;
            } else {
                self.cores[core].if2dc.instruction = Instruction::nop();
                return
            }
        }
/*
        if self.cores[core].get_pc() == 0 {
            for i in 0..self.active_threads {
                if self.joining[i] == core as i32 {
                    self.joining[i] = -1;
                }
            }
        } else {*/
        if !self.cores[core].finished() {
            self.cores[core].do_fetch(mem)
        }
        //}
    }
}

impl IntegerMachine for Machine {
    type IntegerType = i32;

    fn set_privilege(&mut self, _p : u8) { }
    fn get_privilege(&self) -> u8 { 0b11 }

    fn cycle(&mut self, mem:&mut dyn Memory) {
        self.cycles += 1;
        if self.cycles >= 10 {
            self.schedule_next_core();
        }

        let curr = self.current_core;
        self.do_write_back(curr);
        self.do_mem(curr, mem);
        self.do_execute(curr, mem);
        self.do_decode(curr);
        self.do_fetch(curr, mem);
    }

    fn get_i_register(&self, i:usize) -> i32 {
        self.cores[self.current_core].get_register(i)
    }

    fn set_i_register(&mut self, i:usize, value:i32) {
        self.cores[self.current_core].set_register(i, value)
    }

    fn get_csr_field(&self, i:CsrField) -> i32 {
        self.cores[self.current_core].get_csr_field(i)
    }

    fn set_csr_field(&mut self, i:CsrField, value:i32) {
        self.cores[self.current_core].set_csr_field(i, value)
    }

    fn get_pc(&self) -> i32 { self.cores[self.current_core].get_pc() }
    fn set_pc(&mut self, value:i32) { self.cores[self.current_core].set_pc(value) }

    fn finished(&self) -> bool {
        for core in &self.cores {
            if !core.finished() { return false }
        }
        true
    }
}

use std::ops::DerefMut;
impl MultiCoreIMachine for Machine {
    type IntegerType = i32;

    fn step(&mut self, memory:Arc<Mutex<dyn Memory + std::marker::Send>>) {
        let len = self.active_threads;
        crossbeam::thread::scope(|s| {
            let selfref = Arc::new(Mutex::new(self));
            for i in 0..len {
                let mem = memory.clone();
                let selfref = selfref.clone();
                s.spawn(move |_| {
                    selfref.lock().unwrap().do_write_back(i);
                    selfref.lock().unwrap().do_mem(i, mem.lock().unwrap().deref_mut());
                    selfref.lock().unwrap().do_execute(i, mem.lock().unwrap().deref_mut());
                    selfref.lock().unwrap().do_decode(i);
                    selfref.lock().unwrap().do_fetch(i, mem.lock().unwrap().deref_mut());
                });
            }
        }).expect("Execution step failed");
    }

    fn finished(&self) -> bool {
        for core in &self.cores {
            if !core.finished() { return false }
        }
        true
    }

    fn get_pc_of(&self, coreid:usize) -> i32 {
        self.cores[coreid].get_pc()
    }

    fn set_pc_of(&mut self, coreid:usize, value:i32) {
        self.cores[coreid].set_pc(value)
    }

    fn get_i_register_of(&self, coreid:usize, rid:usize) -> i32 {
        self.cores[coreid].get_i_register(rid)
    }

    fn set_i_register_of(&mut self, coreid:usize, rid:usize, value:i32) {
        self.cores[coreid].set_i_register(rid, value)
    }
}
