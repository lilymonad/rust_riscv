use machine::IntegerMachine;
use isa::{Instruction, OpCode, CsrField};
use memory::Memory;
use machine::rv32imc::{self, Machine as RV32I};
use std::collections::HashMap;

struct ThreadData {
    pub registers : [ i32; 31 ],
    pub pc : i32,
}

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
        Machine {
            cores : [ RV32I::new(), RV32I::new()
                    , RV32I::new(), RV32I::new() ],
            joining : [ -1 ; 4 ],
            current_core : 0,
            //threads : vec![ ThreadData { registers: [ 0 ; 31 ], pc: 0 } ],
            active_threads : 1,
            cycles : 0,
            plt_addresses : plt,
        }
    }

    fn schedule_next_core(&mut self) {
        let mut i = (self.current_core + 1) % self.active_threads;
        let mut num = 0;
        while (self.joining[i] != -1 || self.cores[i].get_pc() == 0) && num < self.active_threads {
            if self.cores[i].get_pc() == 0 {
                println!("[SIM] !!! core {} finished !!!", i)
            }
            i = (i + 1) % self.active_threads;
            num += 1
        }
        self.cycles = 0;
        self.current_core = i;
    }

    fn do_write_back(&mut self) {
        self.cores[self.current_core].do_write_back()
    }

    fn do_mem(&mut self, mem:&mut dyn Memory) {
        self.cores[self.current_core].do_mem(mem)
    }

    fn do_execute(&mut self, mem:&mut dyn Memory) {
        let curr = self.current_core;
        let curr_pc = self.cores[curr].dc2ex.pc;
        let i = self.cores[curr].dc2ex.instruction;
        let address = curr_pc.wrapping_add(i.get_imm_j());

        if i.get_opcode() == OpCode::JAL.into() {
            
            if let Some(func_name) = self.plt_addresses.get(&address) {
                if func_name.contains("pthread_create") {
                    let i = self.active_threads as usize;
                    let npc = self.get_i_register(12);
                    self.active_threads += 1;
                    self.cores[i].set_pc(npc);
                    self.cores[i].set_i_register(1, 0);
                    self.cores[i].set_i_register(2, (-1024) * i as i32);
                    self.cores[i].set_i_register(8, (-1024) * i as i32);

                    mem.set_32(self.cores[curr].get_i_register(10) as usize, i as u32);
                    self.cores[curr].set_i_register(10, 0);
                    self.cores[curr].mem2wb = rv32imc::WriteBackData {
                        perform : false,
                        rd : 0,
                        value : 0,
                    };

                    //println!("[SIM] new thread on core {} at 0x{:x} (sp=s0={:x})", i, npc, (-1024) * i as i32)
                }
                else if func_name.contains("pthread_join") {
                    let to_wait = self.cores[curr].get_i_register(10);
                    self.joining[curr] = to_wait;
                    self.cores[curr].dc2ex.instruction = Instruction::addi(0, 0, 0);
                    self.schedule_next_core();
                    //println!("[SIM] thread {} waiting for {} to join", curr, to_wait)
                }
                else if func_name.contains("puts") {
                    let mut str_addr = self.get_i_register(10) as usize;
                    let mut byte = mem.get_8(str_addr); let mut s = String::new();
                    while byte != 0 {
                        byte = mem.get_8(str_addr);
                        s.push(byte as char);
                        str_addr += 1
                    }
                    println!("{}", s)
                }

                self.cores[self.current_core].ex2mem = rv32imc::MemData {
                    value: curr_pc.wrapping_add(4),
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

    fn do_decode(&mut self) {
        self.cores[self.current_core].do_decode()
    }

    fn do_fetch(&mut self, mem:&mut dyn Memory) {
        if self.cores[self.current_core].get_pc() == 0 {
            for i in 0..self.active_threads {
                if self.joining[i] == self.current_core as i32 {
                    self.joining[i] = -1;
                }
            }
        } else {
            self.cores[self.current_core].do_fetch(mem)
        }
    }
}

impl IntegerMachine for Machine {
    type IntegerType = i32;

    fn set_privilege(&mut self, _p : u8) { }
    fn get_privilege(&self) -> u8 { 0b11 }

    fn cycle(&mut self, mem:&mut dyn Memory) {
        self.cycles += 1;
        if self.cycles >= 10 {
            self.schedule_next_core()
        }

        println!("[SIM] === execute core {} ===", self.current_core);
        self.do_write_back();
        self.do_mem(mem);
        self.do_execute(mem);
        self.do_decode();
        self.do_fetch(mem);
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
}

