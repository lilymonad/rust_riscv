use machine::IntegerMachine;
use isa::{CsrField, Instruction, OpCode};
use memory::*;
use bitvec::vec::BitVec;

use std::collections::HashMap;

#[derive(Clone)]
struct Core {
    pub registers: [ i32; 32 ],
}

#[derive(Clone)]
struct Path {
    pub fetch_pc : i32,
    pub execution_mask : BitVec,
    pub waiting_for_sync : BitVec,
}

impl Path {
    pub fn from_pc_mask(pc:i32, mask:BitVec) -> Path {
        let mut waiting = BitVec::new();
        waiting.resize(mask.len(), false);
        Path {
            fetch_pc: pc,
            execution_mask: mask,
            waiting_for_sync: waiting,
        }
    }
}

#[derive(Clone)]
struct Warp {
    pub cores: Vec<Core>,
    pub paths: Vec<Path>,
    pub current_path : usize,
}

impl Warp {
    pub fn new(tpw:usize) -> Warp {
        let mut cs = Vec::new();
        cs.resize(tpw, Core { registers : [ 0; 32 ] });

        let ps = Vec::new();
        
        Warp {
            cores: cs,
            paths: ps,
            current_path: 0,
        }
    }

    fn schedule_path(&mut self) {
    }

    fn for_each_core_alive(&mut self, f:&mut dyn FnMut(&mut Core) -> ()) {
        let path = &mut self.paths[self.current_path];
        for i in 0..self.cores.len() {
            if path.execution_mask[i] {
                f(&mut self.cores[i]);
            }
        }
    }

    fn _for_each_core_alive_i(&mut self, f:&mut dyn FnMut(usize, &mut Core) -> ()) {
        let path = &mut self.paths[self.current_path];
        for i in 0..self.cores.len() {
            if path.execution_mask[i] {
                f(i, &mut self.cores[i]);
            }
        }
    }

    pub fn execute(&mut self, mem:&mut dyn Memory) {
        self.schedule_path();
        let path = &mut self.paths[self.current_path];
        let pc = path.fetch_pc;
        let inst = Instruction(mem.get_32(pc as usize));

        let nth = self.cores.len();

        match inst.get_opcode_enum() {
            OpCode::LUI => {
                self.for_each_core_alive(&mut | core : &mut Core | {
                    core.registers[inst.get_rd() as usize] = inst.get_imm_u();
                });
            },
            OpCode::AUIPC => { // direct jumps are always uniform
                path.fetch_pc = pc.wrapping_add(inst.get_imm_u());
            },
            OpCode::JAL => {
                mem.set_32(inst.get_rd() as usize, pc.wrapping_add(4) as u32);
                path.fetch_pc = pc.wrapping_add(inst.get_imm_j());
            },
            OpCode::JALR => { // indirect jump can be divergent multiple times
                mem.set_32(inst.get_rd() as usize, pc.wrapping_add(4) as u32);

                let mut nph : HashMap<i32, BitVec> = HashMap::new();

                // Compute new paths based on the new thread PCs
                for i in 0..nth {
                    let core = &mut self.cores[i];
                    if path.execution_mask[i] {
                        let new_pc = inst.get_imm_i().
                            wrapping_add(core.registers[inst.get_rs1() as usize]);
                        if nph.contains_key(&new_pc) {
                            nph.get_mut(&new_pc).unwrap().set(i, true);
                        } else {
                            let mut bv = BitVec::new();
                            bv.resize(nth, false);
                            bv.set(i, true);
                            nph.insert(new_pc, bv).unwrap();
                        }
                    }
                }

                // Check if it's a uniform jump
                // and just update the pc of the current path if it is
                if nph.len() == 1 {
                    path.fetch_pc = *nph.keys().next().unwrap();
                } else {
                    // If not, create as many paths as needed and inject them
                    self.paths.remove(self.current_path);
                    for (pc, mask) in nph {
                        self.paths.push(Path::from_pc_mask(pc, mask));
                    }
                }
            },
            OpCode::BRANCH => { // conditional branch
                let  tpc = pc.wrapping_add(inst.get_imm_b());
                let ntpc = pc.wrapping_add(4);

                let mut taken_mask = BitVec::new();
                let mut not_taken_mask = BitVec::new();
                taken_mask.resize(nth, false);
                not_taken_mask.resize(nth, false);

                // compute taken/not_taken masks for each alive thread
                for i in 0..nth {
                    if path.execution_mask[i] {
                        let core = &self.cores[i];
                        let r1 = inst.get_rs1() as usize;
                        let v1 = core.registers[r1];
                        let uv1 = v1 as u32;

                        let r2 = inst.get_rs2() as usize;
                        let v2 = core.registers[r2];
                        let uv2 = v2 as u32;

                        let take = match inst.get_funct3() {
                            0b000 => v1 ==  v2, // BEQ
                            0b001 => v1 !=  v2 , // BNE
                            0b010 => v1 <   v2 , // BLT
                            0b011 => v1 >=  v2 , // BGE
                            0b100 => uv1 <  uv2 , // BLTU
                            0b101 => uv1 >= uv2 , // BGEU
                            _ => false,
                        };

                        taken_mask.set(i, take);
                        not_taken_mask.set(i, !take);
                    }
                }

                // update path, and add new paths if divergent
                if !not_taken_mask.any() {    // uniform taken
                    path.fetch_pc = tpc;
                } else if !taken_mask.any() { // uniform not taken
                    path.fetch_pc = ntpc;
                } else {                      // divergent
                    self.paths.remove(self.current_path);
                    self.paths.push(Path::from_pc_mask(tpc, taken_mask));
                    self.paths.push(Path::from_pc_mask(ntpc, not_taken_mask));
                }
            },
            OpCode::LOAD => {
                let width = inst.get_funct3();
                self.for_each_core_alive(&mut |core| {
                    let base = core.registers[inst.get_rs1() as usize] as usize;
                    let addr = base.wrapping_add(inst.get_imm_i() as usize);
                    core.registers[inst.get_rd() as usize] =
                        match width {
                            0 => mem.get_8(addr) as i32,
                            1 => mem.get_16(addr) as i32,
                            2 => mem.get_32(addr) as i32,
                            _ => 0, // ERROR
                        };
                });
            },
            OpCode::STORE => {
                let width = inst.get_funct3();
                self.for_each_core_alive(&mut |core| {
                    let base = core.registers[inst.get_rs1() as usize] as usize;
                    let addr = base.wrapping_add(inst.get_imm_i() as usize);
                    let src = core.registers[inst.get_rs2() as usize];
                    match width {
                        0 => mem.set_8(addr, src as u8),
                        1 => mem.set_16(addr, src as u16),
                        2 => mem.set_32(addr, src as u32),
                        _ => {}, // ERROR
                    }
                });
            },
            OpCode::OPIMM => {
                self.for_each_core_alive(&mut |core| {
                    let dst = inst.get_rd() as usize;

                    let v1 = core.registers[inst.get_rs1() as usize];
                    let v2 =    if inst.get_funct3() & 0b11 == 1 {
                                    inst.get_rs2() as i32
                                }
                                else { inst.get_imm_i() };

                    core.registers[dst] = match inst.get_funct3() {
                        0b000 => v1.wrapping_add(v2),
                        0b010 => (v1 < v2) as i32,
                        0b011 => ((v1 as u32) < v2 as u32) as i32,
                        0b100 => v1 ^ v2,
                        0b110 => v1 | v2,
                        0b111 => v1 & v2,
                        0b001 => v1 << v2,
                        0b101 => if inst.get_funct7() != 0 { v1 >> v2 }
                                 else { ((v1 as u32) >> v2) as i32 },
                        _ => 0, // Cannot be here, because funct3 is on 3 bits
                    };
                });
            },
            OpCode::OPREG => {
                self.for_each_core_alive(&mut |core| {
                    let dst = inst.get_rd() as usize;
                    let v1 = core.registers[inst.get_rs1() as usize];
                    let v2 = core.registers[inst.get_rs2() as usize];

                    core.registers[dst] = match inst.get_funct7() {
                        0b0000000 => match inst.get_funct3() {
                            0b000 => v1.wrapping_add(v2),
                            0b001 => v1 >> v2,
                            0b010 => (v1 < v2) as i32,
                            0b011 => ((v1 as u32) < v2 as u32) as i32,
                            0b100 => v1 ^ v2,
                            0b101 => ((v1 as u32) >> v2) as i32,
                            0b110 => v1 | v2,
                            0b111 => v1 & v2,
                            _ => 0, // Cannot be here, because funct3 is on 3 bits
                        },
                        0b0000001 => match inst.get_funct3() {
                            _ => 0, // TODO handle M extension (mul/div)
                        },
                        0b0100000 => match inst.get_funct3() {
                            0b000 => v1.wrapping_sub(v2),
                            0b101 => v1 >> v2,
                            _ => 0, // TODO handle bad funct3 values
                        },
                        _ => 0, // TODO add other extensions (F has priority)
                    };
                });
            },
            _ => {}
        }
    }
}

pub struct Machine {
    warps:Vec<Warp>,
}

impl Machine {
    pub fn new(tpw:usize, nb_warps:usize) -> Machine {
        let mut ws = Vec::new();
        ws.resize(nb_warps, Warp::new(tpw));
        Machine {
            warps: ws.clone(),
        }
    }
}

impl IntegerMachine for Machine {
    type IntegerType = i32;


    fn cycle(&mut self, mem:&mut dyn Memory) {
        for warp in &mut self.warps {
            warp.execute(mem)
        }
    }

    fn get_i_register(&self, _id:usize) -> i32 {
        0
    }

    fn set_i_register(&mut self, _id:usize, _value:i32) {
    }

    fn get_pc(&self) -> i32 {
        0
    }

    fn set_pc(&mut self, _value:i32) {
    }

    fn get_privilege(&self) -> u8 {
        0
    }

    fn set_privilege(&mut self, _value:u8) {
    }

    fn get_csr_field(&self, _field:CsrField) -> i32 {
        0
    }

    fn set_csr_field(&mut self, _field:CsrField, _value:i32) {
    }
}
