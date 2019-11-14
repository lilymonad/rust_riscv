use machine::IntegerMachine;
use isa::{CsrField, Instruction, OpCode};
use memory::*;
use bitvec::vec::BitVec;

use std::collections::HashMap;

/// Defines the state of a single hardware thread.
#[derive(Clone)]
struct Core {
    pub registers: [ i32; 32 ],
}

/// Defines a SIMT Path. As threads are grouped in `Warp`s executed in lockstep,
/// we handle divergence by remembering where all threads are with a
/// `(fetch_pc, execution_mask)` tuple. Before fetching instructions, we chose
/// a `Path` to advance.
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

    pub fn is_single(&self) -> bool {
        self.execution_mask.count_ones() == 1
    }
}

/// Defines a hardware warp (a group of threads) which all execute instructions
/// in an SIMD fasion.
#[derive(Clone)]
struct Warp {
    pub cores: Vec<Core>,
    pub paths: Vec<Path>,
    pub current_path: usize,

    // Log variables
    branch_mask_hist: HashMap<i32, Vec<BitVec>>,
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
            branch_mask_hist: HashMap::new(),
        }
    }

    pub fn get_single_core_id(&mut self) -> usize {
        let mask = &self.paths[self.current_path].execution_mask;
        for i in 0..self.cores.len() {
            if mask[i] {
                return i
            }
        }

        panic!("A path is empty")
    }

    pub fn schedule_path(&mut self) {
        if self.paths.is_empty() { self.current_path = 0xFFFFFFFF }
        else {
            let old_pc = self.paths[self.current_path].fetch_pc;
            let mut fusionned = HashMap::new();
            let mut fusion = false;
            for p in &self.paths {
                if fusionned.contains_key(&p.fetch_pc) {
                    let lhs = fusionned.get_mut(&p.fetch_pc).unwrap();
                    *lhs |= p.execution_mask.clone();
                    fusion = true;
                } else {
                    fusionned.insert(p.fetch_pc, p.execution_mask.clone());
                }
            }

            if fusion {
                let mut npaths = Vec::new();
                for (k, v) in fusionned {
                    npaths.push(Path::from_pc_mask(k, v));
                }
                self.current_path = 0;
                if npaths[self.current_path].fetch_pc == old_pc {
                    self.current_path = (self.current_path + 1) % npaths.len();
                }
                self.paths = npaths.clone();
            } else {
                self.current_path = (self.current_path + 1) % self.paths.len();
            }
        }
    }

    pub fn for_each_core_alive(&mut self, f:&mut dyn FnMut(&mut Core) -> ()) {
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

    fn update_branch_hist(&mut self, pc:i32, mask:BitVec) {
        if let Some(hist) = self.branch_mask_hist.get_mut(&pc) {
            hist.push(mask);
        } else {
            self.branch_mask_hist.insert(pc, vec![mask]);
        }
    }

    pub fn execute(&mut self, mem:&mut dyn Memory) {
        if self.current_path == 0xFFFFFFFF { return }

        let pid = self.current_path;
        let path = self.paths[pid].clone();
        let mask = &path.execution_mask;
        let pc = path.fetch_pc;
        let next_pc = pc.wrapping_add(4);
        let inst = Instruction(mem.get_32(pc as usize));

        let nth = self.cores.len();

        let mut update_pc = true;
        match inst.get_opcode_enum() {
            OpCode::LUI => {
                self.for_each_core_alive(&mut | core : &mut Core | {
                    core.registers[inst.get_rd() as usize] = inst.get_imm_u();
                });
            },
            OpCode::AUIPC => { // direct jumps are always uniform
                self.paths[pid].fetch_pc = pc.wrapping_add(inst.get_imm_u());
                update_pc = false
            },
            OpCode::JAL => {
                if inst.get_rd() != 0 {
                    self.for_each_core_alive(&mut |core| {
                        core.registers[inst.get_rd() as usize] = pc.wrapping_add(4);
                    });
                }
                self.paths[pid].fetch_pc = pc.wrapping_add(inst.get_imm_j());
                update_pc = false
            },
            OpCode::JALR => { // indirect jump can be divergent multiple times

                let mut nph : HashMap<i32, BitVec> = HashMap::new();

                // Compute new paths based on the new thread PCs
                for i in 0..nth {
                    let core = &mut self.cores[i];
                    if path.execution_mask[i] {
                        let new_pc = inst.get_imm_i().
                            wrapping_add(core.registers[inst.get_rs1() as usize]);
                        if let Some(bv) = nph.get_mut(&new_pc) {
                            bv.set(i, true);
                        } else {
                            let mut bv = BitVec::new();
                            bv.resize(nth, false);
                            bv.set(i, true);
                            nph.insert(new_pc, bv);
                        }
                        if inst.get_rd() != 0 {
                            core.registers[inst.get_rd() as usize] = pc.wrapping_add(4);
                        }
                    }
                }

                // Check if it's a uniform jump
                // and just update the pc of the current path if it is
                if nph.len() == 1 {
                    self.paths[pid].fetch_pc = *nph.keys().next().unwrap();
                } else {
                    // If not, create as many paths as needed and inject them
                    self.paths.remove(self.current_path);
                    for (pc, mask) in nph {
                        self.paths.push(Path::from_pc_mask(pc, mask));
                    }
                }

                update_pc = false
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
                            0b000 => {v1 ==  v2}, // BEQ
                            0b001 => {v1 !=  v2 }, // BNE
                            0b100 => {v1 <   v2 }, // BLT
                            0b101 => { v1 >=  v2 }, // BGE
                            0b110 =>{ uv1 <  uv2 }, // BLTU
                            0b111 =>{ uv1 >= uv2 }, // BGEU
                            _ => false,
                        };

                        taken_mask.set(i, take);
                        not_taken_mask.set(i, !take);
                    }
                }

                // update path, and add new paths if divergent
                if !not_taken_mask.any() {    // uniform taken
                    self.paths[pid].fetch_pc = tpc;
                } else if !taken_mask.any() { // uniform not taken
                    self.paths[pid].fetch_pc = ntpc;
                } else {                      // divergent
                    self.paths.remove(self.current_path);
                    self.paths.push(Path::from_pc_mask(tpc, taken_mask));
                    self.paths.push(Path::from_pc_mask(ntpc, not_taken_mask));
                }

                update_pc = false
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
                            _ => panic!("LOAD: bad word width"), // ERROR
                        };
                });
            },
            OpCode::STORE => {
                let width = inst.get_funct3();
                self.for_each_core_alive(&mut |core| {
                    let base = core.registers[inst.get_rs1() as usize] as usize;
                    let addr = base.wrapping_add(inst.get_imm_s() as usize);
                    let src = core.registers[inst.get_rs2() as usize];
                    match width {
                        0 => mem.set_8(addr, src as u8),
                        1 => mem.set_16(addr, src as u16),
                        2 => mem.set_32(addr, src as u32),
                        _ => panic!("STORE: Bad word width"), // ERROR
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

        self.update_branch_hist(pc, mask.clone());
        if update_pc {
            self.paths[pid].fetch_pc = next_pc
        }
    }
}

/// The SIMT-X machine. To handle `pthread` or `omp` system calls, we detect them
/// using plt information, and emulate them.
pub struct Machine {
    warps:Vec<Warp>,
    plt_addresses:HashMap<i32, String>,
    idle_threads:Vec<usize>,
    finished:BitVec,
}

impl Machine {
    pub fn new(tpw:usize, nb_warps:usize, plt:HashMap<i32, String>) -> Machine {
        let mut ws = Vec::new();
        ws.resize(nb_warps, Warp::new(tpw));

        let mut idle = Vec::new();
        for i in (0..tpw*nb_warps).rev() {
            idle.push(i)
        }

        let mut fin = BitVec::new();
        fin.resize(tpw*nb_warps, false);

        Machine {
            warps: ws.clone(),
            plt_addresses:plt,
            idle_threads:idle.clone(),
            finished:fin,
        }
    }

    fn pop_first_idle(&mut self) -> usize {
        self.idle_threads.pop().expect("No more threads")
    }
}

impl IntegerMachine for Machine {
    type IntegerType = i32;

    fn cycle(&mut self, mem:&mut dyn Memory) {
        let tpw = self.warps[0].cores.len();

        for wid in 0..self.warps.len() {
            self.warps[wid].schedule_path();

            let pathid = self.warps[wid].current_path;
            if self.warps[wid].paths[pathid].fetch_pc == 0 { continue }

            let pc = self.warps[wid].paths[pathid].fetch_pc;
            let i = Instruction(mem.get_32(pc as usize));
            let address = pc.wrapping_add(i.get_imm_j());

            if i.get_opcode_enum() == OpCode::JAL {
                if let Some(func_name) = self.plt_addresses.get(&address) {

                    
                    if func_name.contains("pthread_create") {

                        assert!(self.warps[wid].paths[pathid].is_single(),
                            "pthread_create must be called by only 1 thread");

                        // allocate a new thread (get its id)
                        let tid = self.pop_first_idle();
                        let w = tid / tpw; let t = tid % tpw;

                        let cid = self.warps[wid].get_single_core_id();
                        // write in memory the tid
                        mem.set_32(self.warps[wid].cores[cid].registers[10] as usize, tid as u32);

                        // setup allocated core's register file
                        let mut regs = [0;32]; let stackoff = (-1024) * tid as i32;
                        regs[2] = stackoff;
                        regs[8] = stackoff;
                        self.warps[w].cores[t].registers = regs;

                        // setup a new path with only allocated thread inside
                        let npc = self.warps[wid].cores[cid].registers[12];
                        let mut m = BitVec::new(); m.resize(tpw, false);
                        m.set(t, true);

                        self.warps[wid].paths.push(Path::from_pc_mask(npc, m));

                        // return 0 and advance current path
                        self.warps[wid].cores[cid].registers[10] = 0;
                        self.warps[wid].paths[pathid].fetch_pc += 4;
                    } else if func_name.contains("pthread_join") {
                        let cid = self.warps[wid].get_single_core_id();
                        let to_wait = self.warps[wid].cores[cid].registers[10];
                        if self.finished[to_wait as usize] {
                            self.warps[wid].paths[pathid].fetch_pc += 4;
                        }
                    } else if func_name.contains("puts") {
                        let cid = self.warps[wid].get_single_core_id();
                        println!("Core #{} [puts]", cid+wid*tpw);
                        self.warps[wid].paths[pathid].fetch_pc += 4;
                    }
                } else {
                    self.warps[wid].execute(mem)
                }
            } else {
                self.warps[wid].execute(mem)
            }

            for i in 0..tpw {
                if self.warps[wid].paths[pathid].execution_mask[i] &&
                    self.warps[wid].cores[i].registers[2] == ((i as i32) *(-1024)) {
                        self.finished.set(i, true);
                }
            }
        }
    }

    fn get_i_register(&self, id:usize) -> i32 {
        return self.warps[0].cores[0].registers[id]
    }

    fn set_i_register(&mut self, _id:usize, _value:i32) {
    }

    fn get_pc(&self) -> i32 {
        for path in &self.warps[0].paths {
            if path.execution_mask[0] {
                return path.fetch_pc
            }
        }

        panic!("No path in warp 0")
    }

    fn set_pc(&mut self, value:i32) {
        if self.warps[0].paths.is_empty() {
            let th = self.pop_first_idle();
            let mut m = BitVec::new(); m.resize(self.warps[0].cores.len(), false);
            m.set(th, true);
            self.warps[0].paths.push(Path::from_pc_mask(value, m));
        }
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

    fn finished(&self) -> bool {
        for warp in &self.warps {
            for path in &warp.paths {
                if path.fetch_pc != 0 {
                    return false
                }
            }
        }
        true
    }
}
