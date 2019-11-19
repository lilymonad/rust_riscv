use machine::IntegerMachine;
use isa::{CsrField, Instruction, OpCode};
use memory::*;
use bitvec::vec::BitVec;

use std::fmt;

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

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(0x{:x}, {})", self.fetch_pc, self.execution_mask)
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

    pub fn get_path_of_core(&self, cid:usize) -> &Path {
        for p in &self.paths {
            if p.execution_mask[cid] { return p }
        }

        panic!("No path");
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
            let old_pc = if self.current_path == 0xFFFFFFFF {
                0
            } else {
                self.paths[self.current_path].fetch_pc
            };
            let mut fusionned = HashMap::new();
            let mut fusion = false;
            for p in &self.paths {
                if let Some(lhs) = fusionned.get_mut(&p.fetch_pc) {
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

    pub fn for_each_core_alive<T:FnMut(&mut Core)->()>(&mut self, mut f:T) {
        let path = &mut self.paths[self.current_path];
        for i in 0..self.cores.len() {
            if path.execution_mask[i] {
                f(&mut self.cores[i]);
            }
        }
    }

    pub fn alive_cores_ids(&self) -> impl Iterator<Item=usize> {
        let bv = self.paths[self.current_path].execution_mask.clone();
        (0..self.cores.len()).into_iter().filter(move |i| bv[*i])
    }

    fn for_each_core_alive_i<T:FnMut(usize, &mut Core)->()>(&mut self, mut f:T) {
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
                self.for_each_core_alive(|core| {
                    core.registers[inst.get_rd() as usize] = inst.get_imm_u();
                });
            },
            OpCode::AUIPC => { // direct jumps are always uniform
                self.paths[pid].fetch_pc = pc.wrapping_add(inst.get_imm_u());
                update_pc = false
            },
            OpCode::JAL => {
                if inst.get_rd() != 0 {
                    self.for_each_core_alive(|core| {
                        core.registers[inst.get_rd() as usize] = pc.wrapping_add(4);
                    });
                }
                self.paths[pid].fetch_pc = pc.wrapping_add(inst.get_imm_j());
                update_pc = false
            },
            OpCode::JALR => { // indirect jump can be divergent multiple times

                let mut nph : HashMap<i32, BitVec> = HashMap::new();

                // Compute new paths based on the new thread PCs
                self.for_each_core_alive_i(|i, core| {
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
                });

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
                self.for_each_core_alive_i(|i, core| {
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
                });

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
                self.for_each_core_alive(|core| {
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
                self.for_each_core_alive(|core| {
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
                self.for_each_core_alive(|core| {
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
                self.for_each_core_alive(|core| {
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

        // If it was a jump, we update the mask history
        // for later analysis
        //
        // If it's not, we just advance the pc
        if update_pc {
            self.paths[pid].fetch_pc = next_pc
        } else {
            self.update_branch_hist(pc, mask.clone());
        }
    }
}

impl fmt::Display for Warp {
    fn fmt(&self, f:&mut fmt::Formatter<'_>) -> fmt::Result {
        let prelude = write!(f, "Warp {}c, \n", self.cores.len());
        self.paths.iter().fold(prelude, |res, p| {
            res.and(write!(f, "\t{}\n", p))
        })
    }
}

/// The barrier type, used to emulate pthread_barrier_* primitives.
/// As a barrier can be associated with its pointer, when creating a barrier,
/// we register a Barrier object associated with its pointer.
///
/// Barriers reinitialize when they are opened (when enough threads are waiting)
/// so we need to store the initial capacity to reinit the barrier.
struct Barrier {
    initial_cap:i32,
    current_cap:i32,
}

/// The SIMT-X machine. To handle `pthread` or `omp` system calls, we detect them
/// using plt information, and emulate them.
pub struct Machine {
    warps:Vec<Warp>,
    plt_addresses:HashMap<i32, String>,
    idle_threads:Vec<usize>,
    barriers:HashMap<i32, Barrier>,
    in_barrier:Vec<i32>,
}

impl Machine {
    pub fn new(tpw:usize, nb_warps:usize, plt_addresses:HashMap<i32, String>) -> Machine {
        let mut warps = Vec::new();
        warps.resize(nb_warps, Warp::new(tpw));

        let mut idle_threads = Vec::new();
        for i in (0..tpw*nb_warps).rev() {
            idle_threads.push(i)
        }

        let mut in_barrier = Vec::new();
        in_barrier.resize(tpw*nb_warps, 0);

        Machine {
            warps,
            plt_addresses,
            idle_threads,
            barriers:HashMap::new(),
            in_barrier,
        }
    }

    fn pop_first_idle(&mut self) -> usize {
        self.idle_threads.pop().expect("No more threads")
    }

    pub fn print_stats(&self) {
        for wid in 0..self.warps.len() {
            println!("=== STATS FOR WARP {} ===", wid);
            let warp = &self.warps[wid];
            for (pc, hist) in &warp.branch_mask_hist {
                println!("\t0x{:x}", pc);
                for bv in hist {
                    println!("\t{}", bv);
                }
            }
        }
    }

    fn free_barrier(&mut self, barr:i32) {
        for wid in 0..self.warps.len() {
            let warp = &mut self.warps[wid];
            let tpw = warp.cores.len();
            for pid in 0..warp.paths.len() {
                let pc = warp.paths[pid].fetch_pc;
                let mask = warp.paths[pid].execution_mask.clone();
                let mut bv_cont = BitVec::new(); bv_cont.resize(tpw, false);
                let mut bv_barr = BitVec::new(); bv_barr.resize(tpw, false);
                for cid in (0..tpw).filter(|i| mask[*i]) {
                    let tid = wid * tpw + cid;
                    if self.in_barrier[tid] == barr {
                        self.in_barrier[tid] = 0;
                        bv_cont.set(cid, true);
                    } else {
                        bv_barr.set(cid, true);
                    }
                }

                if bv_cont.any() {
                    warp.paths[pid].execution_mask = bv_cont;
                    warp.paths[pid].fetch_pc += 4;
                    
                    if bv_barr.any() {
                        warp.paths.push(Path::from_pc_mask(pc, bv_barr));
                    }
                }
            }
        }
    }
}

impl IntegerMachine for Machine {
    type IntegerType = i32;

    fn cycle(&mut self, mem:&mut dyn Memory) {
        let tpw = self.warps[0].cores.len();

        for wid in 0..self.warps.len() {
            self.warps[wid].schedule_path();

            let pathid = self.warps[wid].current_path;
            if pathid == 0xFFFFFFFF || self.warps[wid].paths[pathid].fetch_pc == 0 { continue }

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

                        mem.allocate_at((-1024i32 * (tid+1) as i32) as usize, 1024);

                        let cid = self.warps[wid].get_single_core_id();
                        // write in memory the tid
                        mem.set_32(self.warps[wid].cores[cid].registers[10] as usize, tid as u32);

                        // setup allocated core's register file
                        let mut regs = [0;32]; let stackoff = (-1024) * (tid as i32);
                        regs[2] = stackoff;
                        regs[8] = stackoff;
                        self.warps[w].cores[t].registers = regs;

                        // setup a new path with only allocated thread inside
                        let npc = self.warps[wid].cores[cid].registers[12];
                        let mut m = BitVec::new(); m.resize(tpw, false);
                        m.set(t, true);

                        self.warps[w].paths.push(Path::from_pc_mask(npc, m));

                        // return 0 and advance current path
                        self.warps[wid].cores[cid].registers[10] = 0;
                        self.warps[wid].paths[pathid].fetch_pc += 4;
                    } else if func_name.contains("pthread_join") {
                        let cid = self.warps[wid].get_single_core_id();
                        let to_wait = self.warps[wid].cores[cid].registers[10] as usize;
                        let w_to_wait = to_wait / tpw;
                        let c_to_wait = to_wait % tpw;

                        if self.warps[w_to_wait].get_path_of_core(c_to_wait).fetch_pc == 0 {
                            self.warps[wid].paths[pathid].fetch_pc += 4;
                        }
                    } else if func_name.contains("pthread_barrier_init") {
                        let cid = self.warps[wid].get_single_core_id();
                        let num = self.warps[wid].cores[cid].registers[12];
                        let ptr = self.warps[wid].cores[cid].registers[10];

                        self.barriers.insert(ptr, Barrier {
                            initial_cap:num,
                            current_cap:num,
                        });

                        self.warps[wid].paths[pathid].fetch_pc += 4;
                    } else if func_name.contains("pthread_barrier_wait") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let core = &self.warps[wid].cores[i];
                            let tid = wid*tpw + i;
                            let ptr = core.registers[10];

                            // don't re-execute the wait
                            if self.in_barrier[tid] == ptr { continue }

                            // if the barrier exists
                            if let Some(barr) = self.barriers.get_mut(&ptr) {

                                // put thread in barrier
                                self.in_barrier[tid] = ptr;
                                // decrement its capacity
                                barr.current_cap -= 1;

                                // it the barrier must open, free all threads
                                // then stop the loop
                                if barr.current_cap == 0 {
                                    barr.current_cap = barr.initial_cap;
                                    self.free_barrier(ptr);
                                    break;
                                }
                            }
                        }
                    } else if func_name.contains("puts") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let tid = i + wid*tpw;
                            println!("Core #{} [puts]", tid);
                        }
                        self.warps[wid].paths[pathid].fetch_pc += 4;
                    }
                } else {
                    self.warps[wid].execute(mem)
                }
            } else {
                self.warps[wid].execute(mem)
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
