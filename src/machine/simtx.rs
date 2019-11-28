use machine::MultiCoreIMachine;
use isa::{Instruction, OpCode};
use memory::*;
use types::{MachineInteger, BitSet};
use std::sync::{Arc, Mutex};
use std::fmt;
use std::ops::DerefMut;
use std::collections::{HashMap, BTreeMap};

type BitVec = u32;
pub static MAX_TPW : usize = core::mem::size_of::<BitVec>() * 8;

/// Defines the state of a single hardware thread.
#[derive(Clone)]
struct Core {
    pub registers: [ i32; 32 ],
}

/// Defines a SIMT Path. As threads are grouped in `Warp`s executed in lockstep,
/// we handle divergence by remembering where all threads are with a
/// `(fetch_pc, execution_mask)` tuple. Before fetching instructions, we chose
/// a `Path` to advance.
#[derive(Clone, Copy)]
struct Path {
    pub fetch_pc : i32,
    pub execution_mask : BitVec,
    pub waiting_for_sync : BitVec,
    pub time_since_scheduled : usize,
}

impl Path {
    pub fn from_pc_mask(pc:i32, mask:BitVec) -> Path {
        Path {
            fetch_pc: pc,
            execution_mask: mask,
            waiting_for_sync: 0,
            time_since_scheduled: 0,
        }
    }

    pub fn is_single(&self) -> bool {
        self.execution_mask.count_ones() == 1
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(0x{:x}, {:b})", self.fetch_pc, self.execution_mask)
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
    thresholds: usize,
    fusions: usize,
}

impl Warp {
    pub fn new(tpw:usize) -> Warp {
        let mut cores = Vec::new();
        cores.resize(tpw, Core { registers : [ 0; 32 ] });
        Warp {
            cores,
            paths: Vec::new(),
            current_path: 0,
            branch_mask_hist: HashMap::new(),
            thresholds: 0,
            fusions: 0,
        }
    }

    pub fn get_path_of_core_mut(&mut self, cid:usize) -> &mut Path {
        for p in &mut self.paths {
            if p.execution_mask.at(cid) { return p }
        }

        panic!("No path");
    }

    pub fn get_path_of_core(&self, cid:usize) -> &Path {
        for p in &self.paths {
            if p.execution_mask.at(cid) { return p }
        }

        panic!("No path");
    }

    pub fn get_single_core_id(&mut self) -> usize {
        let mask = &self.paths[self.current_path].execution_mask;
        for i in 0..self.cores.len() {
            if mask.at(i) {
                return i
            }
        }

        panic!("A path is empty")
    }

    /// This function should be called right before any FETCH step of the `Warp`
    /// to ensure we always execute a valid path.
    ///
    /// This function sets the `current_path` of the `Warp` correcly according
    /// to the scheduling rule, but also fusion paths with the same PC.
    pub fn schedule_path(&mut self) {
        if self.paths.is_empty() { self.current_path = 0xFFFFFFFF }
        else {
            let old_pc = if self.current_path == 0xFFFFFFFF {
                0
            } else {
                self.paths[self.current_path].fetch_pc
            };

            // Fusion of path with the same PC
            let mut fusionned = HashMap::new();
            let mut fusion = false;
            for p in &self.paths {
                if let Some(lhs) = fusionned.get_mut(&p.fetch_pc) {
                    *lhs |= p.execution_mask;
                    fusion = true;
                } else {
                    fusionned.insert(p.fetch_pc, p.execution_mask);
                }
            }

            // If fusion occurred, rebuild the path table
            // + reset current_path to 0
            if fusion {
                self.fusions += 1;
                let mut npaths = Vec::new();
                for (k, v) in fusionned {
                    if k == old_pc {
                        self.current_path = npaths.len();
                    }
                    npaths.push(Path::from_pc_mask(k, v));
                }
                self.paths = npaths;
            }

            // else use schedule method
            // [round robin]
            //self.current_path = (self.current_path + 1) % self.paths.len();

            // [min pc + time idle]
            for i in 0..self.paths.len() {
                // if the idle time of the thread is greater than a threshold
                // execute this path in priority
                if self.paths[i].time_since_scheduled > 64 {
                    self.current_path = i;
                    self.paths[i].time_since_scheduled = 0;
                    self.thresholds += 1;
                    break
                }

                // compute the path with the minimum pc
                let ipc = self.paths[i].fetch_pc;
                if ipc < self.paths[self.current_path].fetch_pc {
                    self.current_path = i
                }
            }

            // for each not-chosen path, increment their idle time
            for i in 0..self.paths.len() {
                if i == self.current_path { continue }
                self.paths[i].time_since_scheduled += 1
            }
        }
    }

    /// This function is a helper used to work on all alive threads of the
    /// `current_path`.
    pub fn for_each_core_alive<T:FnMut(&mut Core)->()>(&mut self, mut f:T) {
        let path = &mut self.paths[self.current_path];
        for i in 0..self.cores.len() {
            if path.execution_mask.at(i) {
                f(&mut self.cores[i]);
            }
        }
    }

    /// Same as `for_each_core_alive()` but with the ID of the core.
    fn for_each_core_alive_i<T:FnMut(usize, &mut Core)->()>(&mut self, mut f:T) {
        let path = &mut self.paths[self.current_path];
        for i in 0..self.cores.len() {
            if path.execution_mask.at(i) {
                f(i, &mut self.cores[i]);
            }
        }
    }

    /// Returns an iterator going through all alive cores IDs in order.
    pub fn alive_cores_ids(&self) -> impl Iterator<Item=usize> {
        let bv = self.paths[self.current_path].execution_mask;
        (0..self.cores.len()).into_iter().filter(move |i| bv.at(*i))
    }

    fn update_branch_hist(&mut self, pc:i32, mask:BitVec) {
        if let Some(hist) = self.branch_mask_hist.get_mut(&pc) {
            hist.push(mask);
        } else {
            self.branch_mask_hist.insert(pc, vec![mask]);
        }
    }

    /// Fully executes an instruction (from Fetch to Commit)
    /// 
    /// This operation is NOT cycle accurate. Will be later when needed.
    pub fn execute(&mut self, mem:&mut dyn Memory) {
        if self.current_path == 0xFFFFFFFF { return }

        let pid = self.current_path;
        let path = self.paths[pid];
        let mask = &path.execution_mask;
        let pc = path.fetch_pc;
        let inst = Instruction(mem.get_32(pc as usize));

        let (inst, advance) = if inst.is_compressed() {
            (inst.uncompressed(), 2)
        } else {
            (inst, 4)
        };

        let next_pc = pc.wrapping_add(advance);
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
                        core.registers[inst.get_rd() as usize] = pc.wrapping_add(advance);
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
                        bv.set(i);
                    } else {
                        nph.insert(new_pc, BitVec::singleton(i));
                    }
                    if inst.get_rd() != 0 {
                        core.registers[inst.get_rd() as usize] = pc.wrapping_add(advance);
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
                let ntpc = pc.wrapping_add(advance);

                let mut taken_mask = 0;

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

                    if take {
                        taken_mask.set(i);
                    }
                });

                let not_taken_mask = (!taken_mask) & self.paths[self.current_path].execution_mask;

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
                    let base = core.registers[inst.get_rs1() as usize];
                    let imm = inst.get_imm_i();
                    //println!("{:x}(r{}) + {:x} = {:x}", base, inst.get_rs1(), imm, base.wrapping_add(imm));
                    let addr = (base.wrapping_add(imm) as usize) & 0xffffffff;
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
                    let base = core.registers[inst.get_rs1() as usize];
                    let addr = (base.wrapping_add(inst.get_imm_s()) as usize) & 0xffffffff;
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
                    //if dst == 2 { println!("{} -> r2 = 0x{:08x}", inst, core.registers[dst]) }
                });
            },
            OpCode::OPREG => {
                self.for_each_core_alive(|core| {
                    let dst = inst.get_rd() as usize;
                    let v1 = core.registers[inst.get_rs1() as usize];
                    let v2 = core.registers[inst.get_rs2() as usize];
                    let uv1 = v1 as u32;
                    let uv2 = v2 as u32;
                    let v1_64 = v1 as i64;
                    let v2_64 = v2 as i64;
                    let uv1_64 = uv1 as u64;
                    let uv2_64 = uv2 as u64;

                    let allset = i32::all_set();

                    //if pc == 0x10766 { println!("r14={}, r12={}", v1, v2) }
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
                            0b000 => v1 * v2,
                            0b001 => ((v1_64 * v2_64) >> 32) as i32,
                            0b010 => ((v1_64 * (uv2_64 as i64)) >> 32) as i32,
                            0b011 => ((uv1_64 * uv2_64) >> 32) as i32,
                            0b100 => if v2 == 0 { allset } else { v1 / v2 }, // DIV
                            0b101 => if v2 == 0 { allset } else { (uv1 / uv2) as i32 }, // DIVU
                            0b110 => if v2 == 0 { v1 } else { v1 % v2 }, // REM
                            0b111 => if v2 == 0 { v1 } else { (uv1 % uv2) as i32 }, // REMU
                            _ => 0,
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
            self.update_branch_hist(pc, *mask);
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

/// The barrier type, used to emulate `pthread_barrier_*` primitives.
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
    // Our cores
    warps:Vec<Warp>,


    // For dynamic library calls emulation
    plt_addresses:HashMap<i32, String>,

    // pthread_create thread pool
    idle_threads:Vec<usize>,

    // For pthread_barrier
    in_barrier:Vec<i32>,
    barriers:HashMap<i32, Barrier>,

    // For malloc
    heap_ptr:usize,
    heap_elements:BTreeMap<usize, (usize, bool)>,

    // For loop detection
    detected_loops: HashMap<i32, i32>,
}

impl Machine {
    pub fn new(tpw:usize, nb_warps:usize, plt_addresses:HashMap<i32, String>) -> Machine {

        if tpw > MAX_TPW {
            panic!("This version of SIMTX is compiled with MAX_TPW={}", MAX_TPW)
        }

        let mut warps = Vec::new();
        warps.resize(nb_warps, Warp::new(tpw));

        let mut idle_threads = Vec::new();
        for i in (0..tpw*nb_warps).rev() {
            idle_threads.push(i)
        }

        let mut in_barrier = Vec::new();
        in_barrier.resize(tpw*nb_warps, 0);

        Machine {
            detected_loops: HashMap::new(),
            warps,
            plt_addresses,
            idle_threads,
            barriers:HashMap::new(),
            in_barrier,
            heap_ptr:0x10000000,
            heap_elements:BTreeMap::new(),
        }
    }

    fn malloc(&mut self, mem:&mut dyn Memory, size:usize) -> usize {
        mem.allocate_at(self.heap_ptr, size);

        for (ptr, (chunk_size, used)) in &mut self.heap_elements {
            if !(*used) && *chunk_size < size {
                *used = true;
                return *ptr
            }
        }

        self.heap_elements.insert(self.heap_ptr, (size, true));

        let ret = self.heap_ptr;
        self.heap_ptr += size;

        ret
    }

    fn free(&mut self, ptr:usize) {
        self.heap_elements.get_mut(&ptr)
            .expect("Free unalocated pointer").1 = false;
    }

    fn pop_first_idle(&mut self) -> usize {
        self.idle_threads.pop().expect("No more threads")
    }

    fn push_idle(&mut self, thread:usize) {
        self.idle_threads.push(thread)
    }

    /// Prints the history of execution masks of the branch at address `pc`.
    /// If the address is not a branch or has never been met, it just prints
    /// nothing.
    pub fn print_stats_for_pc(&self, pc:usize) {
        for wid in 0..self.warps.len() {
            println!("=== STATS FOR WARP {} AT PC {} ===", wid, pc);
            let warp = &self.warps[wid];
            warp.branch_mask_hist.get(&(pc as i32)).map( |hist| {
                for bv in hist {
                    println!("\t[{:032b}]", bv);
                }
            });
        }
    }

    /// Prints for each warps the history of all the branch instructions
    /// encountered. It also prints information about thhe scheduler and the
    /// Loop-Detector.
    pub fn print_stats(&self) {
        for wid in 0..self.warps.len() {
            println!("=== STATS FOR WARP {} ===", wid);
            let warp = &self.warps[wid];
            for (pc, hist) in &warp.branch_mask_hist {
                println!("\t0x{:x}", pc);
                for bv in hist {
                    println!("\t[{:032b}]", bv);
                }
            }
            println!("threshold reached {} times", warp.thresholds);
            println!("paths fusionned {} times", warp.fusions);
            println!("detected loops:");
            for (end, start) in &self.detected_loops {
                println!("{:08x} -> {:08x}", start, end)
            }
        }
    }

    fn free_barrier(&mut self, barr:i32) {
        for wid in 0..self.warps.len() {
            let warp = &mut self.warps[wid];
            let tpw = warp.cores.len();
            for pid in 0..warp.paths.len() {
                let pc = warp.paths[pid].fetch_pc;
                let mask = warp.paths[pid].execution_mask;
                let mut bv_cont = 0;
                let mut bv_barr = 0;
                for cid in (0..tpw).filter(|i| mask.at(*i)) {
                    let tid = wid * tpw + cid;
                    if self.in_barrier[tid] == barr {
                        self.in_barrier[tid] = 0;
                        bv_cont.set(cid);
                    } else {
                        bv_barr.set(cid);
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

impl MultiCoreIMachine for Machine {
    type IntegerType = i32;

    fn step(&mut self, mem:Arc<Mutex<dyn Memory + std::marker::Send>>) {
        let mut mem = mem.lock().unwrap();
        let tpw = self.warps[0].cores.len();

        let old_gp = self.warps[0].cores[0].registers[3];
        for wid in 0..self.warps.len() {
            self.warps[wid].schedule_path();

            let pathid = self.warps[wid].current_path;
            if pathid == 0xFFFFFFFF || self.warps[wid].paths[pathid].fetch_pc == 0 { continue }
            let pc = self.warps[wid].paths[pathid].fetch_pc;
            let i = Instruction(mem.get_32(pc as usize));

            let (advance, i) = if i.is_compressed() {
                (2, i.uncompressed())
            } else {
                (4, i)
            };

        //let old14 = self.warps[wid].cores[0].registers[14];

            println!("warp {} 0x{:x} :: {}", wid, pc, i);
        
            if i.is_jump() {
                if i.jump_offset() < 0 {
                    self.detected_loops.insert(pc, pc+i.jump_offset());
                }
            }

            if i.get_opcode_enum() == OpCode::JAL {
                let address = pc.wrapping_add(i.get_imm_j());
                if let Some(func_name) = self.plt_addresses.get(&address) {
                    if func_name.contains("pthread_create") {

                        assert!(self.warps[wid].paths[pathid].is_single(),
                            "pthread_create must be called by only 1 thread");

                        // allocate a new thread (get its id)
                        let tid = self.pop_first_idle();
                        let w = tid / tpw; let t = tid % tpw;

                        let stacksize = 0x00200000;
                        let stackstart = 0x0ff00000 - (0x00200000 * tid); 
                        let stackend = stackstart - stacksize;
                        mem.allocate_at(stackend, stacksize);

                        let cid = self.warps[wid].get_single_core_id();
                        // write in memory the tid
                        mem.set_32(self.warps[wid].cores[cid].registers[10] as usize, tid as u32);

                        // setup allocated core's register file
                        let mut regs = [0;32];
                        regs[2] = stackstart as i32 - 1;
                        regs[8] = stackstart as i32 - 1;
                        regs[3] = self.warps[wid].cores[cid].registers[3];
                        regs[4] = tid as i32;
                        self.warps[w].cores[t].registers = regs;

                        // setup a new path with only allocated thread inside
                        let npc = self.warps[wid].cores[cid].registers[12];
                        let m = BitSet::singleton(t);

                        self.warps[w].paths.push(Path::from_pc_mask(npc, m));

                        // return 0 and advance current path
                        self.warps[wid].cores[cid].registers[10] = 0;
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("pthread_join") {
                        let cid = self.warps[wid].get_single_core_id();
                        let to_wait = self.warps[wid].cores[cid].registers[10] as usize;
                        let w_to_wait = to_wait / tpw;
                        let c_to_wait = to_wait % tpw;
                        let cp = self.warps[w_to_wait].current_path;

                        let p = self.warps[w_to_wait].get_path_of_core_mut(c_to_wait);
                        if p.fetch_pc == 0 {
                            p.execution_mask.unset(c_to_wait);
                            let is_0 = p.execution_mask == 0;
                            self.warps[wid].paths[pathid].fetch_pc += advance;
                            self.push_idle(to_wait);
                            if is_0 {
                                self.warps[w_to_wait].paths.remove(cp);
                            }
                        }
                    } else if func_name.contains("pthread_barrier_init") {
                        let cid = self.warps[wid].get_single_core_id();
                        let num = self.warps[wid].cores[cid].registers[12];
                        let ptr = self.warps[wid].cores[cid].registers[10];

                        self.barriers.insert(ptr, Barrier {
                            initial_cap:num,
                            current_cap:num,
                        });

                        self.warps[wid].paths[pathid].fetch_pc += advance;
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
                            let mut str_addr = self.warps[wid].cores[i].registers[10] as usize;
                            let mut byte = mem.get_8(str_addr); let mut s = String::new();
                            while byte != 0 {
                                s.push(byte as char);
                                str_addr += 1;
                                byte = mem.get_8(str_addr);
                            }
                            println!("{}", s);
                        }
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("malloc") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let size = self.warps[wid].cores[i].registers[10];
                            let ptr = self.malloc(mem.deref_mut(), size as usize);
                            self.warps[wid].cores[i].registers[10] = ptr as i32;
                        }
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("free") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let ptr = self.warps[wid].cores[i].registers[10];
                            self.free(ptr as usize);
                        }
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("GOMP_parallel") {
                        let ids : Vec<usize> = self.warps[wid].alive_cores_ids().collect();
                        if ids.len() != 1 { panic!("GOMP_parallel() called by more than one thread") }

                        let id = ids[0];
                        let core = &self.warps[wid].cores[id];
                        let function = core.registers[10];
                    } else if func_name.contains("omp_get_num_threads") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let num_warps = self.warps.len();
                            let core = &mut self.warps[wid].cores[i];
                            core.registers[10] = (num_warps * tpw) as i32;
                        }
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("omp_get_thread_num") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let core = &mut self.warps[wid].cores[i];
                            let tid = wid*tpw + i;
                            //println!("core {} omp_get_thread_num", wid);
                            core.registers[10] = tid as i32;
                        }
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("exit") {
                        self.warps[wid].paths[pathid].fetch_pc = 0;
                    } else if func_name.contains("strtol") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let core = &mut self.warps[wid].cores[i];
                            let mut str_addr = core.registers[10];
                            let mut to_parse = String::new();
                            let mut byte = mem.get_8(str_addr as usize);

                            //println!("byte at 0x{:x}", str_addr);

                            while byte != 0 {
                                to_parse.push(byte as char);
                                str_addr += 1;
                                byte = mem.get_8(str_addr as usize);
                            }
        
                            //println!("strtol(\"{}\")", to_parse);
                            core.registers[10] = to_parse.parse()
                                .expect(format!("couldnt parse {} to int", to_parse).as_str());
                        }

                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else if func_name.contains("fwrite") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let core = &mut self.warps[wid].cores[i];
                            let file_desc = core.registers[13];
                            let mut str_addr = core.registers[10];
                            let mut to_write = String::new();
                            let mut byte = mem.get_8(str_addr as usize);
                            while byte != 0 {
                                to_write.push(byte as char);
                                str_addr += 1;
                                byte = mem.get_8(str_addr as usize);
                            }
                            match file_desc {
                                0 => print!("{}", to_write),
                                2 => eprint!("{}", to_write),
                                _ => panic!("Unknown fd"),
                            };
                        }
                    } else if func_name.contains("printf") {
                        println!("<printf>");
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    } else {
                        self.warps[wid].paths[pathid].fetch_pc += advance;
                    }
                } else {
                    self.warps[wid].execute(mem.deref_mut())
                }
            } else {
                self.warps[wid].execute(mem.deref_mut())
            }
        //let new14 = self.warps[wid].cores[0].registers[14];
        //if old14 != new14 { println!("0x{:x} th[{}].a4 changed from {:x} to {:x} because of {}", pc, wid, old14, new14, i) }
        }

        let new_gp = self.warps[0].cores[0].registers[3];
        if old_gp != new_gp { panic!("gp changed from {} to {}", old_gp, new_gp) }
    }

    fn get_i_register_of(&self, coreid:usize, id:usize) -> i32 {
        let tpw = self.warps[0].cores.len();
        let wid = coreid / tpw;
        let cid = coreid % tpw;
        return self.warps[wid].cores[cid].registers[id]
    }

    fn set_i_register_of(&mut self, coreid:usize, id:usize, value:i32) {
        let tpw = self.warps[0].cores.len();
        let wid = coreid / tpw;
        let cid = coreid % tpw;
        self.warps[wid].cores[cid].registers[id] = value
    }

    fn get_pc_of(&self, coreid:usize) -> i32 {
        let tpw = self.warps[0].cores.len();
        let wid = coreid / tpw;
        let cid = coreid % tpw;

        for path in &self.warps[wid].paths {
            if path.execution_mask.at(cid) {
                return path.fetch_pc
            }
        }

        0
    }

    fn set_pc_of(&mut self, coreid:usize, value:i32) {
        let tpw = self.warps[0].cores.len();
        let wid = coreid / tpw;
        let cid = coreid % tpw;
        for pid in 0..self.warps[wid].paths.len() {
            let ex = &self.warps[wid].paths[pid].execution_mask;
            if ex.at(cid) {
                let new_mask : BitVec = BitSet::singleton(cid);
                let modified_mask = ex & !new_mask;

                self.warps[wid].paths.push(Path::from_pc_mask(value, new_mask));
                self.warps[wid].paths[pid].execution_mask = modified_mask;
                return
            }
        }

        self.idle_threads.remove_item(&coreid);
        self.warps[wid].paths.push(Path::from_pc_mask(value, BitSet::singleton(cid)));
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
