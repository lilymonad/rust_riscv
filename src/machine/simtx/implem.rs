use machine::{
    MultiCoreIMachine,
};
use machine::simtx::scheduler::SimtxScheduler;
use isa::{Instruction, OpCode, CsrId};
use memory::*;
use types::{MachineInteger, BitSet, BoolIterator};
use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
    fmt,
    ops::DerefMut,
    collections::{HashMap, BTreeMap},
};

type BitVec = u32;
pub static MAX_TPW : usize = core::mem::size_of::<BitVec>() * 8;

/// Defines the state of a single hardware thread.
#[derive(Clone)]
pub struct Core {
    pub registers: [ i32; 32 ],
    pub fregisters: [ f32; 32 ],
}

/// Defines a SIMT Path. As threads are grouped in `Warp`s executed in lockstep,
/// we handle divergence by remembering where all threads are with a
/// `(fetch_pc, execution_mask)` tuple. Before fetching instructions, we chose
/// a `Path` to advance.
#[derive(Clone, Copy, Debug)]
pub struct Path {
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
        self.execution_mask.bits().ones().count() == 1
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(0x{:x}, {:b})", self.fetch_pc, self.execution_mask)
    }
}

#[derive(Debug, Clone)]
pub enum BranchOutcome<BV:BitSet> {
    Uniform(bool, BV),
    Divergent(BV, BV),
}

#[derive(Debug, Clone)]
pub struct CondBranchData {
    times_passed:usize,
    taken_hist:Vec<BranchOutcome<BitVec>>,
}

/// Defines a hardware warp (a group of threads) which all execute instructions
/// in an SIMD fasion.
#[derive(Clone)]
pub struct Warp<S:SimtxScheduler> {
    pub cores: Vec<Core>,
    pub paths: Vec<Path>,
    pub current_path: usize,
    pub cycles_since_last_schedule: usize,

    // Log variables
    pub branch_mask_hist: HashMap<i32, Vec<BitVec>>,
    pub thresholds: usize,
    pub fusions: usize,
    pub cond_branch_data: HashMap<i32, CondBranchData>,
    scheduler:PhantomData<S>,
}

impl<S:SimtxScheduler> Warp<S> {
    pub fn new(tpw:usize) -> Warp<S> {
        let mut cores = Vec::new();
        cores.resize(tpw, Core { registers : [ 0; 32 ], fregisters: [ 0.0; 32 ] });
        Warp {
            cores,
            paths: Vec::new(),
            current_path: 0,
            branch_mask_hist: HashMap::new(),
            thresholds: 0,
            fusions: 0,
            cond_branch_data: HashMap::new(),
            cycles_since_last_schedule: 0,
            scheduler:PhantomData,
        }
    }

    pub fn _get_path_of_core_mut(&mut self, cid:usize) -> Option<&mut Path> {
        for p in &mut self.paths {
            if p.execution_mask.at(cid) { return Some(p) }
        }

        None
    }

    pub fn _get_path_of_core(&self, cid:usize) -> Option<&Path> {
        for p in &self.paths {
            if p.execution_mask.at(cid) { return Some(p) }
        }

        None
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



    fn probas(&self) -> Vec<f32> {
        let ps = &self.paths;

        let raw : Vec<f32> = ps
            .into_iter()
            .enumerate()
            .map(|(i,p)| {
                ps
                    .into_iter()
                    .enumerate()
                    .filter(|(j,_)| i != *j)
                    .fold(0., |v, (j,pp)| {
                        let decrease_factor = 1;
                        v + 1. / ((pp.fetch_pc as f32) - p.fetch_pc as f32)
                            .abs()
                            .powi(decrease_factor)
                    })
            }).collect();

        let total : f32 = (&raw).into_iter().sum();
        raw
            .into_iter()
            .map(|v| v/total)
            .collect()
    }



    /// This function should be called right before any FETCH step of the `Warp`
    /// to ensure we always execute a valid path.
    ///
    /// This function sets the `current_path` of the `Warp` correcly according
    /// to the scheduling rule, but also fusion paths with the same PC.
    pub fn schedule_path(&mut self) {


        //**TODO:
        //* avoir une boite "priorite" qui calcule la prio de scheduling des chemins
        //* definir les bons criteres pour cette boite
        //*
        //* scheduler avec une "fenetre de temps" qu'on peuple et parcour en fct de cette
        //* fonction de probabilite/priorite
        //*/

        S::schedule(self)
    }

    /// This function is a helper used to work on all alive threads of the
    /// `current_path`.
    pub fn for_each_core_alive<T:FnMut(&mut Core)->()>(&mut self, mut f:T) {
        let ex = self.paths[self.current_path].execution_mask;
        for i in ex.bits().ones() {
            f(&mut self.cores[i as usize]);
        }
    }

    pub fn _cores(&self) -> impl Iterator<Item=&Core> {
        let ex = self.paths[self.current_path].execution_mask;
        self.cores.iter().enumerate().filter_map(move |(i, c)| {
            if ex.at(i) { Some(c) } else { None }
        })
    }

    pub fn cores_mut(&mut self) -> impl Iterator<Item=&mut Core> {
        let ex = self.paths[self.current_path].execution_mask;
        self.cores.iter_mut().enumerate().filter_map(move |(i, c)| {
            if ex.at(i) { Some(c) } else { None }
        })
    }

    /// Same as `for_each_core_alive()` but with the ID of the core.
    fn for_each_core_alive_i<T:FnMut(usize, &mut Core)->()>(&mut self, mut f:T) {
        let ex = self.paths[self.current_path].execution_mask;
        for i in ex.bits().ones() {
            f(i as usize, &mut self.cores[i as usize])
        }
    }

    /// Returns an iterator going through all alive cores IDs in order.
    pub fn alive_cores_ids(&self) -> impl Iterator<Item=usize> {
        self.paths[self.current_path].execution_mask.bits().ones().map(|id| id as usize)
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
        let mask = path.execution_mask;
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
                for core in self.cores_mut() {
                    core.registers[inst.get_rd() as usize] = inst.get_imm_u();
                }
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
                    let old_pc = self.paths[self.current_path].fetch_pc;
                    self.paths.remove(self.current_path);
                    for (pc, mask) in nph {
                        if old_pc == pc { self.current_path = self.paths.len() }
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
                        0b000 => { v1 ==  v2 }, // BEQ
                        0b001 => { v1 !=  v2 }, // BNE
                        0b100 => { v1 <   v2 }, // BLT
                        0b101 => { v1 >=  v2 }, // BGE
                        0b110 => { uv1 <  uv2 }, // BLTU
                        0b111 => { uv1 >= uv2 }, // BGEU
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

                let outcome = 
                        if !not_taken_mask.any() {
                            BranchOutcome::Uniform(true, taken_mask)
                        } else if !taken_mask.any() {
                            BranchOutcome::Uniform(false, not_taken_mask)
                        } else {
                            BranchOutcome::Divergent(taken_mask, not_taken_mask)
                        };
                if let Some(dat) = self.cond_branch_data.get_mut(&pc) {
                    dat.times_passed += 1;
                    dat.taken_hist.push(outcome);
                } else {
                    let taken_hist = vec![outcome];
                    let to_push = CondBranchData { times_passed:1, taken_hist };
                    self.cond_branch_data.insert(pc, to_push);
                }

                update_pc = false
            },
            OpCode::LOAD => {
                let width = inst.get_funct3();
                self.for_each_core_alive(|core| {
                    let rbase = inst.get_rs1() as usize;
                    let base = core.registers[rbase];
                    let imm = inst.get_imm_i();
                    //println!("{:x}(r{}) + {:x} = {:x}", base, inst.get_rs1(), imm, base.wrapping_add(imm));

                    let addr = (base.wrapping_add(imm) as usize) & 0xffffffff;

                    let value = match width {
                            0 => mem.get_8(addr) as i32,
                            1 => mem.get_16(addr) as i32,
                            2 => mem.get_32(addr) as i32,
                            _ => panic!("LOAD: bad word width"), // ERROR
                        };
                    core.registers[inst.get_rd() as usize] = value;
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
                    };
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
                        0b000 => v1.wrapping_add(v2),              // ADDI
                        0b010 => (v1 < v2) as i32,                 // SLTI
                        0b011 => ((v1 as u32) < v2 as u32) as i32, // SLTIU
                        0b100 => v1 ^ v2,  // XORI
                        0b110 => v1 | v2,  // ORI
                        0b111 => v1 & v2,  // ANDI
                        0b001 => v1 << v2, // SLLI
                        0b101 => if inst.get_funct7() != 0 { v1 >> v2 } // SRAI
                                 else { ((v1 as u32) >> v2) as i32 },   // SRAIU
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
                            0b001 => v1 << v2, // SLL
                            0b010 => (v1 < v2) as i32, // SLT
                            0b011 => ((v1 as u32) < v2 as u32) as i32, // SLTU
                            0b100 => v1 ^ v2, // XOR
                            0b101 => ((v1 as u32) >> v2) as i32, // SRL
                            0b110 => v1 | v2, // OR
                            0b111 => v1 & v2, // AND
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
                            0b000 => v1.wrapping_sub(v2), // SUB
                            0b101 => v1 >> v2, // SRA
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
            self.update_branch_hist(pc, mask)
        }
    }
}

impl<S:SimtxScheduler> fmt::Display for Warp<S> {
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

#[derive(Debug)]
struct LoopData {
    times_passed:usize,
    num_threads_passed:usize,
}


/// The SIMT-X machine. To handle `pthread` or `omp` system calls, we detect them
/// using plt information, and emulate them.
pub struct Machine<S:SimtxScheduler> {
    // Our cores
    warps:Vec<Warp<S>>,

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

    // For execution analysis
    loop_data: HashMap<i32, LoopData>,

    // 32bits unsigned words for thread stack allocation
    stack_start: usize,
    stack_size: usize,
}

impl<S:SimtxScheduler> Machine<S> {
    pub fn new(tpw:usize, nb_warps:usize, plt_addresses:HashMap<i32, String>) -> Machine<S> {

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
            loop_data:HashMap::new(),

            // default stack size and place
            // it is 128 * 2Kio bytes stacks starting at 0x10000000
            stack_start: 0x20000000,
            stack_size: 0x00200000,
        }
    }

    pub fn place_stack(&mut self, text_end:usize, stack_size:usize) {
        self.stack_start =
            text_end +
            self.warps.len() * self.warps[0].cores.len() * stack_size;
        self.stack_size = stack_size;
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

    pub fn pop_first_idle(&mut self) -> usize {
        self.idle_threads.pop().expect("No more threads")
    }

    fn push_idle(&mut self, thread:usize) {
        self.idle_threads.push(thread)
    }

    fn clean_idle(&mut self) {
        let tpw = self.warps[0].cores.len();

        // for each warp
        for wi in 0..self.warps.len() {
            // Filter out idle path (with fetch_pc == 0)
            // and re-push idle threads into the idle pool
            let mut new_path = self.warps[wi].current_path;
            let new_paths = self.warps[wi].paths.clone().into_iter().enumerate().filter_map(|(i,p)| {
                if p.fetch_pc == 0 {
                    if i == new_path { new_path = 0xFFFFFFFF }
                    for i in p.execution_mask.bits().ones() {
                        self.push_idle(wi * tpw + i as usize)
                    }
                    None
                } else {
                    Some(p)
                }
            });

            self.warps[wi].paths = new_paths.collect();
            self.warps[wi].current_path = new_path;
        }
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
            for (pc, hist) in &warp.cond_branch_data {
                println!("\t0x{:x}", pc);
                for outcome in &hist.taken_hist {
                    match outcome {
                        BranchOutcome::Uniform(taken, mask) => {
                            let s : String = mask.bits().map(|b| {
                                if b { if *taken { 'A' } else { 'B' } } else { ' ' }
                            }).collect();
                            println!("{}", s);
                        },
                        BranchOutcome::Divergent(tm, ntm) => {
                            let s : String = tm.bits().zip(ntm.bits())
                                .map(|(t,nt)| {
                                    if t { 'A' } else if nt { 'B' } else { ' ' }
                                }).collect();
                            println!("{}", s);
                        },
                    }
                }
            }
            println!("threshold reached {} times", warp.thresholds);
            println!("paths merged {} times", warp.fusions);
        }
        println!("detected loops:");
        for (end, start) in &self.detected_loops {
            println!("{:08x} -> {:08x}", start, end)
        }
        for (pc, stats) in &self.loop_data {
            println!("{:08x}: {:?}", pc, stats);
        }
    }

    fn free_barrier(&mut self, barr:i32, advance:i32) {
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
                    warp.paths[pid].fetch_pc += advance;
                    
                    if bv_barr.any() {
                        warp.paths.push(Path::from_pc_mask(pc, bv_barr));
                    }
                }
            }
        }
    }
}

impl<S:SimtxScheduler> MultiCoreIMachine for Machine<S> {
    type IntegerType = i32;

    fn step(&mut self, mem:Arc<Mutex<dyn Memory + std::marker::Send>>) {
        let mut mem = mem.lock().unwrap();
        let tpw = self.warps[0].cores.len();

        let old_gp = self.warps[0].cores[0].registers[3];
        for wid in 0..self.warps.len() {
            self.clean_idle();
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

            //println!("warp {} mask {:x} 0x{:x} :: {}", wid, self.warps[wid].paths[pathid].execution_mask, pc, i);
        
            // Update back-branch stats
            if i.get_opcode_enum() == OpCode::BRANCH || (i.get_opcode_enum() == OpCode::JAL && i.get_rd() == 0) {
                if i.jump_offset() < 0 {
                    let num_threads_passed = self.warps[wid]
                            .paths[pathid].execution_mask.bits().ones().count();
                    self.detected_loops.insert(pc, pc+i.jump_offset());
                    if let Some(dat) = self.loop_data.get_mut(&pc) {
                        dat.times_passed += 1;
                        dat.num_threads_passed += self.warps[wid]
                            .paths[pathid].execution_mask.bits().ones().count();
                    } else {
                        let dat = LoopData { times_passed: 1, num_threads_passed };
                        self.loop_data.insert(pc, dat);

                    }
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

                        let stacksize = self.stack_size;
                        let stackstart = self.stack_start - stacksize * tid; 
                        let stackend = stackstart - stacksize;
                        mem.allocate_at(stackend, stacksize);

                        let cid = self.warps[wid].get_single_core_id();
                        // write in memory the tid
                        let addr = self.warps[wid].cores[cid].registers[10] as usize;
                        mem.set_32(addr, tid as u32);

                        // setup allocated core's register file
                        let mut regs = [0;32];
                        regs[2] = stackstart as i32;
                        regs[8] = stackstart as i32;
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
                        if self.idle_threads.contains(&to_wait) {
                            self.warps[wid].paths[pathid].fetch_pc += advance;
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
                                    self.free_barrier(ptr, advance);
                                    break;
                                }
                            }
                        }
                    } else if func_name.contains("puts") || func_name.contains("printf") {
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
                        let _function = core.registers[10];
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
                            //println!("core {} omp_get_thread_num = {}", wid, tid);
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
        
                            let parsed = to_parse.parse()
                                .expect(format!("couldnt parse {} to int", to_parse).as_str());
                            //println!("strtol(\"{}\") = {}", to_parse, parsed);

                            core.registers[10] = parsed;
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
            } else if i.get_opcode_enum() == OpCode::SYSTEM {
                let csr = CsrId::from((i.get_imm_i() & 0xfff) as u16);
                //let rs1 = i.get_rs1() as usize;
                let rd = i.get_rd() as usize;
                self.warps[wid].for_each_core_alive_i(|i, c| {
                    let v = match csr {
                        CsrId::MHARTID => { i + wid*tpw },
                        _ => 0,
                    };
                    println!("csrr {:?} = {}", csr, v);
                    c.registers[rd] = v as i32;
                });
                self.warps[wid].paths[pathid].fetch_pc += advance;
            } else {
                self.warps[wid].execute(mem.deref_mut())
            }
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
