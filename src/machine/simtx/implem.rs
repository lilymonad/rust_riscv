use machine::{
    MultiCoreIMachine,
};
use machine::simtx::scheduler::SimtxScheduler;
use isa::{Instruction, OpCode, CsrId};
use memory::*;
use types::{MachineInteger, BitSet, BoolIterator};
use std::{
    sync::{Arc, Mutex},
    fmt,
    ops::DerefMut,
    collections::{HashMap, BTreeMap},
    fs::{File, OpenOptions},
    io::{Write, Read, BufReader, BufRead},
    os::unix::fs::FileExt,
};

type BitVec = u32;
pub const MAX_TPW : usize = core::mem::size_of::<BitVec>() * 8;

#[repr(C)]
#[derive(Clone, Copy)]
struct TwoF32 {
    hi:f32,
    lo:f32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct SplitU64 {
    hi:u32,
    lo:u32,
}

impl SplitU64 {
    fn from_u64(bits:u64) -> SplitU64 {
        let hi = (bits >> 32) as u32;
        let lo = bits as u32;
        SplitU64 { hi, lo }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union MachineF32 {
    double:f64,
    float:TwoF32,
    bits:SplitU64,
}

impl MachineF32 {
    fn new() -> Self { Self::from_u64(0) }
    fn from_u64(bits:u64) -> Self { Self { bits: { SplitU64::from_u64(bits) } } }
    fn from_f32(float:f32) -> Self {
        let mut ret = Self { float: TwoF32 { hi:0f32, lo:float } };
        ret.bits.hi = 0xFFFFFFFF;
        ret
    }
    fn from_f64(double:f64) -> Self { Self { double } }
}

/// Defines the state of a single hardware thread.
#[derive(Clone)]
pub struct Core {
    pub registers: [ i32; 32 ],
    pub fregisters: [ MachineF32; 32 ],
}

impl Core {
    fn set_f32_register(&mut self, reg:usize, value:f32) {
        self.fregisters[reg] = MachineF32::from_f32(value);
    }
    fn get_f32_register(&mut self, reg:usize) -> f32 {
        unsafe { self.fregisters[reg].float.lo }
    }
    fn set_f64_register(&mut self, reg:usize, value:f64) {
        self.fregisters[reg].double = value
    }
    fn get_f64_register(&self, reg:usize) -> f64 {
        unsafe { self.fregisters[reg].double }
    }
    fn set_ri(&mut self, reg:usize, value:i32) {
        if reg == 5 {
            println!("WRITE {:x} TO T0", value);
        }
        self.registers[reg] = value
    }
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

impl CondBranchData {
    fn new() -> Self { Self { times_passed : 0, taken_hist : Vec::new() } }
}

/// Defines a hardware warp (a group of threads) which all execute instructions
/// in an SIMD fasion.
#[derive(Clone)]
pub struct Warp<S:SimtxScheduler> {
    pub cores: Vec<Core>,
    pub paths: Vec<Path>,
    pub current_path: Option<usize>,
    pub cycles_since_last_schedule: usize,

    // Log variables
    pub branch_mask_hist: HashMap<i32, Vec<BitVec>>,
    pub thresholds: usize,
    pub fusions: usize,
    pub cond_branch_data: HashMap<i32, CondBranchData>,

    // Scheduler black box 
    pub scheduler:S,
    pub schedule_invalidated:bool,
}

impl<S:SimtxScheduler> Warp<S> {
    pub fn new(tpw:usize) -> Warp<S> {
        let mut cores = Vec::new();
        cores.resize(tpw, Core { registers : [ 0; 32 ], fregisters: [ MachineF32::new(); 32 ] });
        Warp {
            schedule_invalidated:true,
            cores,
            paths: Vec::new(),
            current_path: None,
            branch_mask_hist: HashMap::new(),
            thresholds: 0,
            fusions: 0,
            cond_branch_data: HashMap::new(),
            cycles_since_last_schedule: 0,
            scheduler:S::default(),
        }
    }

    pub fn _get_path_of_core_mut(&mut self, cid:usize) -> Option<&mut Path> {
        self.paths.iter_mut().filter(|p| p.execution_mask.at(cid)).next()
    }

    pub fn _get_path_of_core(&self, cid:usize) -> Option<&Path> {
        self.paths.iter().filter(|p| p.execution_mask.at(cid)).next()
    }

    pub fn get_single_core_id(&self) -> usize {
        self.paths[self.current_path.unwrap()].execution_mask
            .bits()
            .ones()
            .map(|i| i as usize)
            .next()
            .expect("Current path is empty")
    }

    fn _probas(&self) -> Vec<f32> {
        let ps = &self.paths;

        let raw : Vec<f32> = ps
            .into_iter()
            .enumerate()
            .map(|(i,p)| {
                ps
                    .into_iter()
                    .enumerate()
                    .filter(|(j,_)| i != *j)
                    .fold(0., |v, (_,pp)| {
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
    pub fn schedule_path(&mut self) -> Option<usize> {


        //**TODO: scheduling priority timing window
        //* avoir une boite "priorite" qui calcule la prio de scheduling des chemins
        //* definir les bons criteres pour cette boite
        //*
        //* scheduler avec une "fenetre de temps" qu'on peuple et parcour en fct de cette
        //* fonction de probabilite/priorite
        //*/

        S::schedule(self)
    }

    pub fn cores(&self) -> impl Iterator<Item=(usize, &Core)> {
        let ex = self.paths[self.current_path.unwrap()].execution_mask;
        self.cores.iter().enumerate().filter(move |(i,_)| { ex.at(*i) })
    }

    pub fn cores_mut(&mut self) -> impl Iterator<Item=(usize, &mut Core)> {
        let ex = self.paths[self.current_path.unwrap()].execution_mask;
        self.cores.iter_mut().enumerate().filter(move |(i,_)| ex.at(*i))
    }

    /// Returns an iterator going through all alive cores IDs in order.
    pub fn alive_cores_ids(&self) -> impl Iterator<Item=usize> {
        self.paths[self.current_path.unwrap()].execution_mask.bits().ones().map(|id| id as usize)
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
        if self.current_path.is_none() { return }
        let pid = self.current_path.unwrap();
        let mask : u32 = self.paths[pid].execution_mask;
        let pc : i32 = self.paths[pid].fetch_pc;
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
                for (_, core) in self.cores_mut() {
                    core.set_ri(inst.get_rd() as usize, inst.get_imm_u());
                }
            },
            OpCode::AUIPC => { // direct jumps are always uniform
                let value = pc.wrapping_add(inst.get_imm_u());
                for (_, core) in self.cores_mut() {
                    core.set_ri(inst.get_rd() as usize, value)
                }
            },
            OpCode::JAL => {
                if inst.get_rd() != 0 {
                    for (_, core) in self.cores_mut() {
                        core.set_ri(inst.get_rd() as usize, pc.wrapping_add(advance));
                    }
                }
                self.advance_pc(pid, inst.get_imm_j());
                update_pc = false
            },
            OpCode::JALR => { // indirect jump can be divergent multiple times
                let mut nph : HashMap<i32, BitVec> = HashMap::new();

                // Compute new self.paths[pid]s based on the new thread PCs
                for (i, core) in self.cores_mut() {
                    let new_pc = inst.get_imm_i().
                        wrapping_add(core.registers[inst.get_rs1() as usize]);
                    if let Some(bv) = nph.get_mut(&new_pc) {
                        bv.set(i);
                    } else {
                        nph.insert(new_pc, BitVec::singleton(i));
                    }
                    if inst.get_rd() != 0 {
                        core.set_ri(inst.get_rd() as usize, pc.wrapping_add(advance));
                    }
                }

                // Check if it's a uniform jump
                // and just update the pc of the current self.paths[pid] if it is
                if nph.len() == 1 {
                    self.set_pc(pid, *nph.keys().next().unwrap());
                } else {
                    // If not, create as many self.paths[pid]s as needed and inject them
                    let old_pc = self.paths[pid].fetch_pc;
                    self.remove_path(pid);
                    for (pc, mask) in nph {
                        if old_pc == pc { self.current_path = Some(self.paths.len()) }
                        self.push_path(Path::from_pc_mask(pc, mask));
                    }
                }

                update_pc = false
            },
            OpCode::BRANCH => { // conditional branch
                let  tpc = pc.wrapping_add(inst.get_imm_b());
                let ntpc = pc.wrapping_add(advance);

                let mut taken_mask = 0;

                // compute taken/not_taken masks for each alive thread
                for (i, core) in self.cores_mut() {
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
                }

                let not_taken_mask = (!taken_mask) & self.paths[self.current_path.unwrap()].execution_mask;

                // update self.paths[pid], and add new paths if divergent
                if !not_taken_mask.any() {    // uniform taken
                    self.set_pc(pid, tpc);
                } else if !taken_mask.any() { // uniform not taken
                    self.set_pc(pid, ntpc);
                } else {                      // divergent
                    self.remove_path(self.current_path.unwrap());
                    self.push_path(Path::from_pc_mask(tpc, taken_mask));
                    self.push_path(Path::from_pc_mask(ntpc, not_taken_mask));
                }

                let outcome = 
                        if !not_taken_mask.any() {
                            BranchOutcome::Uniform(true, taken_mask)
                        } else if !taken_mask.any() {
                            BranchOutcome::Uniform(false, not_taken_mask)
                        } else {
                            BranchOutcome::Divergent(taken_mask, not_taken_mask)
                        };

                let dat = self.cond_branch_data.entry(pc).or_insert(CondBranchData::new());
                dat.times_passed += 1;
                dat.taken_hist.push(outcome);

                update_pc = false
            },
            OpCode::LOAD => {
                let width = inst.get_funct3();
                for (_, core) in self.cores_mut() {
                    let rbase = inst.get_rs1() as usize;
                    let base = core.registers[rbase];
                    let imm = inst.get_imm_i();

                    let addr = (base.wrapping_add(imm) as usize) & 0xffffffff;

                    let value = match width {
                            0 => mem.get_8(addr) as i32,
                            1 => mem.get_16(addr) as i32,
                            2 => mem.get_32(addr) as i32,
                            _ => panic!("LOAD: bad word width"), // ERROR
                        };

                    //if pc == 0x10ab8 {
                        println!("{} : loaded {} at {:x}", inst, value, addr);
                    //}
                    core.set_ri(inst.get_rd() as usize, value);
                }
            },
            OpCode::STORE => {
                let width = inst.get_funct3();
                for (_, core) in self.cores_mut() {
                    let base = core.registers[inst.get_rs1() as usize];
                    let addr = (base.wrapping_add(inst.get_imm_s()) as usize) & 0xffffffff;

                    let src = core.registers[inst.get_rs2() as usize];
                    match width {
                        0 => mem.set_8(addr, src as u8),
                        1 => mem.set_16(addr, src as u16),
                        2 => mem.set_32(addr, src as u32),
                        _ => panic!("STORE: Bad word width"), // ERROR
                    };
                    if (pc & 0xfffff0) == 0x011110 {
                        println!("STORE = {:x} AT {:x}", src, addr);
                    }
                }
            },
            OpCode::OPIMM => {
                for (_, core) in self.cores_mut() {
                    let dst = inst.get_rd() as usize;

                    let v1 = core.registers[inst.get_rs1() as usize];
                    let v2 =    if inst.get_funct3() & 0b11 == 1 {
                                    inst.get_rs2() as i32
                                }
                                else { inst.get_imm_i() };

                    core.set_ri(dst, match inst.get_funct3() {
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
                    });
                }
            },
            OpCode::OPREG => {
                for (_, core) in self.cores_mut() {
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

                    core.set_ri(dst, match inst.get_funct7() {
                        0b0000000 => match inst.get_funct3() {
                            0b000 => { let v=v1.wrapping_add(v2); println!("{:x}+{:x}={:x}", v1, v2, v); v },
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
                            _ => unreachable!("OPREG SUB OR SHIFT"),
                        }
                        _ => unreachable!("OPREG FUNCT7"),
                    });
                }
            },
            OpCode::FLW => {
                let width = inst.get_funct3();
                for (_, core) in self.cores_mut() {
                    let rbase = inst.get_rs1() as usize;
                    let base = core.registers[rbase];
                    let imm = inst.get_imm_i();

                    let addr = (base.wrapping_add(imm) as usize) & 0xffffffff;

                    println!("{:x} : {:x}(x{}) + {:x} = {:x}",
                        pc,
                        base,
                        rbase,
                        imm,
                        addr);
                    let value = match width {
                            0 | 1 => unreachable!("LOAD: float values are 32bits wide at least"),
                            2 => MachineF32::from_u64(mem.get_32(addr) as u64),
                            3 => {
                                let mut ret = MachineF32::new();
                                ret.bits.hi = mem.get_32(addr) as u32;
                                ret.bits.lo = mem.get_32(addr+4) as u32;
                                ret
                            },
                            _ => unreachable!("LOAD @ 0x{:x}: illegal word width {}", pc, width),
                        };
                    core.fregisters[inst.get_rd() as usize] = value;
                }
            },
            OpCode::FSW => {
                let width = inst.get_funct3();
                for (_, core) in self.cores_mut() {
                    let base = core.registers[inst.get_rs1() as usize];
                    let addr = (base.wrapping_add(inst.get_imm_s()) as usize) & 0xffffffff;

                    let src = unsafe { core.fregisters[inst.get_rs2() as usize].bits };
                    match width {
                        0 | 1 => unreachable!("STORE: float values are 32bits wide at least"),
                        2 => mem.set_32(addr, src.lo),
                        3 => { mem.set_32(addr, src.hi); mem.set_32(addr+4, src.lo) },
                        _ => unreachable!("STORE: illegal word width {}", width),
                    };
                }
            },
            OpCode::FMADD | OpCode::FMSUB | OpCode::FNMADD | OpCode::FNMSUB => { // FMADD.S
                let dst  = inst.get_rd() as usize;
                let _rm  = inst.get_funct3() as usize;
                let src1 = inst.get_rs1() as usize;
                let src2 = inst.get_rs2() as usize;
                let src3 = inst.get_rs3() as usize;
                let fmt  = inst.get_float_fmt();

                for (_, core) in self.cores_mut() {

                    if fmt == 0b00 {
                        let v1 = core.get_f32_register(src1);
                        let v2 = core.get_f32_register(src2);
                        let v3 = core.get_f32_register(src3);

                        let value = match inst.get_opcode() & 0b1100 {
                            0b0000 => v1*v2+v3,
                            0b0100 => v1*v2-v3,
                            0b1000 => -v1*v2+v3,
                            0b1100 => -v1*v2-v3,
                            _ => unreachable!("F[N]M[ADD|SUB]"),
                        };
                        core.set_f32_register(dst, value);
                    } else if fmt == 0b01 {
                        let v1 = core.get_f64_register(src1);
                        let v2 = core.get_f64_register(src2);
                        let v3 = core.get_f64_register(src3);

                        let value = match inst.get_opcode() & 0b1100 {
                            0b0000 => v1*v2+v3,
                            0b0100 => v1*v2-v3,
                            0b1000 => -v1*v2+v3,
                            0b1100 => -v1*v2-v3,
                            _ => unreachable!("F[N]M[ADD|SUB]"),
                        };
                        core.set_f64_register(dst, value);
                    }
                }
            },
            OpCode::FOPREG => { // FLOAT OPREG
                let funct = inst.get_funct7();
                let d_ext = (funct & 0b1) == 0b1;
                let dst   = inst.get_rd() as usize;
                let rs1   = inst.get_rs1() as usize;
                let rs2   = inst.get_rs2() as usize;
                let rm    = inst.get_funct3();

                for (_, core) in self.cores_mut() {
                    let v32_1 = core.get_f32_register(rs1);
                    let v32_2 = core.get_f32_register(rs2);
                    let v64_1 = core.get_f64_register(rs1);
                    let v64_2 = core.get_f64_register(rs2);

                    match funct & 0b1111110 {
                        0b0000000 => core.set_f32_register(dst, v32_1 + v32_2),
                        0b0000001 => core.set_f64_register(dst, v64_1 + v64_2),
                        0b0000100 => core.set_f32_register(dst, v32_1 - v32_2),
                        0b0000101 => core.set_f64_register(dst, v64_1 - v64_2),
                        0b0001000 => core.set_f32_register(dst, v32_1 * v32_2),
                        0b0001001 => core.set_f64_register(dst, v64_1 * v64_2),
                        0b0001100 => core.set_f32_register(dst, v32_1 / v32_2),
                        0b0001101 => core.set_f64_register(dst, v64_1 / v64_2),
                        0b0101100 => core.set_f32_register(dst, f32::sqrt(v32_1)),
                        0b0101101 => core.set_f64_register(dst, f64::sqrt(v64_1)),
                        0b0010000 => { // "FSGNJ[N|X].S"
                            let mut v1 = core.fregisters[rs1];
                            let v2 = core.fregisters[rs2];
                            unsafe {
                                let sign_bit = match rm {
                                    0b000 => v2.bits.lo, // FSGNJ.S
                                    0b001 => !v2.bits.lo, // FSGNJN.S
                                    0b010 => v1.bits.lo ^ v2.bits.lo, // FSGNJX.S
                                    _ => unreachable!("FOPREG RM BITWISE"),
                                } & 0x80000000;
                                v1.bits.lo = (v1.bits.lo & 0x7FFFFFFF) | sign_bit;
                                core.set_f32_register(dst, v1.float.lo)
                            }
                        },
                        0b0010100 => core.set_f32_register(dst,
                            match rm {
                                0 => f32::min(v32_1, v32_2),
                                1 => f32::max(v32_1, v32_2),
                                _ => unreachable!("FOPREG RM MAXMIN"),
                            }),
                        0b1100000 => {
                            match inst.get_rs2() { // FCVT.W[U].S
                                0b00000 => core.set_ri(dst,
                                    if v32_1 > (std::i32::MAX as f32) {
                                        std::i32::MAX
                                    } else if v32_1 < (std::i32::MIN as f32) {
                                        std::i32::MIN
                                    } else {
                                        v32_1 as i32
                                    }),
                                0b00001 => core.set_ri(dst,
                                    if v32_1 > (std::u32::MAX as f32) {
                                        std::u32::MAX as i32
                                    } else if v32_1 < (std::u32::MIN as f32) {
                                        std::u32::MIN as i32
                                    } else {
                                        v32_1 as i32
                                    }),
                                _ => unreachable!("FOPREG CONV"),
                            }
                        },
                        0b1101000 => { // FCVT.S.W[U]
                            match inst.get_rs2() {
                                0b00000 => core.set_ri(dst, v32_1 as i32),
                                0b00001 => core.set_ri(dst, (v32_1 as u32) as i32),
                                _ => unreachable!("FCVT"),
                            }
                        },
                        0b1110000 => {
                            match inst.get_rs2() {
                                0b00000 => {
                                    //println!("STORING IN REG {}", dst);
                                    unsafe { core.set_ri(dst, core.fregisters[rs1].bits.lo as i32) }
                                },
                                0b00001 => unimplemented!("FCLASS.S"),
                                _ => unreachable!("FCLASS"),
                            }
                        },
                        0b1010000 => {
                            core.set_ri(dst, match inst.get_funct3() {
                                0b000 => { (v32_1 <= v32_2) as i32 }, // LE
                                0b001 => { (v32_1 < v32_2) as i32 }, // LT
                                0b010 => { (v32_1 == v32_2) as i32 }, // EQ
                                _ => unreachable!("FLOAT COMP"),
                            })
                        },
                        0b1111000 => core.fregisters[dst].bits.lo = core.registers[rs1] as u32,
                        0b0100000 => { // FCVT.D.S
                            let rd = inst.get_rd() as usize;
                            let rs = inst.get_rs1() as usize;

                            if d_ext {
                                let rd = inst.get_rd() as usize;
                                let rs = inst.get_rs1() as usize;
                                let v = core.get_f64_register(rs) as f32;
                                core.set_f32_register(rd, v)
                            } else {
                                let v = core.get_f32_register(rs) as f64;
                                core.set_f64_register(rd, v)
                            }
                        },
                        _ => unreachable!("FOPREG FUNCT7"),
                    };
                }
            },

            _ => unimplemented!(),
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

    fn advance_pc(&mut self, pid:usize, advance:i32) {
        let old_pc = self.paths[pid].fetch_pc;
        self.set_pc(pid, old_pc.wrapping_add(advance))
    }

    fn set_pc(&mut self, pid:usize, pc:i32) {
        let mask = self.paths[pid].execution_mask;

        // search for a path already at given pc. if found, update its mask
        // and remove the merged path, invalidating the scheduler state
        for i in 0..self.paths.len() {
            let p = &mut self.paths[i];
            if p.fetch_pc == pc {
                p.execution_mask |= mask;
                self.remove_path(pid);
                return
            }
        }

        // if no merging occured, just modify the path's pc
        self.paths[pid].fetch_pc = pc;
    }

    fn push_path(&mut self, path:Path) {
        // if we already have a path at path.fetch_pc, merge the given mask with
        // the current mask
        for p in &mut self.paths {
            if p.fetch_pc == path.fetch_pc {
                p.execution_mask |= path.execution_mask;
                return
            }
        }
        // if no path are here, just push a new path
        self.paths.push(path)
    }

    fn remove_path(&mut self, pid:usize) {
        self.invalidate();
        self.paths.remove(pid);
        if let Some(curr) = self.current_path {
            if curr >= pid { self.current_path = None }
        }
    }

    fn clean_idles(&mut self, offset:usize) -> Vec<usize> {
        self.current_path = None;
        let mut inv = false;
        let ret = self.paths.drain_filter(|p| {
            let b = p.fetch_pc == 0;
            if b { inv = true }
            b
        })
        .flat_map(|p| p.execution_mask.bits().ones())
        .map(|cid| cid as usize + offset)
        .collect();
        self.schedule_invalidated |= inv;
        ret
    }

    pub fn invalidate(&mut self) {
        self.schedule_invalidated = true
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

impl LoopData {
    fn new() -> Self {
        Self { times_passed : 0, num_threads_passed : 0 }
    }
}

static mut LOOPS : Option<HashMap<i32, i32>> = None;
pub fn loops() -> &'static mut HashMap<i32, i32> {
    if unsafe { LOOPS.is_none() } {
       unsafe { LOOPS = Some(HashMap::new()) }
    }
    unsafe { LOOPS.as_mut().unwrap() }
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

    // For files and IO purposes
    file_handles: BTreeMap<i32, (File, u64)>,
    next_fid: i32,
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

            file_handles: BTreeMap::new(),
            next_fid: 3,
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

    fn clean_idles(&mut self) {
        let tpw = self.warps[0].cores.len();
        let iter = self.warps.iter_mut()
            .enumerate()
            .map(|(i, w)| w.clean_idles(i * tpw))
            .flatten();

        self.idle_threads.extend(iter)
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
//        for wid in 0..self.warps.len() {
//            println!("=== STATS FOR WARP {} ===", wid);
//            let warp = &self.warps[wid];
//            for (pc, hist) in &warp.branch_mask_hist {
//                println!("\t0x{:x}", pc);
//                for bv in hist {
//                    println!("\t[{:032b}]", bv);
//                }
//            }
//            for (pc, hist) in &warp.cond_branch_data {
//                println!("\t0x{:x}", pc);
//                for outcome in &hist.taken_hist {
//                    match outcome {
//                        BranchOutcome::Uniform(taken, mask) => {
//                            let s : String = mask.bits().map(|b| {
//                                if b { if *taken { 'A' } else { 'B' } } else { ' ' }
//                            }).collect();
//                            println!("{}", s);
//                        },
//                        BranchOutcome::Divergent(tm, ntm) => {
//                            let s : String = tm.bits().zip(ntm.bits())
//                                .map(|(t,nt)| {
//                                    if t { 'A' } else if nt { 'B' } else { ' ' }
//                                }).collect();
//                            println!("{}", s);
//                        },
//                    }
//                }
//            }
//            println!("threshold reached {} times", warp.thresholds);
//            println!("paths merged {} times", warp.fusions);
//        }
        println!("detected loops:");
        for (end, start) in &self.detected_loops {
            println!("{:08x} -> {:08x}", start, end)
        }
    }

    pub fn print_relevant_pcs(&self) {
        println!("=== DETECTED LOOPS ===");
        for (end, start) in &self.detected_loops {
            println!("{:08x} -> {:08x}", start, end)
        }
    }

    pub fn print_branch_stats(&self) {
        println!("=== BRANCH STATS ===");
        for (pc, stats) in &self.loop_data {
            println!("{:08x}: {:?}", pc, stats);
        }
    }

    fn free_barrier(&mut self, barr:i32, advance:i32) {
        for wid in 0..self.warps.len() {
            let warp = &mut self.warps[wid];
            let tpw = warp.cores.len();
            let mut pid = 0;
            while pid < warp.paths.len() {
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
                    warp.advance_pc(pid, advance);
                    
                    if bv_barr.any() {
                        warp.push_path(Path::from_pc_mask(pc, bv_barr));
                    }
                }
                pid += 1;
            }
        }
    }
}

impl<S:SimtxScheduler> MultiCoreIMachine for Machine<S> {
    type IntegerType = i32;

    fn step(&mut self, mem:Arc<Mutex<dyn Memory + std::marker::Send>>) {
        let mut mem = mem.lock().unwrap();
        let tpw = self.warps[0].cores.len();

        for wid in 0..self.warps.len() {
            self.clean_idles();
            let pathid = self.warps[wid].schedule_path();

            if pathid.is_none() ||
                self.warps[wid].paths[pathid.unwrap()].fetch_pc == 0 { continue }

            let pathid = pathid.unwrap();
            let pc = self.warps[wid].paths[pathid].fetch_pc;

            let i = Instruction(mem.get_32(pc as usize));

            let (advance, i) = if i.is_compressed() {
                (2, i.uncompressed())
            } else {
                (4, i)
            };

            // DEBUG
            #[cfg(debug_assertions)]
            println!("warp {} mask {:x} 0x{:x} :: {}", wid, self.warps[wid].paths[pathid].execution_mask, pc, i);
        
            // Update back-branch stats
            if i.get_opcode_enum() == OpCode::BRANCH || (i.get_opcode_enum() == OpCode::JAL && i.get_rd() == 0) {
                if i.jump_offset() < 0 {
                    let num_threads_passed = self.warps[wid]
                            .paths[pathid].execution_mask.bits().ones().count();
                    self.detected_loops.insert(pc, pc+i.jump_offset());

                    let dat = self.loop_data.entry(pc).or_insert(LoopData::new());
                    dat.times_passed += 1;
                    dat.num_threads_passed += num_threads_passed;
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
                        regs[10] = self.warps[wid].cores[cid].registers[13];
                        self.warps[w].cores[t].registers = regs;

                        // setup a new path with only allocated thread inside
                        let npc = self.warps[wid].cores[cid].registers[12];
                        let m = BitSet::singleton(t);

                        self.warps[w].push_path(Path::from_pc_mask(npc, m));

                        // return 0 and advance current path
                        self.warps[wid].cores[cid].set_ri(10, 0);
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("pthread_join") {
                        let cid = self.warps[wid].get_single_core_id();
                        let to_wait = self.warps[wid].cores[cid].registers[10] as usize;
                        if self.idle_threads.contains(&to_wait) {
                            self.warps[wid].advance_pc(pathid, advance);
                        }
                    } else if func_name.contains("pthread_barrier_init") {
                        let cid = self.warps[wid].get_single_core_id();
                        let num = self.warps[wid].cores[cid].registers[12];
                        let ptr = self.warps[wid].cores[cid].registers[10];

                        self.barriers.insert(ptr, Barrier {
                            initial_cap:num,
                            current_cap:num,
                        });

                        self.warps[wid].advance_pc(pathid, advance);
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
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("malloc") {
                        for i in self.warps[wid].alive_cores_ids() {
                            print!("MALLOC CALLED!");
                            let size = self.warps[wid].cores[i].registers[10];
                            let ptr = self.malloc(mem.deref_mut(), size as usize);
                            self.warps[wid].cores[i].set_ri(10, ptr as i32);
                            println!(" ADRESSE EST {:x}", ptr);
                        }
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("free") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let ptr = self.warps[wid].cores[i].registers[10];
                            self.free(ptr as usize);
                        }
                        self.warps[wid].advance_pc(pathid, advance);
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
                            core.set_ri(10, (num_warps * tpw) as i32);
                        }
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("omp_get_thread_num") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let core = &mut self.warps[wid].cores[i];
                            let tid = wid*tpw + i;
                            //println!("core {} omp_get_thread_num = {}", wid, tid);
                            core.set_ri(10, tid as i32);
                        }
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("exit") {
                        self.warps[wid].set_pc(pathid, 0);
                    } else if func_name.contains("strtof") {
                        for i in self.warps[wid].alive_cores_ids() {
                            let core = &mut self.warps[wid].cores[i];
                            let mut str_addr = core.registers[10];
                            let mut to_parse = String::new();
                            let mut byte = mem.get_8(str_addr as usize);

                            //println!("byte at 0x{:x}", str_addr);

                            while byte != 0 && byte != ('\n' as u8) {
                                to_parse.push(byte as char);
                                str_addr += 1;
                                byte = mem.get_8(str_addr as usize);
                            }
        
                            //println!("strtof({})", to_parse);
                            let parsed = to_parse.parse()
                                .expect(format!("couldnt parse {} to float", to_parse).as_str());
                            //println!("strtol(\"{}\") = {}", to_parse, parsed);

                            let x : MachineF32 = MachineF32::from_f32(parsed);
                            unsafe { core.set_ri(10, x.bits.lo as i32); }
                        }
                        self.warps[wid].advance_pc(pathid, advance);
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

                            core.set_ri(10, parsed);
                        }
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("fopen") {
                        let cid = self.warps[wid].get_single_core_id();
                        let core = &mut self.warps[wid].cores[wid];
                        let mut addr = core.registers[10] as usize;
                        let mut c = mem.get_8(addr);
                        let mut fname = String::new();
                        while c != 0 {
                            fname.push(c as char);
                            addr += 1;
                            c = mem.get_8(addr);
                        }
                        let mut oo = OpenOptions::new();
                        oo
                            .write(true)
                            .read(true)
                            .create(true);

                        core.set_ri(10, match oo.open(&fname) {
                            Err(_) => 0,
                            Ok(f) => {
                                self.file_handles.insert(self.next_fid
                                    , (f, 0));
                                let ret = self.next_fid;
                                self.next_fid += 1;
                                ret
                            },
                        });

                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("fgets") {
                        let cid = self.warps[wid].get_single_core_id();
                        let core = &mut self.warps[wid].cores[wid];
                        let mut addr = core.registers[10] as usize;
                        let size = core.registers[11] as u64;
                        let fp = core.registers[12];

                        match fp {
                            0 | 2 => panic!("reading from stdout or stderr"),
                            1 => {
                                let mut buf = String::new();
                                std::io::stdin().read_line(&mut buf).unwrap();
                                for byte in buf.bytes() {
                                    mem.set_8(addr, byte);
                                    addr += 1;
                                }
                                mem.set_8(addr, 0);
                            },
                            n => {
                                self.file_handles.get_mut(&n).map(|(file, cur)| {
                                    let mut vec = vec![0;128];
                                    if let Ok(size) = file.read_at(&mut vec, *cur) {
                                        let line =
                                        vec.iter().take_while(|c| {
                                            **c != ('\n' as u8)
                                        });

                                        let mut i = 0;
                                        for b in line {
                                            mem.set_8(addr + i, *b);
                                            i += 1;
                                        }
                                        mem.set_8(addr + i, 0);

                                        *cur += (i+1) as u64;
                                    }
                                });
                            },
                        }

                        self.warps[wid].advance_pc(pathid, advance);
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
                                1 => panic!("writing to stdin"),
                                2 => eprint!("{}", to_write),
                                n => self.file_handles.get_mut(&n).map(|(f,cur)| {
                                    match f.write_at(to_write.as_bytes(), *cur) {
                                        Err(_) => {},
                                        Ok(size) => { *cur += size as u64 },
                                    }
                                }).unwrap(),
                            };
                        }
                        self.warps[wid].advance_pc(pathid, advance);
                    } else if func_name.contains("printf") {
                        println!("<printf>");
                        self.warps[wid].advance_pc(pathid, advance);
                    } else {
                        self.warps[wid].advance_pc(pathid, advance);
                    }
                } else {
                    self.warps[wid].execute(mem.deref_mut())
                }
            } else if i.get_opcode_enum() == OpCode::SYSTEM {
                let csr = CsrId::from((i.get_imm_i() & 0xfff) as u16);
                //let rs1 = i.get_rs1() as usize;
                let rd = i.get_rd() as usize;
                for (i, c) in self.warps[wid].cores_mut() {
                    let v = match csr {
                        CsrId::MHARTID => { i + wid*tpw },
                        _ => 0,
                    };
                    println!("csrr {:?} = {}", csr, v);
                    c.set_ri(rd, v as i32);
                }
                self.warps[wid].advance_pc(pathid, advance);
            } else {
                self.warps[wid].execute(mem.deref_mut())
            }
        }
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
        self.warps[wid].cores[cid].set_ri(id, value)
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

                self.warps[wid].push_path(Path::from_pc_mask(value, new_mask));
                self.warps[wid].paths[pid].execution_mask = modified_mask;
                return
            }
        }

        self.idle_threads.remove_item(&coreid);
        self.warps[wid].push_path(Path::from_pc_mask(value, BitSet::singleton(cid)));
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
