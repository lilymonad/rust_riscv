use machine::IntegerMachine;
use isa::{Instruction, OpCode, CsrId, CsrField};
use memory::Memory;

/// Represent the data which we need to send to the `write back` step
#[derive(Debug)]
pub struct WriteBackData {
    pub perform: bool,
    pub rd: usize,
    pub value: i32,
}

pub enum WordSize {
    B = 0,
    H = 1,
    W = 2,
    D = 4,
}

impl From<u8> for WordSize {
    /// Helper to create a WordSize out of an u8
    fn from(s:u8) -> WordSize {
        match s {
            0 => WordSize::B,
            1 => WordSize::H,
            2 => WordSize::W,
            _ => WordSize::D,
        }
    }
}

pub enum MemAction {
    Load,
    Store,
}

/// Represent the data which we need to send to the `mem` step
/// It also contains information to forward to the next step (`write back`)
pub struct MemData {
    pub pc: i32,

    /// data forwarding from ex stage
    pub wb_perform: bool,
    pub wb_rd: usize,

    /// used as union for either WB value or Store value
    pub value: i32,

    /// data needed to perform the load/store
    pub perform: Option<MemAction>,
    pub addr: usize,
    pub size: WordSize,
}

#[derive(Copy, Clone)]
pub struct PipelineState {
    pub pc: i32,
    pub instruction: Instruction,
}

impl PipelineState {
    pub fn empty() -> PipelineState {
        PipelineState { pc: 0, instruction: Instruction(0) }
    }
}

pub struct Machine {
    pub registers: [i32; 31],
    pc: i32,

    pub if2dc: PipelineState,
    pub dc2ex: PipelineState,
    pub ex2mem: MemData,
    pub mem2wb: WriteBackData,

    csr_file: [i32; 4096],
}

impl IntegerMachine for Machine {
    type IntegerType = i32;

    fn set_privilege(&mut self, _p : u8) { }
    fn get_privilege(&self) -> u8 { 0b11 }

    fn cycle(&mut self, mem : &mut dyn Memory) {
        self.do_write_back();
        self.do_mem(mem);
        self.do_execute();
        self.do_decode();
        self.do_fetch(mem);
    }

    fn get_i_register(&self, i:usize) -> i32 {
        self.get_register(i)
    }

    fn set_i_register(&mut self, i:usize, value:i32) {
        self.set_register(i, value)
    }

    fn get_csr_field(&self, i:CsrField) -> i32 {
        let x = self.csr_file[i.get_csr_id() as usize];
        (x & (i.mask::<i32>() as i32)) >> i.offset::<i32>()
    }

    fn set_csr_field(&mut self, i:CsrField, value:i32) {
        let num : &mut i32 = &mut self.csr_file[i.get_csr_id() as usize];
        let mask : i32 = i.mask();
        let notmask = !mask;

        *num = (*num & notmask) | (mask & (value << i.offset::<i32>()))
    }
    

    fn get_pc(&self) -> i32 { self.pc }
    fn set_pc(&mut self, value:i32) { self.pc = value }

    fn finished(&self) -> bool { self.pc == 0 }
}

impl Machine {

    pub fn new() -> Machine {
        let mut ret = Machine {
            csr_file: [0; 4096],
            registers : [0; 31],
            pc: 0, 
            if2dc: PipelineState::empty(),
            dc2ex: PipelineState::empty(),
            ex2mem: MemData { pc: 0, wb_rd: 0, wb_perform: false, perform: None, 
                addr: 0, size: WordSize::B, value: 0 },
            mem2wb: WriteBackData { perform: false, rd: 0, value: 0 },
        };

        ret.set_csr(CsrId::MISA, 0x40002000);
        ret
    }

    pub fn get_register(&self, i:usize) -> i32 {
        if i <= 0 || i > 31 {
            0
        } else {
            self.registers[i-1]
        }
    }

    pub fn set_register(&mut self, i:usize, x:i32) {
        // TODO implement exceptions when writing to r0
        if i > 0 && i < 32 {
            self.registers[i-1] = x
        }
    }

    pub fn do_write_back(&mut self) {
        if self.mem2wb.perform {
            let rd = self.mem2wb.rd;
            let value = self.mem2wb.value;
            self.set_register(rd, value)
        }
    }

    pub fn do_mem(&mut self, mem: &mut dyn Memory) {
        let value : i32;
        let perform_wb : bool;
        let rd: usize = self.ex2mem.wb_rd;

        match &self.ex2mem.perform {
            Some(MemAction::Load) => {
                perform_wb = true;
                value = match self.ex2mem.size {
                    WordSize::B => mem.get_8(self.ex2mem.addr) as i32,
                    WordSize::H => mem.get_16(self.ex2mem.addr) as i32,
                    WordSize::W => mem.get_32(self.ex2mem.addr) as i32,
                    _ => 0,
                };
            },
            Some(MemAction::Store) => {
                let addr = self.ex2mem.addr;
                let val  = self.ex2mem.value;
                match self.ex2mem.size {
                    WordSize::B => mem.set_8(addr, val as u8),
                    WordSize::H => mem.set_16(addr, val as u16),
                    WordSize::W => mem.set_32(addr, val as u32),
                    _ => { },
                }
                perform_wb = false;
                value = 0
            },
            None => {
                perform_wb = self.ex2mem.wb_perform;
                value = self.ex2mem.value;
            }
        }

        self.mem2wb = WriteBackData { perform: perform_wb, value: value, rd: rd };

        // bypass
        if self.mem2wb.perform {
            self.do_write_back()
        }
    }

    pub fn do_execute(&mut self) {
        let curr_pc = self.dc2ex.pc;
        let mut to_mem = MemData { pc: curr_pc, wb_perform: false, wb_rd: 0
            , value: 0, perform: None, addr: 0, size: WordSize::B };
        let i = self.dc2ex.instruction;
        let mut illegal = false;

        let (i, advance) = if i.is_compressed() { (i.uncompressed(), 2) } else { (i, 4) };

        match i.get_opcode_enum() {
            OpCode::LUI => {
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;
                to_mem.value = i.get_imm_u();
            },
            OpCode::AUIPC => {
                self.pc = curr_pc + i.get_imm_u();
                self.if2dc = PipelineState::empty();
                self.dc2ex = PipelineState::empty()
            },
            OpCode::JAL => {
                to_mem.value = curr_pc.wrapping_add(4);
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;
                self.pc = curr_pc.wrapping_add(i.get_imm_j());
                self.if2dc = PipelineState::empty();
                self.dc2ex = PipelineState::empty()
            },
            OpCode::JALR => {
                to_mem.value = curr_pc.wrapping_add(4);
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;
                self.pc = self.get_register(i.get_rs1() as usize)
                    .wrapping_add(i.get_imm_i());
                self.if2dc = PipelineState::empty();
                self.dc2ex = PipelineState::empty()
            },
            OpCode::BRANCH => {
                let  tpc = curr_pc.wrapping_add(i.get_imm_b());
                let ntpc = curr_pc.wrapping_add(advance);
                
                let r1 = i.get_rs1() as usize;
                let v1 = self.get_register(r1);
                let uv1 = v1 as u32;

                let r2 = i.get_rs2() as usize;
                let v2 = self.get_register(r2);
                let uv2 = v2 as u32;

                self.pc = match i.get_funct3() {
                    0b000 => if  v1 ==  v2 { tpc } else { ntpc }, // BEQ
                    0b001 => if  v1 !=  v2 { tpc } else { ntpc }, // BNE
                    0b100 => if  v1 <   v2 { tpc } else { ntpc }, // BLT
                    0b101 => if  v1 >=  v2 { tpc } else { ntpc }, // BGE
                    0b110 => if uv1 <  uv2 { tpc } else { ntpc }, // BLTU
                    0b111 => if uv1 >= uv2 { tpc } else { ntpc }, // BGEU
                    _ => curr_pc,
                };

                if self.pc == tpc {
                    self.if2dc = PipelineState::empty();
                    self.dc2ex = PipelineState::empty()
                }
            },
            OpCode::LOAD => {
                let width = WordSize::from(i.get_funct3());
                let base = self.get_register(i.get_rs1() as usize) as usize;
                to_mem.perform = Some(MemAction::Load);
                to_mem.addr = (i.get_imm_i() as usize).wrapping_add(base);
                to_mem.size = width;
                to_mem.wb_rd = i.get_rd() as usize;
            },
            OpCode::STORE => {
                let width = WordSize::from(i.get_funct3());
                let base = self.get_register(i.get_rs1() as usize) as usize;
                let src = self.get_register(i.get_rs2() as usize);
                to_mem.perform = Some(MemAction::Store);
                to_mem.addr = (i.get_imm_s() as usize).wrapping_add(base);
                to_mem.size = width;
                to_mem.value = src;
            },
            OpCode::OPIMM => {
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;

                let v1 = self.get_register(i.get_rs1() as usize);
                let v2 = if i.get_funct3() & 0b11 == 1 { i.get_rs2() as i32 }
                         else { i.get_imm_i() };

                to_mem.value = match i.get_funct3() {
                    0b000 => v1.wrapping_add(v2),
                    0b010 => (v1 < v2) as i32,
                    0b011 => ((v1 as u32) < v2 as u32) as i32,
                    0b100 => v1 ^ v2,
                    0b110 => v1 | v2,
                    0b111 => v1 & v2,
                    0b001 => v1 << v2,
                    0b101 => if i.get_funct7() != 0 { v1 >> v2 }
                             else { ((v1 as u32) >> v2) as i32 },
                    _ => 0, // Cannot be here, because funct3 is on 3 bits
                };
            },
            OpCode::OPREG => {
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;

                let v1 = self.get_register(i.get_rs1() as usize);
                let v2 = self.get_register(i.get_rs2() as usize);
                let uv1 = v1 as u32;
                let uv2 = v2 as u32;
                let v1_64 = v1 as i64;
                let v2_64 = v2 as i64;
                let uv1_64 = uv1 as u64;
                let uv2_64 = uv2 as u64;

                let allset = 0xFFFFFFFFu32 as i32;

                to_mem.value = match i.get_funct7() {
                    0b0000000 => match i.get_funct3() {
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
                    0b0000001 => match i.get_funct3() { // M Extension
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
                    0b0100000 => match i.get_funct3() {
                        0b000 => v1.wrapping_sub(v2),
                        0b101 => v1 >> v2,
                        _ => 0, // TODO handle bad funct3 values
                    },
                    _ => 0, // TODO add other extensions (F has priority)
                };

            },
            OpCode::SYSTEM => {
                match i.get_funct3() {
                    0b000 => {
                        match i.get_funct7() {
                            0b0000000 => { // ECALL, EBREAK, URET ...
                                match i.get_rs2() {
                                    0b00000 => { /* ECALL */
                                        self.raise_exception(false, self.get_privilege() as i32 + 8, 0, curr_pc);
                                        self.dc2ex = PipelineState::empty();
                                        self.if2dc = PipelineState::empty();
                                    },
                                    0b00001 => { /* EBREAK */
                                        self.raise_exception(false, 3, 0, curr_pc);
                                        self.dc2ex = PipelineState::empty();
                                        self.if2dc = PipelineState::empty();
                                    },
                                    0b00010 => { /* URET */ 
                                        let mpie = self.get_csr_field(CsrField::UPIE);
                                        self.set_csr_field(CsrField::UIE, mpie);
                                        self.set_csr_field(CsrField::UPIE, 1);
                                        self.set_pc(self.get_csr(CsrId::UEPC).unwrap());
                                    },
                                    _ => { }
                                }
                            },
                            0b0001000 => { // SRET
                                match i.get_rs2() {
                                    0b00010 => { /* SRET */
                                        let tsr = self.get_csr_field(CsrField::TSR);
                                        let prv = self.get_privilege();
                                        if prv < 0b01 || prv == 0b01 && tsr == 1 {
                                            illegal = true
                                        } else {
                                            let mpp = self.get_csr_field(CsrField::SPP);
                                            let mpie = self.get_csr_field(CsrField::SPIE);
                                            self.set_csr_field(CsrField::SIE, mpie);
                                            self.set_csr_field(CsrField::SPIE, 1);
                                            self.set_csr_field(CsrField::SPP, 0);
                                            self.set_privilege(mpp as u8);
                                            self.set_pc(self.get_csr(CsrId::SEPC).unwrap());
                                        }
                                    },
                                    0b00101 => { /* TODO WFI */ },
                                    _ => { }
                                }
                            },
                            0b0011000 => { // MRET
                                match i.get_rs2() {
                                    0b00010 => {
                                        if self.get_privilege() < 0b11 {
                                            illegal = true
                                        } else {
                                            let mpp = self.get_csr_field(CsrField::MPP);
                                            let mpie = self.get_csr_field(CsrField::MPIE);
                                            self.set_csr_field(CsrField::MIE, mpie);
                                            self.set_csr_field(CsrField::MPIE, 1);
                                            self.set_csr_field(CsrField::MPP, 0);
                                            self.set_privilege(mpp as u8);
                                            self.set_pc(self.get_csr(CsrId::MEPC).unwrap());
                                        }
                                    },
                                    _ => { }
                                }
                            },
                            _ => {}
                        }
                    },
                    0b001 => { /* CSRRW */
                        let csr = CsrId::from(i.get_imm_i() as u16);
                        let rs1 = i.get_rs1() as usize;
                        let rd = i.get_rd() as usize;

                        illegal = 
                            self.get_csr(csr).and_then(| v | {
                                to_mem.wb_rd = rd;
                                to_mem.wb_perform = true;
                                to_mem.value = v;
                                
                                self.set_csr(csr, self.get_i_register(rs1))
                            }).is_none();
                    },
                    0b010 => { /* CSRRS */
                        let csr = CsrId::from(i.get_imm_i() as u16);
                        let rs1 = i.get_rs1() as usize;
                        let rd = i.get_rd() as usize;

                        illegal =
                            self.get_csr(csr).and_then(| v | {
                                to_mem.wb_rd = rd;
                                to_mem.wb_perform = true;
                                to_mem.value = v;

                                self.set_csr(csr, v | self.get_i_register(rs1))
                            }).is_none();
                    },
                    0b011 => { /* CSRRC */ 
                        let csr = CsrId::from(i.get_imm_i() as u16);
                        let rs1 = i.get_rs1() as usize;
                        let rd = i.get_rd() as usize;

                        illegal =
                            self.get_csr(csr).and_then(| v | {
                                to_mem.wb_rd = rd;
                                to_mem.wb_perform = true;
                                to_mem.value = v;

                                self.set_csr(csr, v & !self.get_i_register(rs1))
                            }).is_none();
                    },
                    0b101 => { /* CSRRWI */
                        let csr = CsrId::from(i.get_imm_i() as u16);
                        let rs1 = i.get_rs1() as usize;
                        let rd = i.get_rd() as usize;

                        illegal = 
                            self.get_csr(csr).and_then(| v | {
                                to_mem.wb_rd = rd;
                                to_mem.wb_perform = true;
                                to_mem.value = v;
                                
                                self.set_csr(csr, rs1 as i32)
                            }).is_none();
                    },
                    0b110 => { /* CSRRSI */
                        let csr = CsrId::from(i.get_imm_i() as u16);
                        let rs1 = i.get_rs1() as usize;
                        let rd = i.get_rd() as usize;

                        illegal = 
                            self.get_csr(csr).and_then(| v | {
                                to_mem.wb_rd = rd;
                                to_mem.wb_perform = true;
                                to_mem.value = v;
                                
                                self.set_csr(csr, v | (rs1 as i32))
                            }).is_none();
                    },
                    0b111 => { /* CSRRCI */
                        let csr = CsrId::from(i.get_imm_i() as u16);
                        let rs1 = i.get_rs1() as usize;
                        let rd = i.get_rd() as usize;

                        illegal = 
                            self.get_csr(csr).and_then(| v | {
                                to_mem.wb_rd = rd;
                                to_mem.wb_perform = true;
                                to_mem.value = v;
                                
                                self.set_csr(csr, v | !(rs1 as i32))
                            }).is_none();
                    },
                    _ => {}
                }
            },
            _ => {}
        }

        if illegal {
            self.raise_exception(false, 2, 0, curr_pc);
            self.dc2ex = PipelineState::empty();
            self.if2dc = PipelineState::empty();
        }

        self.ex2mem = to_mem
    }

    pub fn do_decode(&mut self) {
        self.dc2ex = self.if2dc
    }

    pub fn do_fetch(&mut self, mem:&mut dyn Memory) {
        if self.pc % 2 != 0 { self.raise_exception(false, 0, 0, self.pc); }

        let first = mem.get_16(self.pc as usize) as u32;

        let ic = Instruction(first);

        let (advance, i) =
            if ic.is_compressed() {
                (2, ic)
            } else {
                let second = mem.get_16((self.pc + 2) as usize) as u32;
                (4, Instruction((second << 16) | first))
            };

        println!("fetched {}", i);
        self.if2dc = PipelineState { pc: self.pc, instruction: i };
        self.pc += advance
    }
}
