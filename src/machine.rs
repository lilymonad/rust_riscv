use types::MachineInteger;
use isa::{Instruction, OpCode, CsrId, CsrField};
use memory::Memory;

/// This trait represent the minimal implementation of a RISC-V Machine.
/// It needs to give access to integer registers and CSR registers.
pub trait RiscvIMachine {
    type IntegerType : MachineInteger;

    /// A single clock cycle
    fn cycle(&mut self);

    fn get_i_register(&self, id:usize) -> Self::IntegerType;
    fn set_i_register(&mut self, id:usize, value:Self::IntegerType);

    /// As this function is the `get` counterpart of `set_pc()`, it needs to return
    /// the right PC (in pipelined simulators there are multiple "PCs").
    /// This function returns the PC of the instruction we are fetching.
    fn get_pc(&self) -> Self::IntegerType;

    /// This function is crucial as it is used in helpers such as `raise_exception()`.
    /// It is used to set the PC of the fetched instruction. When calling `cycle()`
    /// the PC set by this function will be used to get the next instruction to be
    /// executed.
    fn set_pc(&mut self, value:Self::IntegerType);

    /// Gets a CSR Field's value. As CSR Fields are bit slices never wider than
    /// `XLEN`, we return an `XLEN`-wide number with `bitN` of the `XLEN` number
    /// corresponding to `bitN` of the CSR Field.
    fn get_csr_field(&self, id:CsrField) -> Self::IntegerType;

    /// Sets a CSR Field's value. As CSR Fields are bit slices never wider than
    /// `XLEN`, the parameter is a `XLEN`-wide number with `bitN` of the parameter
    /// corresponding to `bitN` of the CSR Field.
    fn set_csr_field(&mut self, id:CsrField, value:Self::IntegerType);

    /// Gets privilege level of the processor. `0b00, 0b01, 0b11` correspond
    /// respectively to `Machine`, `Supervisor`, and `User` privilege.
    fn get_privilege(&self) -> u8;

    /// Sets privilege level of the processor. `0b00, 0b01, 0b11` correspond
    /// respectively to `Machine`, `Supervisor`, and `User` privilege.
    fn set_privilege(&mut self, privilege : u8);

    /// This function is a helper function to access CSR with CSRRx instructions.
    /// Many CSR fields are placed in the same CSR , but with different 
    /// access privileges. The best example is `mstatus` CSR which contains many
    /// Machine-level fields, but also Supervisor-level fields which can be
    /// accessed with the `sstatus` CSR.
    // TODO finish full implementation (e.g. unnamed counters)
    fn get_csr(&self, id:CsrId) -> Option<Self::IntegerType> {

        // prevent lower privilege accesses
        let prv = self.get_privilege();
        if prv < id.level() { return None }

        match id {
            CsrId::MISA =>
                Some((self.get_csr_field(CsrField::MXL) << (Self::IntegerType::XLEN - 2)) |
                 self.get_csr_field(CsrField::Extensions)),
            CsrId::MARCHID => Some(self.get_csr_field(CsrField::ArchitectureID)),
            CsrId::MVENDORID => {
                Some((self.get_csr_field(CsrField::Bank) << 7) |
                 self.get_csr_field(CsrField::Offset))
            },
            CsrId::MIMPID => Some(self.get_csr_field(CsrField::Implementation)),
            CsrId::MHARTID => Some(self.get_csr_field(CsrField::HartID)),
            CsrId::MSTATUS => {
                let base =
                    (self.get_csr_field(CsrField::TSR) << 22) |
                    (self.get_csr_field(CsrField::TW) << 21) |
                    (self.get_csr_field(CsrField::TVM) << 20) |
                    (self.get_csr_field(CsrField::MPRV) << 17) |
                    (self.get_csr_field(CsrField::MPP) << 11) |
                    (self.get_csr_field(CsrField::MPIE) << 7) |
                    (self.get_csr_field(CsrField::MIE) << 3) |
                    self.get_csr(CsrId::SSTATUS).unwrap();
                Some(if Self::IntegerType::XLEN > 32 {
                    (self.get_csr_field(CsrField::SXL) << 34) |
                    (self.get_csr_field(CsrField::UXL) << 32) |
                    base
                } else {
                    base
                })
            },
            CsrId::MTVEC => {
                Some((self.get_csr_field(CsrField::MTVecBASE) << 2) |
                self.get_csr_field(CsrField::MTVecMODE))
            },
            CsrId::MEDELEG => Some(self.get_csr_field(CsrField::SynchronousExceptions)),
            CsrId::MIDELEG => Some(self.get_csr_field(CsrField::Interrupts)),
            CsrId::MIP => {
                Some((self.get_csr_field(CsrField::MEIP) << 11) |
                (self.get_csr_field(CsrField::MTIP) << 7) |
                (self.get_csr_field(CsrField::MSIP) << 3) |
                 self.get_csr(CsrId::SIP).unwrap())
            },
            CsrId::MIE => {
                Some((self.get_csr_field(CsrField::MEIE) << 11) |
                (self.get_csr_field(CsrField::MTIE) << 7) |
                (self.get_csr_field(CsrField::MSIE) << 3) |
                 self.get_csr(CsrId::SIE).unwrap())
            },
            CsrId::MCYCLE => { 
                let prv = self.get_privilege();
                let permS = self.get_csr_field(CsrField::MCYEN);
                let permU = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && permS == one
                    || prv == 0b00 && permS == one && permU == one {
                    Some(self.get_csr_field(CsrField::MCYCLE))
                } else {
                    None
                }
            },
            CsrId::MCYCLEH => {
                let prv = self.get_privilege();
                let permS = self.get_csr_field(CsrField::MCYEN);
                let permU = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && permS == one
                    || prv == 0b00 && permS == one && permU == one {
                        Some(
                if Self::IntegerType::XLEN == 32 {
                    self.get_csr_field(CsrField::MCYCLEH) >> 32
                } else { Self::IntegerType::from(0) })
                } else { None }
            },
            CsrId::MINSTRET => {
                let prv = self.get_privilege();
                let permS = self.get_csr_field(CsrField::MCYEN);
                let permU = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && permS == one
                    || prv == 0b00 && permS == one && permU == one {
                Some(self.get_csr_field(CsrField::MINSTRET))
                } else { None }
            },
            CsrId::MINSTRETH => {
                let prv = self.get_privilege();
                let permS = self.get_csr_field(CsrField::MCYEN);
                let permU = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && permS == one
                    || prv == 0b00 && permS == one && permU == one {
                    Some(
                    if Self::IntegerType::XLEN == 32 {
                        self.get_csr_field(CsrField::MINSTRETH) >> 32
                    } else { Self::IntegerType::from(0) })
                } else { None }
            },
            CsrId::MCOUNTEREN => {
                Some((self.get_csr_field(CsrField::MHPMEN) << 3) |
                (self.get_csr_field(CsrField::MIREN) << 2) |
                (self.get_csr_field(CsrField::MTMEN) << 1) |
                 self.get_csr_field(CsrField::MCYEN))
            },
            CsrId::MCOUNTINHIBIT => {
                Some((self.get_csr_field(CsrField::MHPMIN) << 3) |
                (self.get_csr_field(CsrField::MIRIN) << 2) |
                (self.get_csr_field(CsrField::MTMIN) << 1) |
                 self.get_csr_field(CsrField::MCYIN))
            },
            CsrId::MSCRATCH => Some(self.get_csr_field(CsrField::MSCRATCH)),
            CsrId::MEPC => Some(self.get_csr_field(CsrField::MEPC)),
            CsrId::MCAUSE => {
                Some((self.get_csr_field(CsrField::MCauseInterrupt)
                    << (Self::IntegerType::XLEN - 1)) |
                 self.get_csr_field(CsrField::MCauseCode))
            },
            CsrId::MTVAL => Some(self.get_csr_field(CsrField::MTVAL)),
            CsrId::SSTATUS => {
                let base =
                    (self.get_csr_field(CsrField::SD) <<
                        (Self::IntegerType::XLEN - 1)) |
                    (self.get_csr_field(CsrField::MXR ) << 19) |
                    (self.get_csr_field(CsrField::SUM ) << 18) |
                    (self.get_csr_field(CsrField::XS) << 15) |
                    (self.get_csr_field(CsrField::FS) << 13) |
                    (self.get_csr_field(CsrField::SPP) << 8) |
                    (self.get_csr_field(CsrField::SPIE) << 5) |
                    (self.get_csr_field(CsrField::UPIE) << 4) |
                    (self.get_csr_field(CsrField::SIE) << 1) |
                    (self.get_csr_field(CsrField::UIE ) << 0);
                Some(if Self::IntegerType::XLEN > 32 {
                    (self.get_csr_field(CsrField::UXL) << 32) | base
                } else {
                    base
                })
            },
            CsrId::STVEC => {
                Some((self.get_csr_field(CsrField::STVecBASE) << 2) |
                self.get_csr_field(CsrField::STVecMODE))
            },
            CsrId::SIP => {
                Some((self.get_csr_field(CsrField::SEIP) << 9) |
                (self.get_csr_field(CsrField::UEIP) << 8) |
                (self.get_csr_field(CsrField::STIP) << 5) |
                (self.get_csr_field(CsrField::UTIP) << 4) |
                (self.get_csr_field(CsrField::SSIP) << 1) |
                 self.get_csr_field(CsrField::USIP))
            },
            CsrId::SIE => {
                Some((self.get_csr_field(CsrField::SEIE) << 9) |
                (self.get_csr_field(CsrField::UEIE) << 8) |
                (self.get_csr_field(CsrField::STIE) << 5) |
                (self.get_csr_field(CsrField::UTIE) << 4) |
                (self.get_csr_field(CsrField::SSIE) << 1) |
                 self.get_csr_field(CsrField::USIE))
            },
            CsrId::SCOUNTEREN => {
                Some((self.get_csr_field(CsrField::SHPMEN) << 3) |
                (self.get_csr_field(CsrField::SIREN) << 2) |
                (self.get_csr_field(CsrField::STMEN) << 1) |
                 self.get_csr_field(CsrField::SCYEN))
            },
            CsrId::SSCRATCH => Some(self.get_csr_field(CsrField::SSCRATCH)),
            CsrId::SEPC => Some(self.get_csr_field(CsrField::SEPC)),
            CsrId::SCAUSE => {
                Some((self.get_csr_field(CsrField::SCauseInterrupt)
                    << (Self::IntegerType::XLEN - 1)) |
                 self.get_csr_field(CsrField::SCauseCode))
            },
            CsrId::STVAL => Some(self.get_csr_field(CsrField::STVAL)),
            CsrId::SATP => {
                let tvm = self.get_csr_field(CsrField::TVM);
                let one = Self::IntegerType::from(1);
                if tvm == one { None } else {
                    Some((self.get_csr_field(CsrField::MODE) << 31) |
                    (self.get_csr_field(CsrField::ASID) << 22) |
                     self.get_csr_field(CsrField::PPN))
                }
            },
            _ => Some(Self::IntegerType::from(0)),
        }
    }


    /// Setter for CSR registers. This function has a default definition using
    /// `set_csr_field()`. By default, we test for privilege level, access mode
    /// (WARL/WLRL/RO/RW), and we take care or setting bit fields at the right
    /// offset in the register.
    // TODO finish implementation
    fn set_csr(&mut self, id:CsrId, value:Self::IntegerType) -> Option<()> {
        let prv = self.get_privilege();
        let xlen = Self::IntegerType::XLEN as usize;
        if prv < id.level() || id.mode() == 0b11 { return None }
        match id {
            CsrId::MSTATUS => {
                self.set_csr(CsrId::SSTATUS, value);
                self.set_csr_field(CsrField::TSR, value.bit_slice(23, 22));
                self.set_csr_field(CsrField::TW, value.bit_slice(22, 21));
                self.set_csr_field(CsrField::TVM, value.bit_slice(21, 20));
                self.set_csr_field(CsrField::MPRV, value.bit_slice(18, 17));
                self.set_csr_field(CsrField::MPP, value.bit_slice(13, 11));
                self.set_csr_field(CsrField::MPIE, value.bit_slice(8, 7));
                self.set_csr_field(CsrField::MIE, value.bit_slice(4, 3));
                Some(())
            },
            CsrId::MEDELEG => { self.set_csr_field(CsrField::SynchronousExceptions, value); Some(()) },
            CsrId::MIDELEG => { self.set_csr_field(CsrField::Interrupts, value); Some(()) },
            CsrId::SIP => {
                self.set_csr_field(CsrField::USIP, value.bit_slice(1, 0));
                self.set_csr_field(CsrField::SSIP, value.bit_slice(2, 1));
                self.set_csr_field(CsrField::UTIP, value.bit_slice(5, 4));
                self.set_csr_field(CsrField::STIP, value.bit_slice(6, 5));
                self.set_csr_field(CsrField::UEIP, value.bit_slice(9, 8));
                self.set_csr_field(CsrField::SEIP, value.bit_slice(10, 9));
                Some(())
            },
            CsrId::SIE => {
                self.set_csr_field(CsrField::USIE, value.bit_slice(1, 0));
                self.set_csr_field(CsrField::SSIE, value.bit_slice(2, 1));
                self.set_csr_field(CsrField::UTIE, value.bit_slice(5, 4));
                self.set_csr_field(CsrField::STIE, value.bit_slice(6, 5));
                self.set_csr_field(CsrField::UEIE, value.bit_slice(9, 8));
                self.set_csr_field(CsrField::SEIE, value.bit_slice(10, 9));
                Some(())
            },
            CsrId::MTVEC => {
                self.set_csr_field(CsrField::MTVecMODE, value.bit_slice(2, 0));
                self.set_csr_field(CsrField::MTVecBASE, value.bit_slice(31, 2));
                Some(())
            },
            CsrId::MEPC => { self.set_csr_field(CsrField::MEPC, value); Some(()) },
            CsrId::SSTATUS => {
                self.set_csr_field(CsrField::MXR, value.bit_slice(20, 19));
                self.set_csr_field(CsrField::SUM, value.bit_slice(19, 18));
                self.set_csr_field(CsrField::SPP, value.bit_slice(9, 8));
                self.set_csr_field(CsrField::SPIE, value.bit_slice(6, 5));
                self.set_csr_field(CsrField::SIE, value.bit_slice(2, 1));
                Some(())
            },
            CsrId::STVEC => {
                self.set_csr_field(CsrField::STVecMODE, value.bit_slice(2, 0));
                self.set_csr_field(CsrField::STVecBASE, value.bit_slice(31, 2));
                Some(())
            },
            CsrId::SEPC => { self.set_csr_field(CsrField::SEPC, value); Some(()) },
            CsrId::SCAUSE => {
                self.set_csr_field(CsrField::SCauseCode, value.bit_slice(xlen-1, 0));
                self.set_csr_field(CsrField::SCauseInterrupt, value.bit_slice(xlen, xlen-1));
                Some(())
            },
            CsrId::STVAL => { self.set_csr_field(CsrField::STVAL, value); Some(()) },
            CsrId::MIP => {
                self.set_csr(CsrId::SIP, value);
                self.set_csr_field(CsrField::MSIP, value.bit_slice(4, 3));
                self.set_csr_field(CsrField::MTIP, value.bit_slice(8, 7));
                self.set_csr_field(CsrField::MEIP, value.bit_slice(12, 11));
                Some(())
            },
            CsrId::MIE => {
                self.set_csr(CsrId::SIE, value);
                self.set_csr_field(CsrField::MSIE, value.bit_slice(4, 3));
                self.set_csr_field(CsrField::MTIE, value.bit_slice(8, 7));
                self.set_csr_field(CsrField::MEIE, value.bit_slice(12, 11));
                Some(())
            },
            CsrId::SATP => {
                let tvm = self.get_csr_field(CsrField::TVM);
                let prv = self.get_privilege();
                let one = Self::IntegerType::from(1);
                if prv < 0b11 && tvm == one { None }
                else {
                    Some(())
                }
            },
            _ => { Some(()) },
        }
    }

    /// This function is the default implementation of the way an exception
    /// is raised in RISC-V. It only needs to have some CSR Fields implemented
    /// and a way to set the privilege level and the PC of the processor.
    /// This function is used whenever the processor implementation needs to
    /// raise an exception (e.g. missaligned or illegal instruction)
    fn raise_exception(&mut self, is_interrupt : bool
                       , code : i32
                       , info : Self::IntegerType
                       , pc : Self::IntegerType) {
        let medeleg = self.get_csr_field(CsrField::SynchronousExceptions);
        let mideleg = self.get_csr_field(CsrField::Interrupts);
        let from = Self::IntegerType::from;
        let deleg_e = !is_interrupt && (medeleg & from(1 << code)) != from(0);
        let deleg_i = is_interrupt && (mideleg & from(1 << code)) != from(0);
        let old_priv = self.get_privilege();
        if old_priv < 0b11 && (deleg_e || deleg_i) {
            let addr = self.get_csr_field(CsrField::STVecBASE);
            self.set_privilege(0b01);
            self.set_csr_field(CsrField::STVAL, info);
            self.set_csr_field(CsrField::SPP, from(old_priv as i32));
            self.set_csr_field(CsrField::SEPC, pc);
            self.set_csr_field(CsrField::SCauseInterrupt, from(is_interrupt as i32));
            self.set_csr_field(CsrField::SCauseCode, from(code));
            let sie = self.get_csr_field(CsrField::SIE);
            self.set_csr_field(CsrField::SPIE, sie);
            self.set_csr_field(CsrField::SIE, from(0));
            self.set_pc(addr << 2);
        } else {
            let addr = self.get_csr_field(CsrField::MTVecBASE);
            self.set_privilege(0b11);
            self.set_csr_field(CsrField::MTVAL, info);
            self.set_csr_field(CsrField::MPP, from(old_priv as i32));
            let mie = self.get_csr_field(CsrField::MIE);
            self.set_csr_field(CsrField::MPIE, mie);
            self.set_csr_field(CsrField::MIE, from(0));
            self.set_csr_field(CsrField::MEPC, pc);
            self.set_csr_field(CsrField::MCauseInterrupt, from(is_interrupt as i32));
            self.set_csr_field(CsrField::MCauseCode, from(code));
            self.set_pc(addr << 2);
        }
    }
}

/// Represent the data which we need to send to the [write back] step
struct WriteBackData {
    pub perform: bool,
    pub rd: usize,
    pub value: i32,
}

enum WordSize {
    B = 1,
    H = 2,
    W = 4,
    D = 8,
}

impl From<u8> for WordSize {
    /// Helper to create a WordSize out of an u8
    fn from(s:u8) -> WordSize {
        match s {
            1 => WordSize::B,
            2 => WordSize::H,
            4 => WordSize::W,
            _ => WordSize::D,
        }
    }
}

enum MemAction {
    Load,
    Store,
}

/// Represent the data which we need to send to the [mem] step
/// It also contains information to forward to the next step ([write back])
struct MemData {
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
struct PipelineState {
    pub pc: i32,
    pub instruction: Instruction,
}

impl PipelineState {
    fn empty() -> PipelineState {
        PipelineState { pc: 0, instruction: Instruction(0) }
    }
}

pub struct RV32IMachine {
    registers: [i32; 31],
    pc: i32,

    if2dc: PipelineState,
    dc2ex: PipelineState,
    ex2mem: MemData,
    mem2wb: WriteBackData,

    memory: Box<dyn Memory>,
}

impl RiscvIMachine for RV32IMachine {
    type IntegerType = i32;

    fn set_privilege(&mut self, _p : u8) { }
    fn get_privilege(&self) -> u8 { 0b11 }

    fn cycle(&mut self) {
        self.do_write_back();
        self.do_mem();
        self.do_execute();
        self.do_decode();
        self.do_fetch();
    }

    fn get_i_register(&self, i:usize) -> i32 {
        self.get_register(i)
    }

    fn set_i_register(&mut self, i:usize, value:i32) {
        self.set_register(i, value)
    }

    fn get_csr_field(&self, _i:CsrField) -> i32 { 0 }
    fn set_csr_field(&mut self, _i:CsrField, _value:i32) {
    }

    fn get_pc(&self) -> i32 { self.pc }
    fn set_pc(&mut self, value:i32) { self.pc = value }
}

impl RV32IMachine {

    pub fn new(mem:Box<dyn Memory>) -> RV32IMachine {
        RV32IMachine {
            registers : [0; 31],
            pc: 0, 
            if2dc: PipelineState::empty(),
            dc2ex: PipelineState::empty(),
            ex2mem: MemData { pc: 0, wb_rd: 0, wb_perform: false, perform: None, 
                addr: 0, size: WordSize::B, value: 0 },
            mem2wb: WriteBackData { perform: false, rd: 0, value: 0 },
            memory: mem,
        }
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

    /// Executes a pipeline cycle
    pub fn cycle(&mut self) {
        // We perform operation in reverse order to simulate a pipeline. Each
        // step must execute something based on previously computed last step.
        self.do_write_back();
        self.do_mem();
        self.do_execute();
        self.do_decode();
        self.do_fetch()
    }

    fn do_write_back(&mut self) {
        if self.mem2wb.perform {
            let rd = self.mem2wb.rd;
            let value = self.mem2wb.value;
            self.set_register(rd, value)
        }
    }

    fn do_mem(&mut self) {
        let value : i32;
        let perform_wb : bool;
        let rd: usize = self.ex2mem.wb_rd;

        match &self.ex2mem.perform {
            Some(MemAction::Load) => {
                perform_wb = true;
                value = match self.ex2mem.size {
                    WordSize::B => self.memory.get_8(self.ex2mem.addr) as i32,
                    WordSize::H => self.memory.get_16(self.ex2mem.addr) as i32,
                    WordSize::W => self.memory.get_32(self.ex2mem.addr) as i32,
                    _ => 0,
                };
            },
            Some(MemAction::Store) => {
                let addr = self.ex2mem.addr;
                let val  = self.ex2mem.value;
                match self.ex2mem.size {
                    WordSize::B => self.memory.set_8(addr, val as u8),
                    WordSize::H => self.memory.set_16(addr, val as u16),
                    WordSize::W => self.memory.set_32(addr, val as u32),
                    _ => { },
                };
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
        if self.ex2mem.wb_perform {
            self.do_write_back()
        }
    }

    fn do_execute(&mut self) {
        let curr_pc = self.dc2ex.pc;
        let mut to_mem = MemData { pc: curr_pc, wb_perform: false, wb_rd: 0
            , value: 0, perform: None, addr: 0, size: WordSize::B };
        let i = self.dc2ex.instruction;
        let mut illegal = false;
        match i.get_opcode_enum() {
            OpCode::LUI => {
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;
                to_mem.value = i.get_imm_u();
            },
            OpCode::AUIPC => {
                self.pc = curr_pc + i.get_imm_u();
            },
            OpCode::JAL => {
                to_mem.value = curr_pc.wrapping_add(4);
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;
                self.pc = curr_pc.wrapping_add(i.get_imm_j());
            },
            OpCode::JALR => {
                to_mem.value = curr_pc.wrapping_add(4);
                to_mem.wb_perform = true;
                to_mem.wb_rd = i.get_rd() as usize;
                self.pc = self.get_register(i.get_rs1() as usize).wrapping_add(i.get_imm_i());
            },
            OpCode::BRANCH => {
                let npc = curr_pc.wrapping_add(i.get_imm_b());
                
                let v1 = self.get_register(i.get_rs1() as usize);
                let uv1 = v1 as u32;

                let v2 = self.get_register(i.get_rs2() as usize);
                let uv2 = v2 as u32;

                self.pc = match i.get_funct3() {
                    0b000 => if  v1 ==  v2 { npc } else { self.pc }, // BEQ
                    0b001 => if  v1 !=  v2 { npc } else { self.pc }, // BNE
                    0b010 => if  v1 <   v2 { npc } else { self.pc }, // BLT
                    0b011 => if  v1 >=  v2 { npc } else { self.pc }, // BGE
                    0b100 => if uv1 <  uv2 { npc } else { self.pc }, // BLTU
                    0b101 => if uv1 >= uv2 { npc } else { self.pc }, // BGEU
                    _ => self.pc,
                }
            },
            OpCode::LOAD => {
                let width = WordSize::from(i.get_funct3());
                let base = self.get_register(i.get_rs1() as usize) as usize;
                to_mem.perform = Some(MemAction::Load);
                to_mem.addr = i.get_imm_i() as usize + base;
                to_mem.size = width;
            },
            OpCode::STORE => {
                let width = WordSize::from(i.get_funct3());
                let base = self.get_register(i.get_rs1() as usize) as usize;
                let src = self.get_register(i.get_rs2() as usize);
                to_mem.perform = Some(MemAction::Store);
                to_mem.addr = i.get_imm_s() as usize + base;
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
                    0b0000001 => match i.get_funct3() {
                        _ => 0, // TODO handle M extension (mul/div)
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
                                        self.set_pc(self.get_csr(CsrId::SEPC).unwrap());
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
                        let csr = CsrId(i.get_imm_i() as u16);
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
                        let csr = CsrId(i.get_imm_i() as u16);
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
                        let csr = CsrId(i.get_imm_i() as u16);
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
                        let csr = CsrId(i.get_imm_i() as u16);
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
                        let csr = CsrId(i.get_imm_i() as u16);
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
                        let csr = CsrId(i.get_imm_i() as u16);
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

    fn do_decode(&mut self) {
        self.dc2ex = self.if2dc
    }

    fn do_fetch(&mut self) {
        if self.pc % 4 != 0 { self.raise_exception(false, 0, 0, self.pc); }
        let i = Instruction(self.memory.get_32(self.pc as usize));
        self.if2dc = PipelineState { pc: self.pc, instruction: i };
        self.pc += 4
    }
}
