
/// A machine implementing the simplest RVI32 specification
pub mod rv32i;

/// A machine implementing "hardware threads" by emulating pthread library calls
pub mod rv32pthread;

/// An implementation of the SIMT-X machine (SIMT on CPU)
pub mod simtx;

use memory::Memory;
use types::MachineInteger;
use isa::{CsrId, CsrField};

/// This trait represent the minimal implementation of a RISC-V Machine.
/// It needs to give access to integer registers and CSR registers.
pub trait IntegerMachine {
    type IntegerType : MachineInteger;

    /// A single clock cycle
    fn cycle(&mut self, &mut dyn Memory);

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
                let perm_s = self.get_csr_field(CsrField::MCYEN);
                let perm_u = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && perm_s == one
                    || prv == 0b00 && perm_s == one && perm_u == one {
                    Some(self.get_csr_field(CsrField::MCYCLE))
                } else {
                    None
                }
            },
            CsrId::MCYCLEH => {
                let prv = self.get_privilege();
                let perm_s = self.get_csr_field(CsrField::MCYEN);
                let perm_u = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && perm_s == one
                    || prv == 0b00 && perm_s == one && perm_u == one {
                        Some(
                if Self::IntegerType::XLEN == 32 {
                    self.get_csr_field(CsrField::MCYCLEH) >> 32
                } else { Self::IntegerType::from(0) })
                } else { None }
            },
            CsrId::MINSTRET => {
                let prv = self.get_privilege();
                let perm_s = self.get_csr_field(CsrField::MCYEN);
                let perm_u = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && perm_s == one
                    || prv == 0b00 && perm_s == one && perm_u == one {
                Some(self.get_csr_field(CsrField::MINSTRET))
                } else { None }
            },
            CsrId::MINSTRETH => {
                let prv = self.get_privilege();
                let perm_s = self.get_csr_field(CsrField::MCYEN);
                let perm_u = self.get_csr_field(CsrField::SCYEN);
                let one = Self::IntegerType::from(1);
                if prv == 0b11
                    || prv == 0b01 && perm_s == one
                    || prv == 0b00 && perm_s == one && perm_u == one {
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

