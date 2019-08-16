use machine::RiscvIMachine;

/// Base structure of an instruction in the RV32I format
/// (just an unsigned 32bits int)
///
/// For more information, see the RISC-V reference in the repository
#[derive(Debug, Copy, Clone)]
pub struct Instruction(pub u32);

impl Instruction {

    /// Creates a R type RV32I instruction. These are used for operations with
    /// only register operands (e.g. `add r1 r1 r2`).
    ///
    /// # Arguments
    /// * `opcode` - The opcode
    /// * `rd` - The destination register
    /// * `rs1` - The first operand register
    /// * `rs2` - The second operand register
    /// * `funct` - A 10bits number extending the opcode
    pub fn create_r(opcode:u8, rd:u8, rs1:u8, rs2: u8, funct:u16) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode);
        ret.set_rd(rd);
        ret.set_rs1(rs1);
        ret.set_rs2(rs2);
        ret.set_funct10(funct);
        ret
    }

    /// Creates a I type RV32I instruction. These are used for operations with
    /// a register and an immediate (e.g. `addi r1 r1 128`).
    ///
    /// # Arguments
    /// * `opcode` - The opcode
    /// * `rd` - The destination register
    /// * `rs1` - The register operand
    /// * `imm` - The immediate operand on 12bits
    /// * `funct` - The function to perform (extension of the opcode, on 3bits)
    pub fn create_i(opcode:u8, rd:u8, rs1:u8, imm:i32, funct:u8) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode);
        ret.set_rd(rd);
        ret.set_rs1(rs1);
        ret.set_imm_i(imm);
        ret.set_funct3(funct);
        ret
    }

    /// Creates a S type RV32I instruction. These are used for operations with
    /// 2 register operands and an immediate, but no destination register
    /// (e.g. `stw r1 r2 10`).
    ///
    /// # Arguments
    /// * `opcode` - The opcode
    /// * `rs1` - First register operand
    /// * `rs2` - Second register operand
    /// * `imm` - Immediate operand on 12bits representing bits [11:0]
    /// * `funct` - A 3bits extension of the opcode
    pub fn create_s(opcode:u8, rs1:u8, rs2:u8, imm:i32, funct:u8) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode);
        ret.set_rs1(rs1);
        ret.set_rs2(rs2);
        ret.set_imm_s(imm);
        ret.set_funct3(funct);
        ret
    }

    /// Creates a B type RV32I instruction. These are S type instructions with
    /// a different immediate layout (the immediate on B represent bits [12:1])
    pub fn create_b(opcode:u8, rs1:u8, rs2:u8, imm:i32, funct:u8) -> Instruction {
        let mut ret = Self::create_s(opcode, rs1, rs2, 0, funct);

        ret.set_imm_b(imm);
        ret
    }

    /// Creates a U type RV32I instruction. These are used for operations with
    /// only an immediate operand. As it carries fewer information than other
    /// instructions, U type instructions have more space for their immediate.
    ///
    /// # Arguments
    /// * `opcode` - The opcode
    /// * `rd` - The destination register of the operation
    /// * `imm` - bits [31:12] of the 32bits immediate value
    pub fn create_u(opcode:u8, rd: u8, imm:i32) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode);
        ret.set_rd(rd);
        ret.set_imm_u(imm);
        ret
    }

    /// Creates a J type RV32I instruction. These are U type instructions with
    /// a different immediate layout (the immdiate on J represent bits [19:0])
    pub fn create_j(opcode:u8, rd:u8, imm:i32) -> Instruction {
        let mut ret = Self::create_u(opcode, rd, 0);

        ret.set_imm_j(imm);
        ret
    }

    pub fn get_opcode(&self) -> u8 {
        (self.0 & 0x7F) as u8
    }

    pub fn set_opcode(&mut self, opcode:u8) {
        self.0 = (self.0 & 0xFFFFFF80) | ((opcode as u32) << 0)
    }

    pub fn get_rd(&self) -> u8 {
        ((self.0 & 0xF80) >> 7) as u8
    }

    pub fn set_rd(&mut self, rd:u8) {
        self.0 = (self.0 & 0xFFFFF07F) | ((rd as u32) << 7)
    }

    pub fn get_rs1(&self) -> u8 {
        ((self.0 & 0xF8000) >> 15) as u8
    }

    pub fn set_rs1(&mut self, rs1:u8) {
        self.0 = (self.0 & 0xFFF07FFF) | ((rs1 as u32) << 15)
    }

    pub fn get_rs2(&self) -> u8 {
        ((self.0 & 0x1F00000) >> 20) as u8
    }

    pub fn set_rs2(&mut self, rs2:u8) {
        self.0 = (self.0 & 0xFE0FFFFF) | ((rs2 as u32) << 20)
    }

    pub fn get_funct3(&self) -> u8 {
        ((self.0 & 0x7000) >> 12) as u8
    }

    pub fn set_funct3(&mut self, funct3:u8) {
        self.0 = (self.0 & 0xFFFF8FFF) | ((funct3 as u32) << 12)
    }

    pub fn get_funct7(&self) -> u8 {
        ((self.0 & 0xFE000000) >> 25) as u8
    }

    pub fn set_funct7(&mut self, funct7:u8) {
        self.0 = (self.0 & 0x01FFFFFF) | ((funct7 as u32) << 25)
    }

    pub fn get_funct10(&self) -> u16 {
        ((self.get_funct7() << 3) | (self.get_funct3())) as u16
    }

    pub fn set_funct10(&mut self, funct10:u16) {
        self.set_funct7((funct10 >> 3) as u8);
        self.set_funct3((funct10 & 0x7) as u8)
    }

    pub fn get_imm_i(&self) -> i32 {
        let imm11_0 = (self.0 & 0xFFF00000) as i32;
        imm11_0 >> 20
    }

    pub fn set_imm_i(&mut self, imm:i32) {
        self.0 = (self.0 & 0x000FFFFF) | (imm << 20) as u32
    }

    pub fn get_imm_s(&self) -> i32 {
        let high = (self.0 & 0xFE000000) as i32;
        let low = self.get_rd() as i32;
        (high >> 20) | low
    }

    pub fn set_imm_s(&mut self, imm:i32) {
        self.0 = (self.0 & 0x01FFFFFF) | ((imm & 0xFE0) << 20) as u32;
        self.set_rd((imm & 0x1F) as u8);
    }

    pub fn get_imm_u(&self) -> i32 {
        (self.0 & 0xFFFFF000) as i32
    }

    pub fn set_imm_u(&mut self, imm:i32) {
        self.0 = (self.0 & 0x00000FFF) | ((imm as u32) & 0xFFFFF000)
    }

    pub fn get_imm_b(&self) -> i32 {
        let sign = (self.0 & 0x80000000) as i32;
        let overlap = (self.0 & 0x7E000000) as i32;
        let bit7 = (self.0 & 0x80) as i32;
        let high_rd = (self.get_rd() & 0x1E) as i32;
        (sign >> 19) | (bit7 << 4) | (overlap >> 20) | high_rd
    }

    pub fn set_imm_b(&mut self, imm:i32) {
        self.0 &= 0x01FFE07F;

        self.0 |= ((imm & 0x1000) << 19) as u32;
        self.0 |= ((imm & 0x0800) >> 4) as u32;
        self.0 |= ((imm & 0x07E0) << 20) as u32;
        self.0 |= ((imm & 0x001E) << 7) as u32;
    }

    pub fn get_imm_j(&self) -> i32 {
        let sign = (self.0 & 0x80000000) as i32;
        let a = (self.0 & 0x000FF000) as i32;
        let b = (self.0 & 0x00100000) as i32;
        let c = (self.0 & 0x7FE00000) as i32;
        (sign >> 11) | a | (b >> 9) | (c >> 20)
    }

    pub fn set_imm_j(&mut self, imm:i32) {
        self.0 = self.0 & 0x00000FFF;

        self.0 |= ((imm & 0x100000) << 11) as u32;
        self.0 |= ((imm & 0x0007FE) << 20) as u32;
        self.0 |= ((imm & 0x000800) << 9) as u32;
        self.0 |= (imm  & 0x0FF000) as u32;
    }
    
    pub fn get_type(&self) -> Type {
        match self.get_opcode() {
            0b0000011 => Type::I,
            0b0010011 => Type::I,
            0b1001111 => Type::I,
            0b1110011 => Type::I,
            0b0100011 => Type::S,
            0b0110011 => Type::R,
            0b0110111 => Type::U,
            0b0010111 => Type::U,
            0b1101111 => Type::J,
            0b0001111 => Type::U,
            0b1100011 => Type::B,
            _ => Type::U,
        }
    }

    pub fn get_opcode_enum(&self) -> OpCode {
        let codes = &[OpCode::LUI, OpCode::AUIPC, OpCode::JAL, OpCode::JALR
        , OpCode::BRANCH, OpCode::LOAD, OpCode::STORE, OpCode::OPIMM
        , OpCode::OPREG, OpCode::FENCE, OpCode::CSR ];

        for c in codes {
            if *c as u8 == self.get_opcode() {
                return *c
            }
        }

        OpCode::INVALID
    }
}

/// Enum representing the type of instruction.
#[derive(Debug, Copy, Clone)]
pub enum Type {
    R,
    I,
    S,
    B,
    U,
    J,
}

/// Enum naming the different opcodes values
#[derive(PartialEq, Debug, Copy, Clone)]
pub enum OpCode {
    LUI     = 0b0110111,
    AUIPC   = 0b0010111,
    JAL     = 0b1101111,
    JALR    = 0b1001111,
    BRANCH  = 0b1100011,
    LOAD    = 0b0000011,
    STORE   = 0b0100011,
    OPIMM   = 0b0010011,
    OPREG   = 0b0110011,
    FENCE   = 0b0001111,
    CSR     = 0b1110011,
    INVALID = 0,
}

/// This type represents a CSR's (Control State Register) ID in the CSR table
///
/// These registers are 12-bits indexed and used by the software to either
/// control the machine (e.g. modify privilege mode, register interruption
/// handlers ...), or know about its state (e.g. available extensions
/// , performances counters ...).
///
/// You can match any CsrId with its implemented constants. This structure helps
/// representing a CSR ID as what it really is in hardware (12bits number) and
/// adds some helper functions to easily get privilege the R/W permissions and
/// privilege level of the indexed register.
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub struct CsrId(pub u16);

impl CsrId {
    pub const USTATUS : CsrId = CsrId(0x000);
    pub const UIE : CsrId = CsrId(0x004);
    pub const UTVEC : CsrId = CsrId(0x005);
    pub const USCRATCH : CsrId = CsrId(0x040);
    pub const UEPC : CsrId = CsrId(0x041);
    pub const UCAUSE : CsrId = CsrId(0x042);
    pub const UTVAL : CsrId = CsrId(0x043);
    pub const UIP : CsrId = CsrId(0x044);

    pub const FFLAGS : CsrId = CsrId(0x001);
    pub const FRM : CsrId = CsrId(0x002);
    pub const FCSR : CsrId = CsrId(0x003);

    pub const CYCLE : CsrId = CsrId(0xC00);
    pub const TIME : CsrId = CsrId(0xC01);
    pub const INSTRET : CsrId = CsrId(0xC02);

    pub fn hmpcounter(i:u16) -> CsrId { CsrId(0xC00 + i) }

    pub const CYCLEH : CsrId = CsrId(0xC80);
    pub const TIMEH : CsrId = CsrId(0xC81);
    pub const INSTRETH : CsrId = CsrId(0xC82);

    pub fn hmpcounter_h(i:u16) -> CsrId { CsrId(0xC80 + i) }

    pub const SSTATUS : CsrId = CsrId(0x100);
    pub const SEDELEG : CsrId = CsrId(0x102);
    pub const SIDELEG : CsrId = CsrId(0x103);
    pub const SIE : CsrId = CsrId(0x104);
    pub const STVEC : CsrId = CsrId(0x105);
    pub const SCOUNTEREN : CsrId = CsrId(0x106);

    pub const SSCRATCH : CsrId = CsrId(0x140);
    pub const SEPC : CsrId = CsrId(0x141);
    pub const SCAUSE : CsrId = CsrId(0x142);
    pub const STVAL : CsrId = CsrId(0x143);
    pub const SIP : CsrId = CsrId(0x144);

    pub const SATP : CsrId = CsrId(0x180);

    pub const HSTATUS : CsrId = CsrId(0xA00);
    pub const HEDELEG : CsrId = CsrId(0xA02);
    pub const HIDELEG : CsrId = CsrId(0xA03);

    pub const HGATP : CsrId = CsrId(0xA80);

    pub const BSSTATUS : CsrId = CsrId(0x200);
    pub const BSIE : CsrId = CsrId(0x204);
    pub const BSTVEC : CsrId = CsrId(0x205);
    pub const BSSCRATCH : CsrId = CsrId(0x240);
    pub const BSEPC : CsrId = CsrId(0x241);
    pub const BSCAUSE : CsrId = CsrId(0x242);
    pub const BSTVAL : CsrId = CsrId(0x243);
    pub const BSIP : CsrId = CsrId(0x244);
    pub const BSATP : CsrId = CsrId(0x280);

    pub const MVENDORID : CsrId = CsrId(0xF11);
    pub const MARCHID : CsrId = CsrId(0xF12);
    pub const MIMPID : CsrId = CsrId(0xF13);
    pub const MHARTID : CsrId = CsrId(0xF14);

    pub const MSTATUS : CsrId = CsrId(0x300);
    pub const MISA : CsrId = CsrId(0x301);
    pub const MEDELEG : CsrId = CsrId(0x302);
    pub const MIDELEG : CsrId = CsrId(0x303);
    pub const MIE : CsrId = CsrId(0x304);
    pub const MTVEC : CsrId = CsrId(0x305);
    pub const MCOUNTEREN : CsrId = CsrId(0x306);

    pub const MSCRATCH : CsrId = CsrId(0x340);
    pub const MEPC : CsrId = CsrId(0x341);
    pub const MCAUSE : CsrId = CsrId(0x342);
    pub const MTVAL : CsrId = CsrId(0x343);
    pub const MIP : CsrId = CsrId(0x344);

    pub fn pmpcfg(i:u16) -> CsrId { CsrId(0x3A0 + i) }
    pub fn pmpaddr(i:u16) -> CsrId { CsrId(0x3B0 + i) }

    pub const MCYCLE : CsrId = CsrId(0xB00);
    pub const MINSTRET : CsrId = CsrId(0xB02);

    pub fn mhmpcounter(i:u16) -> CsrId { CsrId(0xB00 + i) }

    pub const MCYCLEH : CsrId = CsrId(0xB80);
    pub const MINSTRETH : CsrId = CsrId(0xB82);

    pub fn mhmpcounter_h(i:u16) -> CsrId { CsrId(0xB80 + i) }

    pub const MCOUNTINHIBIT : CsrId = CsrId(0x320);

    pub fn mhpevent(i:u16) -> CsrId { CsrId(0x323 + i) }

    pub const TSELECT : CsrId = CsrId(0x7A0);
    pub const TDATA1 : CsrId = CsrId(0x7A1);
    pub const TDATA2 : CsrId = CsrId(0x7A2);
    pub const TDATA3 : CsrId = CsrId(0x7A3);

    pub const DCSR : CsrId = CsrId(0x7B0);
    pub const DPC : CsrId = CsrId(0x7B1);
    pub const DSCRATCH0 : CsrId = CsrId(0x7B2);
    pub const DSCRATCH1 : CsrId = CsrId(0x7B3);

    pub fn mode(&self) -> u8 {
        (self.0 >> 10) as u8
    }

    pub fn level(&self) -> u8 {
        ((self.0 >> 8) & 0b11) as u8
    }
}

/// An enum representing every CSR fields (slices of CSR). It is used to access
/// every CSR field individually in order to check their type (RW/RO/WARL/WLRL)
pub enum CsrField {
    // TODO define all fields
    MODE,
    ASID,
    PPN,
    MXL,
    MXR,
    SUM,
    SPP,
    SPIE,
    SIE,
    SCauseInterrupt,
    SCauseCode,
    Extensions,
    MCauseCode,
    MCauseInterrupt,
}

/// CSR field read/write type
///
/// * `RW`: Can be read and written freely
/// * `RO`: Can be read but not written
/// * `WARL`: (Write Any Read Legal) Can write any value to the register, even
///           illegal ones. The register is assured to return legal values when read.
/// * `WLRL`: (Write Legal Read Legal) Can write only legal values in the register
///           if an illegal value is written, you can't expect legal value to be read.
pub enum CsrFieldType {
    RW, RO, WARL, WLRL,
}

impl CsrField {

    // TODO finish the full implementation
    pub fn get_type(&self) -> CsrFieldType {
        match self {
            CsrField::MXL => CsrFieldType::WARL,
            CsrField::Extensions => CsrFieldType::WARL,
            CsrField::PPN => CsrFieldType::WARL,
            _ => CsrFieldType::RO,
        }
    }
}
