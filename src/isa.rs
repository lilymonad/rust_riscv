use types::MachineInteger;
use std::fmt;

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
    pub fn create_r(opcode:OpCode, rd:u8, rs1:u8, rs2: u8, funct:u16) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode.into());
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
    pub fn create_i(opcode:OpCode, rd:u8, rs1:u8, imm:i32, funct:u8) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode.into());
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
    /// * `imm` - Immediate operand on 12bits representing bits `[11:0]`
    /// * `funct` - A 3bits extension of the opcode
    pub fn create_s(opcode:OpCode, rs1:u8, rs2:u8, imm:i32, funct:u8) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode.into());
        ret.set_rs1(rs1);
        ret.set_rs2(rs2);
        ret.set_imm_s(imm);
        ret.set_funct3(funct);
        ret
    }

    /// Creates a B type RV32I instruction. These are S type instructions with
    /// a different immediate layout (the immediate on B represent bits `[12:1]`)
    pub fn create_b(opcode:OpCode, rs1:u8, rs2:u8, imm:i32, funct:u8) -> Instruction {
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
    /// * `imm` - bits `[31:12]` of the 32bits immediate value
    pub fn create_u(opcode:OpCode, rd: u8, imm:i32) -> Instruction {
        let mut ret = Instruction(0);

        ret.set_opcode(opcode.into());
        ret.set_rd(rd);
        ret.set_imm_u(imm);
        ret
    }

    /// Creates a J type RV32I instruction. These are U type instructions with
    /// a different immediate layout (the immdiate on J represent bits `[19:0]`)
    pub fn create_j(opcode:OpCode, rd:u8, imm:i32) -> Instruction {
        let mut ret = Self::create_u(opcode, rd, 0);

        ret.set_imm_j(imm);
        ret
    }

    // Per-instruction ctor
    pub fn lui(rd:u8, imm:i32) -> Instruction { Self::create_u(OpCode::LUI, rd, imm) }
    pub fn auipc(rd:u8, imm:i32) -> Instruction { Self::create_u(OpCode::AUIPC, rd, imm) }
    pub fn jal(rd:u8, imm:i32) -> Instruction { Self::create_j(OpCode::JAL, rd, imm) }
    pub fn jalr(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::JALR, rd, rs1, imm, 0) }
    pub fn beq(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_b(OpCode::BRANCH, rs1, rs2, imm, 0) }
    pub fn bne(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_b(OpCode::BRANCH, rs1, rs2, imm, 1) }
    pub fn blt(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_b(OpCode::BRANCH, rs1, rs2, imm, 4) }
    pub fn bge(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_b(OpCode::BRANCH, rs1, rs2, imm, 5) }
    pub fn bltu(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_b(OpCode::BRANCH, rs1, rs2, imm, 6) }
    pub fn bgeu(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_b(OpCode::BRANCH, rs1, rs2, imm, 7) }
    pub fn lb(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::LOAD, rd, rs1, imm, 0) }
    pub fn lh(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::LOAD, rd, rs1, imm, 1) }
    pub fn lw(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::LOAD, rd, rs1, imm, 2) }
    pub fn lbu(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::LOAD, rd, rs1, imm, 4) }
    pub fn lhu(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::LOAD, rd, rs1, imm, 5) }
    pub fn sb(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_s(OpCode::STORE, rs1, rs2, imm, 0) }
    pub fn sh(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_s(OpCode::STORE, rs1, rs2, imm, 1) }
    pub fn sw(rs1:u8, rs2:u8, imm:i32) -> Instruction { Self::create_s(OpCode::STORE, rs1, rs2, imm, 2) }
    pub fn addi(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::OPIMM, rd, rs1, imm, 0) }
    pub fn slti(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::OPIMM, rd, rs1, imm, 2) }
    pub fn sltiu(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::OPIMM, rd, rs1, imm, 3) }
    pub fn xori(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::OPIMM, rd, rs1, imm, 4) }
    pub fn ori(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::OPIMM, rd, rs1, imm, 6) }
    pub fn andi(rd:u8, rs1:u8, imm:i32) -> Instruction { Self::create_i(OpCode::OPIMM, rd, rs1, imm, 7) }
    pub fn slli(rd:u8, rs1:u8, shamt:i32) -> Instruction { Self::create_r(OpCode::OPIMM, rd, rs1, shamt as u8, 1) } 
    pub fn srli(rd:u8, rs1:u8, shamt:i32) -> Instruction { Self::create_r(OpCode::OPIMM, rd, rs1, shamt as u8, 5) } 
    pub fn srai(rd:u8, rs1:u8, shamt:i32) -> Instruction { Self::create_r(OpCode::OPIMM, rd, rs1, shamt as u8, 261) } 
    pub fn add(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 0) }
    pub fn sub(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 256) }
    pub fn sll(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 1) }
    pub fn slt(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 2) }
    pub fn sltu(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 3) }
    pub fn xor(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 4) }
    pub fn srl(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 5) }
    pub fn sra(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 261) }
    pub fn or(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 6) }
    pub fn and(rd:u8, rs1:u8, rs2:u8) -> Instruction { Self::create_r(OpCode::OPREG, rd, rs1, rs2, 7) }
    pub fn fence(pred:u8, succ:u8) -> Instruction { Self::create_i(OpCode::FENCE, 0, 0, (pred << 4 | succ) as i32, 1) }
    pub fn fence1() -> Instruction { Self::fence(0, 0) }

    pub fn nop() -> Instruction { Self::addi(0, 0, 0) }

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
        ((self.get_funct7() as u16) << 3) | (self.get_funct3() as u16)
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
        self.0 &= 0x01FFF07F;

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
        self.get_opcode_enum().into()
    }

    pub fn get_opcode_enum(&self) -> OpCode {
        self.get_opcode().into()
    }

    /// This function is mainly used as a helper for the fmt::Display trait
    /// in order to pretty-print an instruction with println!()
    pub fn get_mnemonic(&self) -> &str {
        match self.get_opcode_enum() {
            OpCode::LUI => "lui",
            OpCode::AUIPC => "auipc",
            OpCode::JAL => "jal",
            OpCode::JALR => "jalr",
            OpCode::OPIMM => { match self.get_funct3() {
                0 => "addi", 2 => "slti", 3 => "sltiu", 4 => "xori", 6 => "ori",
                7 => "andi", 1 => "slli",
                5 => { match self.get_funct7() { 0 => "srli", 32 => "srai", _ => "opimm" } },
                _ => "opimm",
            } },
            OpCode::BRANCH => { match self.get_funct3() {
                0 => "beq", 1 => "bne", 4 => "blt", 5 => "bge", 6 => "bltu",
                7 => "bgeu", _ => "illegal",
            } },
            OpCode::LOAD => { match self.get_funct3() {
                0 => "lb", 1 => "lh", 2 => "lw", 4 => "lbu", 5 => "lhu",
                _ => "load",
            } },
            OpCode::STORE => { match self.get_funct3() {
                0 => "sb", 1 => "sh", 2 => "sw", _ => "illegal",
            } },
            OpCode::OPREG => { match self.get_funct10() {
                0 => "add", 256 => "sub", 1 => "sll", 2 => "slt", 3 => "sltu",
                4 => "xor", 5 => "srl", 261 => "sra", 6 => "or", 7 => "and",
                _ => "opreg",
            } },
            OpCode::FENCE => { match self.get_funct3() {
                0 => "fence", 1 => "fence.1", _ => "illegal",
            } },
            OpCode::SYSTEM => { match self.get_funct7() {
                _ => "sys",
            } },
            OpCode::INVALID => "illegal",
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get_type() {
            Type::R => {
                write!(f, "{} r{} = r{}, r{}", self.get_mnemonic(), self.get_rd(), self.get_rs1(), self.get_rs2())
            },
            Type::I => {
                let mnemonic = self.get_mnemonic();
                let imm = 
                    if mnemonic == "srli" || mnemonic == "srai"
                        { self.get_rs2() as i32 }
                    else
                        { self.get_imm_i() };
                write!(f, "{} r{} = r{}, {}", mnemonic, self.get_rd(), self.get_rs1(), imm)
            },
            Type::S => {
                write!(f, "{} r{} @ r{}+{}", self.get_mnemonic(), self.get_rs2(), self.get_rs1(), self.get_imm_s())
            },
            Type::B => {
                write!(f, "{} @pc+{} if r{} $ r{}", self.get_mnemonic(), self.get_imm_b(), self.get_rs1(), self.get_rs2())
            },
            Type::U => {
                write!(f, "{} r{}, {}", self.get_mnemonic(), self.get_rd(), self.get_imm_u())
            },
            Type::J => {
                write!(f, "{} {}, ret r{}", self.get_mnemonic(), self.get_imm_j(), self.get_rd())
            },
        }
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
    LUI    ,
    AUIPC  ,
    JAL    ,
    JALR   ,
    BRANCH ,
    LOAD   ,
    STORE  ,
    OPIMM  ,
    OPREG  ,
    FENCE  ,
    SYSTEM ,
    INVALID,
}

impl Into<Type> for OpCode {
    fn into(self) -> Type {
        match self {
            OpCode::LUI     => Type::U,
            OpCode::AUIPC   => Type::U,
            OpCode::JAL     => Type::J,
            OpCode::JALR    => Type::I,
            OpCode::BRANCH  => Type::B,
            OpCode::LOAD    => Type::I,
            OpCode::STORE   => Type::S,
            OpCode::OPIMM   => Type::I,
            OpCode::OPREG   => Type::R,
            OpCode::FENCE   => Type::U,
            OpCode::SYSTEM  => Type::I,
            _ => Type::U,
        }
    }
}

impl From<u8> for OpCode {
    fn from(v:u8) -> OpCode {
        match v {
            0b0110111 => OpCode::LUI,
            0b0010111 => OpCode::AUIPC,
            0b1101111 => OpCode::JAL,
            0b1100111 => OpCode::JALR,
            0b1100011 => OpCode::BRANCH,
            0b0000011 => OpCode::LOAD,
            0b0100011 => OpCode::STORE,
            0b0010011 => OpCode::OPIMM,
            0b0110011 => OpCode::OPREG,
            0b0001111 => OpCode::FENCE,
            0b1110011 => OpCode::SYSTEM,
            _ => OpCode::INVALID,
        }
    }
}

impl Into<u8> for OpCode {
    fn into(self) -> u8 {
        match self {
            OpCode::LUI     => 0b0110111,
            OpCode::AUIPC   => 0b0010111,
            OpCode::JAL     => 0b1101111,
            OpCode::JALR    => 0b1100111,
            OpCode::BRANCH  => 0b1100011,
            OpCode::LOAD    => 0b0000011,
            OpCode::STORE   => 0b0100011,
            OpCode::OPIMM   => 0b0010011,
            OpCode::OPREG   => 0b0110011,
            OpCode::FENCE   => 0b0001111,
            OpCode::SYSTEM  => 0b1110011,
            OpCode::INVALID => 0,
        }
    }
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
    Bank, Offset, // mvendorid
    ArchitectureID, // marchid
    Implementation, // mimpid
    HartID, // mhartid
    MTVecBASE, MTVecMODE, // mtvec
    STVecBASE, STVecMODE, // stvec
    SynchronousExceptions, Interrupts, // medeleg, mideleg
    MEIP, SEIP, UEIP, MTIP, STIP, UTIP, MSIP, SSIP, USIP, // mip
    MEIE, SEIE, UEIE, MTIE, STIE, UTIE, MSIE, SSIE, USIE, // mie
    MTIME, MTIMECMP, // mtime, mtimecmp
    MCYCLE, MCYCLEH, // mcycle+h
    MINSTRET, MINSTRETH, // minstret+h
    MHPMEN, MIREN, MTMEN, MCYEN, // mcounteren
    SHPMEN, SIREN, STMEN, SCYEN, // scounteren
    MHPMIN, MIRIN, MTMIN, MCYIN, // mcountinhibit
    MSCRATCH, SSCRATCH,
    MEPC, SEPC,
    MTVAL, STVAL,
    MODE, ASID, PPN, // satp
    MXL, Extensions, // misa
    UXL, SXL, TSR, TW, TVM, MPRV, MPP, MPIE, MIE, // +sstatus = mstatus
    SD, MXR, SUM, XS, FS, SPP, SPIE, SIE, // sstatus
    UPIE, UIE, // ustatus
    MCauseInterrupt, MCauseCode, // mcause
    SCauseInterrupt, SCauseCode, // scause
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
    pub fn get_type(&self) -> CsrFieldType {
        match self {
            CsrField::MXL | CsrField::Extensions | CsrField::PPN |
                CsrField::MPP | CsrField::SPP | CsrField::SXL | CsrField::UXL |
                CsrField::FS | CsrField::MTVecBASE | CsrField::STVecBASE |
                CsrField::MTVecMODE | CsrField::SynchronousExceptions |
                CsrField::Interrupts | CsrField::MEIP | CsrField::SEIP |
                CsrField::UEIP | CsrField::MTIP | CsrField::STIP | CsrField::UTIP |
                CsrField::MSIP | CsrField::SSIP | CsrField::USIP | CsrField::MEIE |
                CsrField::SEIE | CsrField::UEIE | CsrField::MTIE | CsrField::STIE |
                CsrField::UTIE | CsrField::MSIE | CsrField::SSIE | CsrField::USIE |
                CsrField::MHPMEN | CsrField::MIREN | CsrField::MTMEN | CsrField::MCYEN |
                CsrField::MODE | CsrField::ASID | CsrField::STVecMODE | CsrField::SEPC |
                CsrField::MEPC
                    => CsrFieldType::WARL,
            CsrField::MCauseCode | CsrField::SCauseCode => CsrFieldType::WLRL,
            CsrField::XS | CsrField::SD => CsrFieldType::RO,
            _ => CsrFieldType::RW,
        }
    }

    pub fn get_csr_id(&self) -> CsrId {
        match self {
            CsrField::Bank | CsrField::Offset => CsrId::MVENDORID,
            CsrField::ArchitectureID => CsrId::MARCHID,
            CsrField::Implementation => CsrId::MIMPID,
            CsrField::HartID => CsrId::MHARTID,
            CsrField::MTVecBASE | CsrField::MTVecMODE => CsrId::MTVEC,
            CsrField::STVecBASE | CsrField::STVecMODE => CsrId::STVEC,
            CsrField::SynchronousExceptions => CsrId::MEDELEG,
            CsrField::Interrupts => CsrId::MIDELEG,
            CsrField::MEIP | CsrField::SEIP | CsrField::UEIP | CsrField::MTIP |
                CsrField::STIP | CsrField::UTIP | CsrField::MSIP | CsrField::SSIP |
                CsrField::USIP => CsrId::MIP,
            CsrField::MEIE | CsrField::SEIE | CsrField::UEIE | CsrField::MTIE |
                CsrField::STIE | CsrField::UTIE | CsrField::MSIE |
                CsrField::SSIE | CsrField::USIE => CsrId::MIE,
            CsrField::MTIME => CsrId::TIME,
            CsrField::MTIMECMP => CsrId::TIME /* CsrId::TIMECMP */,
            CsrField::MINSTRET => CsrId::MINSTRET,
            CsrField::MINSTRETH => CsrId::MINSTRETH,
            CsrField::MCYCLE => CsrId::MCYCLE,
            CsrField::MCYCLEH => CsrId::MCYCLEH,
            CsrField::MHPMEN | CsrField::MIREN | CsrField::MTMEN |
                CsrField::MCYEN => CsrId::MCOUNTEREN,
            CsrField::MHPMIN | CsrField::MIRIN | CsrField::MTMIN |
                CsrField::MCYIN => CsrId::MCOUNTINHIBIT,
            CsrField::SHPMEN | CsrField::SIREN | CsrField::STMEN |
                CsrField::SCYEN => CsrId::SCOUNTEREN,
            CsrField::MSCRATCH => CsrId::MSCRATCH,
            CsrField::SSCRATCH => CsrId::SSCRATCH,
            CsrField::MEPC => CsrId::MEPC,
            CsrField::SEPC => CsrId::SEPC,
            CsrField::MTVAL => CsrId::MTVAL,
            CsrField::STVAL => CsrId::STVAL,
            CsrField::MODE | CsrField::ASID | CsrField::PPN => CsrId::SATP,
            CsrField::MXL | CsrField::Extensions => CsrId::MISA,
            CsrField::UXL | CsrField::SXL | CsrField::TSR | CsrField::TW |
                CsrField::TVM | CsrField::MPRV | CsrField::MPP | CsrField::MPIE
                | CsrField::MIE | CsrField::SD | CsrField::MXR | CsrField::SUM
                | CsrField::XS | CsrField::FS | CsrField::SPP
                | CsrField::SPIE | CsrField::SIE | CsrField::UPIE
                | CsrField::UIE => CsrId::MSTATUS,
            CsrField::MCauseInterrupt | CsrField::MCauseCode => CsrId::MCAUSE,
            CsrField::SCauseInterrupt | CsrField::SCauseCode => CsrId::SCAUSE,
        }
    }

    pub fn offset<T : MachineInteger>(&self) -> u32 {
        match self {
            CsrField::Bank => 7,
            CsrField::MXL => T::XLEN - 2,
            CsrField::TSR => 22,
            CsrField::TW => 21,
            CsrField::TVM => 20,
            CsrField::MPRV => 17,
            CsrField::MPP => 11,
            CsrField::MPIE => 7,
            CsrField::MIE => 3,
            CsrField::UXL => 32,
            CsrField::SXL => 34,
            CsrField::MTVecBASE | CsrField::STVecBASE => 2,
            CsrField::MEIE | CsrField::MEIP => 11,
            CsrField::MTIP | CsrField::MTIE => 7,
            CsrField::MSIP | CsrField::MSIE => 3,
            CsrField::MCYCLEH | CsrField::MINSTRETH => 32,
            CsrField::MHPMEN | CsrField::SHPMEN | CsrField::MHPMIN => 3,
            CsrField::MIREN | CsrField::SIREN | CsrField::MIRIN => 2,
            CsrField::MTMEN | CsrField::STMEN | CsrField::MTMIN => 1,
            CsrField::MCauseInterrupt | CsrField::SCauseInterrupt => T::XLEN - 1,
            CsrField::SD => T::XLEN - 1,
            CsrField::MXR => 19,
            CsrField::SUM => 18,
            CsrField::XS => 15,
            CsrField::FS => 13,
            CsrField::SPP => 8,
            CsrField::SPIE => 5,
            CsrField::UPIE => 4,
            CsrField::SIE => 1,
            CsrField::SEIP | CsrField::SEIE => 9,
            CsrField::UEIP | CsrField::UEIE => 8,
            CsrField::STIP | CsrField::STIE => 5,
            CsrField::UTIP | CsrField::UTIE => 4,
            CsrField::SSIP | CsrField::SSIE => 1,
            CsrField::MODE => 31,
            CsrField::ASID => 22,
            _ => 0,
        }
    }

    // TODO finish implementation
    pub fn mask<T : MachineInteger>(&self) -> T {
        let xlen = T::XLEN as usize;
        match self {
            CsrField::TSR => T::slice_mask(23, 22),
            CsrField::TW => T::slice_mask(22, 21),
            CsrField::TVM => T::slice_mask(20, 21),
            CsrField::MPRV => T::slice_mask(18, 17),
            CsrField::MPP => T::slice_mask(13, 11),
            CsrField::MPIE => T::slice_mask(8, 7),
            CsrField::MIE => T::slice_mask(4, 3),
            CsrField::USIE | CsrField::USIP => T::slice_mask(1, 0),
            CsrField::SSIE | CsrField::SSIP => T::slice_mask(2, 1),
            CsrField::UTIE | CsrField::UTIP => T::slice_mask(5, 4),
            CsrField::STIE | CsrField::STIP => T::slice_mask(6, 5),
            CsrField::UEIE | CsrField::UEIP => T::slice_mask(9, 8),
            CsrField::SEIE | CsrField::SEIP => T::slice_mask(10, 9),
            CsrField::MTVecMODE | CsrField::STVecMODE => T::slice_mask(2, 0),
            CsrField::MTVecBASE | CsrField::STVecBASE => T::slice_mask(31, 2),
            CsrField::MXR => T::slice_mask(20, 19),
            CsrField::SUM  => T::slice_mask(19, 18),
            CsrField::SPP  => T::slice_mask(9, 8),
            CsrField::SPIE => T::slice_mask(6, 5),
            CsrField::SIE  => T::slice_mask(2, 1),
            CsrField::SCauseCode | CsrField::MCauseCode
                => T::slice_mask(xlen-1, 0),
            CsrField::SCauseInterrupt | CsrField::MCauseInterrupt
                => T::slice_mask(xlen, xlen-1),
            CsrField::MSIP | CsrField::MSIE => T::slice_mask(4, 3),
            CsrField::MTIP | CsrField::MTIE => T::slice_mask(8, 7),
            CsrField::MEIP | CsrField::MEIE => T::slice_mask(12, 11),
            _ => T::all_set(),
        }
    }
}
