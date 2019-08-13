
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
            0b1101111 => Type::U,
            0b0001111 => Type::U,
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
    U,
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
