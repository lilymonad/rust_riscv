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
    
    pub fn get_c_func3(&self) -> u8 {
        ((self.0 & 0xE000) >> 13) as u8
    }

    pub fn get_cmem_rs1(&self) -> u8 {
        ((self.0 & 0x0380) >> 7) as u8
    }

    pub fn get_cl_rd(&self) -> u8 {
        ((self.0 & 0x001E) >> 2) as u8
    }

    pub fn get_cmem_imm(&self) -> i32 {
        let deuxsept = (self.0 >> 6) & 0b1;
        let six = (self.0 >> 5) & 0b1;
        (((self.0 & 0x1E00) >> 7) | (deuxsept << 2) | (six << 6)) as i32
    }

    pub fn get_cs_rs2(&self) -> u8 {
        self.get_cl_rd()
    }

    pub fn get_c_nzr(&self) -> u8 {
        (self.0 >> 7) as u8
    }

    pub fn get_c_nzimm(&self) -> i32 {
        let num = ((self.0 & 0x1000) | ((self.0 & 0x3E) << 5)) as i16;
        ((num << 3) >> 3) as i32
    }

    pub fn get_cj_imm(&self) -> i32 {
        let troisun = (self.0 >> 2)  & 0b000000001110;
        let quatre = (self.0 >> 9)   & 0b000000010000;
        let cinq = (self.0 << 3)     & 0b000000100000;
        let six = (self.0 >> 1)      & 0b000001000000;
        let sept = (self.0 << 1)     & 0b000010000000;
        let huitneuf = (self.0 >> 1) & 0b001100000000;
        let dix = (self.0 << 2)      & 0b010000000000;
        let onze = (self.0 >> 1)     & 0b100000000000;

        (((troisun | quatre | cinq | six | sept | huitneuf | dix | onze) 
         << 4) >> 4) as i32
    }

    pub fn get_cb_imm(&self) -> i32 {
        let undeux = (self.0 >> 2)         & 0b000000000110;
        let troisquatre = (self.0 >> 7)    & 0b000000011000;
        let cinq = (self.0 << 3)           & 0b000000100000;
        let sixsept = (self.0 << 1)        & 0b000011000000;
        let huit    = (self.0 >> 4)        & 0b000100000000;
        (((undeux | troisquatre | cinq | sixsept | huit)
          << 7) >> 7) as i32
    }

    pub fn get_clwsp_imm(&self) -> i32 {
        let deuxquatre = (self.0 >> 2) & 0b00011100;
        let cinq = (self.0 >> 7)       & 0b00100000;
        let sixsept = (self.0 << 4)    & 0b11000000;
        (deuxquatre | cinq | sixsept) as i32
    }

    pub fn get_cswsp_imm(&self) -> i32 {
        let deuxcinq = (self.0 >> 5) & 0b001111100;
        let sixsept  = (self.0 >> 1) & 0b110000000;
        (deuxcinq | sixsept) as i32
    }

    pub fn get_type(&self) -> Type {
        self.get_opcode_enum().into()
    }

    pub fn get_opcode_enum(&self) -> OpCode {
        self.get_opcode().into()
    }


    pub fn be(&self) -> u32 {
        self.0
    }

    pub fn le(&self) -> u32 {
        let one = self.0 << 24;
        let two = (self.0 << 8) & 0x00FF0000;
        let the = (self.0 >> 8) & 0x0000FF00;
        let fou = self.0 >> 24;

        one | two | the | fou
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

    /// Tells if an instruction is a C instruction (compressed instruction from
    /// the C extension of RISC-V). A compressed instruction is 16bits wide.
    pub fn is_compressed(&self) -> bool {
        (self.get_opcode() & 0b11) != 0b11
    }

    /// Translates a C instruction into a RV32 one, useful for machines that
    /// want to implement C extension by only implementing the RV32 base
    // TODO: test it
    pub fn uncompressed(&self) -> Instruction {
        match self.get_opcode() & 0b11 {
            0b10 => {
                match self.get_c_func3() {
                    0b000 => { Instruction::slli(self.get_c_nzr(), self.get_c_nzr(), self.get_c_nzimm()) },
                    0b010 => { Instruction::lw(self.get_c_nzr(), 2, self.get_clwsp_imm()) },
                    0b110 => { Instruction::sw(2, self.get_cs_rs2(), self.get_cswsp_imm()) },
                    0b100 => {
                        let code = self.get_c_nzimm();
                        let rsrd = self.get_c_nzr();
                        let rs2  = self.get_cs_rs2();
                        if code & 0b100000 == 0{
                            if code & 0b011111 == 0 { // 00
                                Instruction::jalr(0, rsrd, 0)
                            } else { // 01
                                Instruction::addi(rsrd, rs2, 0)
                            }
                        } else {
                            if code & 0b011111 == 0 { // 10
                                Instruction::jalr(1, rsrd, 0)
                            } else { // 11
                                Instruction::add(rsrd, rsrd, rs2)
                            }
                        }
                    },
                    _ => Instruction::nop()
                }
            },
            0b01 => {
                match self.get_c_func3() {
                    0b000 => {
                        let rsrd = self.get_c_nzr();
                        if rsrd == 0 {
                            Instruction::nop()
                        } else {
                            let nzimm = self.get_c_nzimm();
                            Instruction::addi(rsrd, rsrd, nzimm)
                        }
                    },
                    0b001 => { Instruction::jal(1, self.get_cj_imm()) },
                    0b101 => { Instruction::jal(0, self.get_cj_imm()) },
                    0b010 => {
                        let r = self.get_c_nzr();
                        let imm = self.get_c_nzimm();
                        Instruction::addi(r, 0, imm)
                    },
                    0b011 => {
                        let r = self.get_c_nzr();
                        let imm = self.get_c_nzimm() << 12;
                        Instruction::lui(r, imm)
                    },
                    0b100 => {
                        let code = (self.get_c_nzr() >> 3) & 0b11;
                        let r = self.get_c_nzr() & 0b111;
                        let nzimm = self.get_c_nzimm();
                        let rs2 = self.get_cs_rs2();
                        let alucode = (nzimm >> 2) & 0b11;
                        match code {
                            0b00 => { Instruction::srli(r, r, nzimm) },
                            0b01 => { Instruction::srai(r, r, nzimm) },
                            0b10 => { Instruction::andi(r, r, nzimm) },
                            0b11 => {
                                match alucode {
                                    0b00 => Instruction::sub(r, r, rs2),
                                    0b01 => Instruction::xor(r, r, rs2),
                                    0b10 => Instruction::or(r, r, rs2),
                                    0b11 => Instruction::and(r, r, rs2),
                                    _ => Instruction::nop(),
                                }
                            },
                            _ => Instruction::nop()
                        }
                    },
                    0b110 => { Instruction::beq(self.get_cmem_rs1()+8, 0, self.get_cb_imm()) },
                    0b111 => { Instruction::bne(self.get_cmem_rs1()+8, 0, self.get_cb_imm()) },
                    _ => Instruction::nop()
                }
            },
            0b00 => {
                match self.get_c_func3() {
                    0b010 => {
                        let r1 = self.get_cmem_rs1();
                        let rd = self.get_cl_rd();
                        let imm = self.get_cmem_imm() as i32;
                        Instruction::lw(rd + 8, r1 + 8, imm)
                    },
                    0b110 => {
                        let r1 = self.get_cmem_rs1();
                        let r2 = self.get_cs_rs2();
                        let imm = self.get_cmem_imm();

                        Instruction::sw(r1 + 8, r2 + 8, imm as i32)
                    },
                    _ => Instruction::nop()
                }
            },
            _ => Instruction::nop(),
        }
    }

    /// Display the values of registers instead of their name.
    /// It is useful for debugging, to know if a register has a bad value.
    pub fn display_values(&self, rs:&[i32]) -> String {
         match self.get_type() {
            Type::R => {
                format!("{} r{} = {}, {}", self.get_mnemonic(), self.get_rd(), rs[self.get_rs1() as usize], rs[self.get_rs2() as usize])
            },
            Type::I => {
                let mnemonic = self.get_mnemonic();
                let imm = 
                    if mnemonic == "srli" || mnemonic == "srai"
                        { self.get_rs2() as i32 }
                    else
                        { self.get_imm_i() };
                format!("{} r{} = {}, {}", mnemonic, self.get_rd(), rs[self.get_rs1() as usize], imm)
            },
            Type::S => {
                format!("{} {} @ {}+{}", self.get_mnemonic(), rs[self.get_rs2() as usize], rs[self.get_rs1() as usize], self.get_imm_s())
            },
            Type::B => {
                format!("{} @pc+{} if {} $ {}", self.get_mnemonic(), self.get_imm_b(), rs[self.get_rs1() as usize], rs[self.get_rs2() as usize])
            },
            Type::U => {
                format!("{} r{}, {}", self.get_mnemonic(), self.get_rd(), self.get_imm_u())
            },
            Type::J => {
                format!("{} {}, ret r{}", self.get_mnemonic(), self.get_imm_j(), rs[self.get_rd() as usize])
            },
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
pub enum CsrId {
    USTATUS = 0x000,
    UIE = 0x004,
    UTVEC = 0x005,
    USCRATCH = 0x040,
    UEPC = 0x041,
    UCAUSE = 0x042,
    UTVAL = 0x043,
    UIP = 0x044,

    FFLAGS = 0x001,
    FRM = 0x002,
    FCSR = 0x003,

    CYCLE = 0xC00,
    TIME = 0xC01,
    INSTRET = 0xC02,

    HPMCOUNTER03 = 0xC03,
    HPMCOUNTER04 = 0xC04,
    HPMCOUNTER05 = 0xC05,
    HPMCOUNTER06 = 0xC06,
    HPMCOUNTER07 = 0xC07,
    HPMCOUNTER08 = 0xC08,
    HPMCOUNTER09 = 0xC09,
    HPMCOUNTER10 = 0xC0A,
    HPMCOUNTER11 = 0xC0B,
    HPMCOUNTER12 = 0xC0C,
    HPMCOUNTER13 = 0xC0D,
    HPMCOUNTER14 = 0xC0E,
    HPMCOUNTER15 = 0xC0F,
    HPMCOUNTER16 = 0xC10,
    HPMCOUNTER17 = 0xC11,
    HPMCOUNTER18 = 0xC12,
    HPMCOUNTER19 = 0xC13,
    HPMCOUNTER20 = 0xC14,
    HPMCOUNTER21 = 0xC15,
    HPMCOUNTER22 = 0xC16,
    HPMCOUNTER23 = 0xC17,
    HPMCOUNTER24 = 0xC18,
    HPMCOUNTER25 = 0xC19,
    HPMCOUNTER26 = 0xC1A,
    HPMCOUNTER27 = 0xC1B,
    HPMCOUNTER28 = 0xC1C,
    HPMCOUNTER29 = 0xC1D,
    HPMCOUNTER30 = 0xC1E,
    HPMCOUNTER31 = 0xC1F,

    CYCLEH = 0xC80,
    TIMEH = 0xC81,
    INSTRETH = 0xC82,

    HPMCOUNTER03H = 0xC83,
    HPMCOUNTER04H = 0xC84,
    HPMCOUNTER05H = 0xC85,
    HPMCOUNTER06H = 0xC86,
    HPMCOUNTER07H = 0xC87,
    HPMCOUNTER08H = 0xC88,
    HPMCOUNTER09H = 0xC89,
    HPMCOUNTER10H = 0xC8A,
    HPMCOUNTER11H = 0xC8B,
    HPMCOUNTER12H = 0xC8C,
    HPMCOUNTER13H = 0xC8D,
    HPMCOUNTER14H = 0xC8E,
    HPMCOUNTER15H = 0xC8F,
    HPMCOUNTER16H = 0xC90,
    HPMCOUNTER17H = 0xC91,
    HPMCOUNTER18H = 0xC92,
    HPMCOUNTER19H = 0xC93,
    HPMCOUNTER20H = 0xC94,
    HPMCOUNTER21H = 0xC95,
    HPMCOUNTER22H = 0xC96,
    HPMCOUNTER23H = 0xC97,
    HPMCOUNTER24H = 0xC98,
    HPMCOUNTER25H = 0xC99,
    HPMCOUNTER26H = 0xC9A,
    HPMCOUNTER27H = 0xC9B,
    HPMCOUNTER28H = 0xC9C,
    HPMCOUNTER29H = 0xC9D,
    HPMCOUNTER30H = 0xC9E,
    HPMCOUNTER31H = 0xC9F,

    SSTATUS = 0x100,
    SEDELEG = 0x102,
    SIDELEG = 0x103,
    SIE = 0x104,
    STVEC = 0x105,
    SCOUNTEREN = 0x106,

    SSCRATCH = 0x140,
    SEPC = 0x141,
    SCAUSE = 0x142,
    STVAL = 0x143,
    SIP = 0x144,

    SATP = 0x180,

    HSTATUS = 0xA00,
    HEDELEG = 0xA02,
    HIDELEG = 0xA03,

    HGATP = 0xA80,

    BSSTATUS = 0x200,
    BSIE = 0x204,
    BSTVEC = 0x205,
    BSSCRATCH = 0x240,
    BSEPC = 0x241,
    BSCAUSE = 0x242,
    BSTVAL = 0x243,
    BSIP = 0x244,
    BSATP = 0x280,

    MVENDORID = 0xF11,
    MARCHID = 0xF12,
    MIMPID = 0xF13,
    MHARTID = 0xF14,

    MSTATUS = 0x300,
    MISA = 0x301,
    MEDELEG = 0x302,
    MIDELEG = 0x303,
    MIE = 0x304,
    MTVEC = 0x305,
    MCOUNTEREN = 0x306,

    MSCRATCH = 0x340,
    MEPC = 0x341,
    MCAUSE = 0x342,
    MTVAL = 0x343,
    MIP = 0x344,

    PMPCFG0 = 0x3A0,
    PMPCFG1 = 0x3A1,
    PMPCFG2 = 0x3A2,
    PMPCFG3 = 0x3A3,

    PMPADDR00 = 0x3B0,
    PMPADDR01 = 0x3B1,
    PMPADDR02 = 0x3B2,
    PMPADDR03 = 0x3B3,
    PMPADDR04 = 0x3B4,
    PMPADDR05 = 0x3B5,
    PMPADDR06 = 0x3B6,
    PMPADDR07 = 0x3B7,
    PMPADDR08 = 0x3B8,
    PMPADDR09 = 0x3B9,
    PMPADDR10 = 0x3BA,
    PMPADDR11 = 0x3BB,
    PMPADDR12 = 0x3BC,
    PMPADDR13 = 0x3BD,
    PMPADDR14 = 0x3BE,
    PMPADDR15 = 0x3BF,

    MCYCLE = 0xB00,
    MINSTRET = 0xB02,

    MHMPCOUNTER03 = 0xB03,
    MHMPCOUNTER04 = 0xB04,
    MHMPCOUNTER05 = 0xB05,
    MHMPCOUNTER06 = 0xB06,
    MHMPCOUNTER07 = 0xB07,
    MHMPCOUNTER08 = 0xB08,
    MHMPCOUNTER09 = 0xB09,
    MHMPCOUNTER10 = 0xB0A,
    MHMPCOUNTER11 = 0xB0B,
    MHMPCOUNTER12 = 0xB0C,
    MHMPCOUNTER13 = 0xB0D,
    MHMPCOUNTER14 = 0xB0E,
    MHMPCOUNTER15 = 0xB0F,
    MHMPCOUNTER16 = 0xB10,
    MHMPCOUNTER17 = 0xB11,
    MHMPCOUNTER18 = 0xB12,
    MHMPCOUNTER19 = 0xB13,
    MHMPCOUNTER20 = 0xB14,
    MHMPCOUNTER21 = 0xB15,
    MHMPCOUNTER22 = 0xB16,
    MHMPCOUNTER23 = 0xB17,
    MHMPCOUNTER24 = 0xB18,
    MHMPCOUNTER25 = 0xB19,
    MHMPCOUNTER26 = 0xB1A,
    MHMPCOUNTER27 = 0xB1B,
    MHMPCOUNTER28 = 0xB1C,
    MHMPCOUNTER29 = 0xB1D,
    MHMPCOUNTER30 = 0xB1E,
    MHMPCOUNTER31 = 0xB1F,

    MCYCLEH = 0xB80,
    MINSTRETH = 0xB82,

    MHMPCOUNTER03H = 0xB83,
    MHMPCOUNTER04H = 0xB84,
    MHMPCOUNTER05H = 0xB85,
    MHMPCOUNTER06H = 0xB86,
    MHMPCOUNTER07H = 0xB87,
    MHMPCOUNTER08H = 0xB88,
    MHMPCOUNTER09H = 0xB89,
    MHMPCOUNTER10H = 0xB8A,
    MHMPCOUNTER11H = 0xB8B,
    MHMPCOUNTER12H = 0xB8C,
    MHMPCOUNTER13H = 0xB8D,
    MHMPCOUNTER14H = 0xB8E,
    MHMPCOUNTER15H = 0xB8F,
    MHMPCOUNTER16H = 0xB90,
    MHMPCOUNTER17H = 0xB91,
    MHMPCOUNTER18H = 0xB92,
    MHMPCOUNTER19H = 0xB93,
    MHMPCOUNTER20H = 0xB94,
    MHMPCOUNTER21H = 0xB95,
    MHMPCOUNTER22H = 0xB96,
    MHMPCOUNTER23H = 0xB97,
    MHMPCOUNTER24H = 0xB98,
    MHMPCOUNTER25H = 0xB99,
    MHMPCOUNTER26H = 0xB9A,
    MHMPCOUNTER27H = 0xB9B,
    MHMPCOUNTER28H = 0xB9C,
    MHMPCOUNTER29H = 0xB9D,
    MHMPCOUNTER30H = 0xB9E,
    MHMPCOUNTER31H = 0xB9F,

    MCOUNTINHIBIT = 0x320,

    MHPEVENT03 = 0x323,
    MHPEVENT04 = 0x324,
    MHPEVENT05 = 0x325,
    MHPEVENT06 = 0x326,
    MHPEVENT07 = 0x327,
    MHPEVENT08 = 0x328,
    MHPEVENT09 = 0x329,
    MHPEVENT10 = 0x32a,
    MHPEVENT11 = 0x32b,
    MHPEVENT12 = 0x32c,
    MHPEVENT13 = 0x32d,
    MHPEVENT14 = 0x32e,
    MHPEVENT15 = 0x32f,
    MHPEVENT16 = 0x330,
    MHPEVENT17 = 0x331,
    MHPEVENT18 = 0x332,
    MHPEVENT19 = 0x333,
    MHPEVENT20 = 0x334,
    MHPEVENT21 = 0x335,
    MHPEVENT22 = 0x336,
    MHPEVENT23 = 0x337,
    MHPEVENT24 = 0x338,
    MHPEVENT25 = 0x339,
    MHPEVENT26 = 0x33a,
    MHPEVENT27 = 0x33b,
    MHPEVENT28 = 0x33c,
    MHPEVENT29 = 0x33d,
    MHPEVENT30 = 0x33e,
    MHPEVENT31 = 0x33f,

    TSELECT = 0x7A0,
    TDATA1 = 0x7A1,
    TDATA2 = 0x7A2,
    TDATA3 = 0x7A3,

    DCSR = 0x7B0,
    DPC = 0x7B1,
    DSCRATCH0 = 0x7B2,
    DSCRATCH1 = 0x7B3,
}

impl CsrId {
    pub fn mode(&self) -> u8 {
        ((*self as u16) >> 10) as u8
    }

    pub fn level(&self) -> u8 {
        (((*self as u16) >> 8) & 0b11) as u8
    }
}

impl From<u16> for CsrId {
    fn from(value:u16) -> CsrId {
        match value {
            0x000 => CsrId::USTATUS ,
            0x004 => CsrId::UIE ,
            0x005 => CsrId::UTVEC ,
            0x040 => CsrId::USCRATCH ,
            0x041 => CsrId::UEPC ,
            0x042 => CsrId::UCAUSE ,
            0x043 => CsrId::UTVAL ,
            0x044 => CsrId::UIP ,
            0x001 => CsrId::FFLAGS ,
            0x002 => CsrId::FRM ,
            0x003 => CsrId::FCSR ,
            0xC00 => CsrId::CYCLE ,
            0xC01 => CsrId::TIME ,
            0xC02 => CsrId::INSTRET ,
            0xC03 => CsrId::HPMCOUNTER03 ,
            0xC04 => CsrId::HPMCOUNTER04 ,
            0xC05 => CsrId::HPMCOUNTER05 ,
            0xC06 => CsrId::HPMCOUNTER06 ,
            0xC07 => CsrId::HPMCOUNTER07 ,
            0xC08 => CsrId::HPMCOUNTER08 ,
            0xC09 => CsrId::HPMCOUNTER09 ,
            0xC0A => CsrId::HPMCOUNTER10 ,
            0xC0B => CsrId::HPMCOUNTER11 ,
            0xC0C => CsrId::HPMCOUNTER12 ,
            0xC0D => CsrId::HPMCOUNTER13 ,
            0xC0E => CsrId::HPMCOUNTER14 ,
            0xC0F => CsrId::HPMCOUNTER15 ,
            0xC10 => CsrId::HPMCOUNTER16 ,
            0xC11 => CsrId::HPMCOUNTER17 ,
            0xC12 => CsrId::HPMCOUNTER18 ,
            0xC13 => CsrId::HPMCOUNTER19 ,
            0xC14 => CsrId::HPMCOUNTER20 ,
            0xC15 => CsrId::HPMCOUNTER21 ,
            0xC16 => CsrId::HPMCOUNTER22 ,
            0xC17 => CsrId::HPMCOUNTER23 ,
            0xC18 => CsrId::HPMCOUNTER24 ,
            0xC19 => CsrId::HPMCOUNTER25 ,
            0xC1A => CsrId::HPMCOUNTER26 ,
            0xC1B => CsrId::HPMCOUNTER27 ,
            0xC1C => CsrId::HPMCOUNTER28 ,
            0xC1D => CsrId::HPMCOUNTER29 ,
            0xC1E => CsrId::HPMCOUNTER30 ,
            0xC1F => CsrId::HPMCOUNTER31 ,
            0xC80 => CsrId::CYCLEH ,
            0xC81 => CsrId::TIMEH ,
            0xC82 => CsrId::INSTRETH ,
            0xC83 => CsrId::HPMCOUNTER03H ,
            0xC84 => CsrId::HPMCOUNTER04H ,
            0xC85 => CsrId::HPMCOUNTER05H ,
            0xC86 => CsrId::HPMCOUNTER06H ,
            0xC87 => CsrId::HPMCOUNTER07H ,
            0xC88 => CsrId::HPMCOUNTER08H ,
            0xC89 => CsrId::HPMCOUNTER09H ,
            0xC8A => CsrId::HPMCOUNTER10H ,
            0xC8B => CsrId::HPMCOUNTER11H ,
            0xC8C => CsrId::HPMCOUNTER12H ,
            0xC8D => CsrId::HPMCOUNTER13H ,
            0xC8E => CsrId::HPMCOUNTER14H ,
            0xC8F => CsrId::HPMCOUNTER15H ,
            0xC90 => CsrId::HPMCOUNTER16H ,
            0xC91 => CsrId::HPMCOUNTER17H ,
            0xC92 => CsrId::HPMCOUNTER18H ,
            0xC93 => CsrId::HPMCOUNTER19H ,
            0xC94 => CsrId::HPMCOUNTER20H ,
            0xC95 => CsrId::HPMCOUNTER21H ,
            0xC96 => CsrId::HPMCOUNTER22H ,
            0xC97 => CsrId::HPMCOUNTER23H ,
            0xC98 => CsrId::HPMCOUNTER24H ,
            0xC99 => CsrId::HPMCOUNTER25H ,
            0xC9A => CsrId::HPMCOUNTER26H ,
            0xC9B => CsrId::HPMCOUNTER27H ,
            0xC9C => CsrId::HPMCOUNTER28H ,
            0xC9D => CsrId::HPMCOUNTER29H ,
            0xC9E => CsrId::HPMCOUNTER30H ,
            0xC9F => CsrId::HPMCOUNTER31H ,
            0x100 => CsrId::SSTATUS ,
            0x102 => CsrId::SEDELEG ,
            0x103 => CsrId::SIDELEG ,
            0x104 => CsrId::SIE ,
            0x105 => CsrId::STVEC ,
            0x106 => CsrId::SCOUNTEREN ,
            0x140 => CsrId::SSCRATCH ,
            0x141 => CsrId::SEPC ,
            0x142 => CsrId::SCAUSE ,
            0x143 => CsrId::STVAL ,
            0x144 => CsrId::SIP ,
            0x180 => CsrId::SATP ,
            0xA00 => CsrId::HSTATUS ,
            0xA02 => CsrId::HEDELEG ,
            0xA03 => CsrId::HIDELEG ,
            0xA80 => CsrId::HGATP ,
            0x200 => CsrId::BSSTATUS ,
            0x204 => CsrId::BSIE ,
            0x205 => CsrId::BSTVEC ,
            0x240 => CsrId::BSSCRATCH ,
            0x241 => CsrId::BSEPC ,
            0x242 => CsrId::BSCAUSE ,
            0x243 => CsrId::BSTVAL ,
            0x244 => CsrId::BSIP ,
            0x280 => CsrId::BSATP ,
            0xF11 => CsrId::MVENDORID ,
            0xF12 => CsrId::MARCHID ,
            0xF13 => CsrId::MIMPID ,
            0xF14 => CsrId::MHARTID ,
            0x300 => CsrId::MSTATUS ,
            0x301 => CsrId::MISA ,
            0x302 => CsrId::MEDELEG ,
            0x303 => CsrId::MIDELEG ,
            0x304 => CsrId::MIE ,
            0x305 => CsrId::MTVEC ,
            0x306 => CsrId::MCOUNTEREN ,
            0x340 => CsrId::MSCRATCH ,
            0x341 => CsrId::MEPC ,
            0x342 => CsrId::MCAUSE ,
            0x343 => CsrId::MTVAL ,
            0x344 => CsrId::MIP ,
            0x3A0 => CsrId::PMPCFG0 ,
            0x3A1 => CsrId::PMPCFG1 ,
            0x3A2 => CsrId::PMPCFG2 ,
            0x3A3 => CsrId::PMPCFG3 ,
            0x3B0 => CsrId::PMPADDR00 ,
            0x3B1 => CsrId::PMPADDR01 ,
            0x3B2 => CsrId::PMPADDR02 ,
            0x3B3 => CsrId::PMPADDR03 ,
            0x3B4 => CsrId::PMPADDR04 ,
            0x3B5 => CsrId::PMPADDR05 ,
            0x3B6 => CsrId::PMPADDR06 ,
            0x3B7 => CsrId::PMPADDR07 ,
            0x3B8 => CsrId::PMPADDR08 ,
            0x3B9 => CsrId::PMPADDR09 ,
            0x3BA => CsrId::PMPADDR10 ,
            0x3BB => CsrId::PMPADDR11 ,
            0x3BC => CsrId::PMPADDR12 ,
            0x3BD => CsrId::PMPADDR13 ,
            0x3BE => CsrId::PMPADDR14 ,
            0x3BF => CsrId::PMPADDR15 ,
            0xB00 => CsrId::MCYCLE ,
            0xB02 => CsrId::MINSTRET ,
            0xB03 => CsrId::MHMPCOUNTER03 ,
            0xB04 => CsrId::MHMPCOUNTER04 ,
            0xB05 => CsrId::MHMPCOUNTER05 ,
            0xB06 => CsrId::MHMPCOUNTER06 ,
            0xB07 => CsrId::MHMPCOUNTER07 ,
            0xB08 => CsrId::MHMPCOUNTER08 ,
            0xB09 => CsrId::MHMPCOUNTER09 ,
            0xB0A => CsrId::MHMPCOUNTER10 ,
            0xB0B => CsrId::MHMPCOUNTER11 ,
            0xB0C => CsrId::MHMPCOUNTER12 ,
            0xB0D => CsrId::MHMPCOUNTER13 ,
            0xB0E => CsrId::MHMPCOUNTER14 ,
            0xB0F => CsrId::MHMPCOUNTER15 ,
            0xB10 => CsrId::MHMPCOUNTER16 ,
            0xB11 => CsrId::MHMPCOUNTER17 ,
            0xB12 => CsrId::MHMPCOUNTER18 ,
            0xB13 => CsrId::MHMPCOUNTER19 ,
            0xB14 => CsrId::MHMPCOUNTER20 ,
            0xB15 => CsrId::MHMPCOUNTER21 ,
            0xB16 => CsrId::MHMPCOUNTER22 ,
            0xB17 => CsrId::MHMPCOUNTER23 ,
            0xB18 => CsrId::MHMPCOUNTER24 ,
            0xB19 => CsrId::MHMPCOUNTER25 ,
            0xB1A => CsrId::MHMPCOUNTER26 ,
            0xB1B => CsrId::MHMPCOUNTER27 ,
            0xB1C => CsrId::MHMPCOUNTER28 ,
            0xB1D => CsrId::MHMPCOUNTER29 ,
            0xB1E => CsrId::MHMPCOUNTER30 ,
            0xB1F => CsrId::MHMPCOUNTER31 ,
            0xB80 => CsrId::MCYCLEH ,
            0xB82 => CsrId::MINSTRETH ,
            0xB83 => CsrId::MHMPCOUNTER03H ,
            0xB84 => CsrId::MHMPCOUNTER04H ,
            0xB85 => CsrId::MHMPCOUNTER05H ,
            0xB86 => CsrId::MHMPCOUNTER06H ,
            0xB87 => CsrId::MHMPCOUNTER07H ,
            0xB88 => CsrId::MHMPCOUNTER08H ,
            0xB89 => CsrId::MHMPCOUNTER09H ,
            0xB8A => CsrId::MHMPCOUNTER10H ,
            0xB8B => CsrId::MHMPCOUNTER11H ,
            0xB8C => CsrId::MHMPCOUNTER12H ,
            0xB8D => CsrId::MHMPCOUNTER13H ,
            0xB8E => CsrId::MHMPCOUNTER14H ,
            0xB8F => CsrId::MHMPCOUNTER15H ,
            0xB90 => CsrId::MHMPCOUNTER16H ,
            0xB91 => CsrId::MHMPCOUNTER17H ,
            0xB92 => CsrId::MHMPCOUNTER18H ,
            0xB93 => CsrId::MHMPCOUNTER19H ,
            0xB94 => CsrId::MHMPCOUNTER20H ,
            0xB95 => CsrId::MHMPCOUNTER21H ,
            0xB96 => CsrId::MHMPCOUNTER22H ,
            0xB97 => CsrId::MHMPCOUNTER23H ,
            0xB98 => CsrId::MHMPCOUNTER24H ,
            0xB99 => CsrId::MHMPCOUNTER25H ,
            0xB9A => CsrId::MHMPCOUNTER26H ,
            0xB9B => CsrId::MHMPCOUNTER27H ,
            0xB9C => CsrId::MHMPCOUNTER28H ,
            0xB9D => CsrId::MHMPCOUNTER29H ,
            0xB9E => CsrId::MHMPCOUNTER30H ,
            0xB9F => CsrId::MHMPCOUNTER31H ,
            0x320 => CsrId::MCOUNTINHIBIT ,
            0x323 => CsrId::MHPEVENT03 ,
            0x324 => CsrId::MHPEVENT04 ,
            0x325 => CsrId::MHPEVENT05 ,
            0x326 => CsrId::MHPEVENT06 ,
            0x327 => CsrId::MHPEVENT07 ,
            0x328 => CsrId::MHPEVENT08 ,
            0x329 => CsrId::MHPEVENT09 ,
            0x32a => CsrId::MHPEVENT10 ,
            0x32b => CsrId::MHPEVENT11 ,
            0x32c => CsrId::MHPEVENT12 ,
            0x32d => CsrId::MHPEVENT13 ,
            0x32e => CsrId::MHPEVENT14 ,
            0x32f => CsrId::MHPEVENT15 ,
            0x330 => CsrId::MHPEVENT16 ,
            0x331 => CsrId::MHPEVENT17 ,
            0x332 => CsrId::MHPEVENT18 ,
            0x333 => CsrId::MHPEVENT19 ,
            0x334 => CsrId::MHPEVENT20 ,
            0x335 => CsrId::MHPEVENT21 ,
            0x336 => CsrId::MHPEVENT22 ,
            0x337 => CsrId::MHPEVENT23 ,
            0x338 => CsrId::MHPEVENT24 ,
            0x339 => CsrId::MHPEVENT25 ,
            0x33a => CsrId::MHPEVENT26 ,
            0x33b => CsrId::MHPEVENT27 ,
            0x33c => CsrId::MHPEVENT28 ,
            0x33d => CsrId::MHPEVENT29 ,
            0x33e => CsrId::MHPEVENT30 ,
            0x33f => CsrId::MHPEVENT31 ,
            0x7A0 => CsrId::TSELECT ,
            0x7A1 => CsrId::TDATA1 ,
            0x7A2 => CsrId::TDATA2 ,
            0x7A3 => CsrId::TDATA3 ,
            0x7B0 => CsrId::DCSR ,
            0x7B1 => CsrId::DPC ,
            0x7B2 => CsrId::DSCRATCH0 ,
            0x7B3 => CsrId::DSCRATCH1 ,
            _ => panic!("Bad CsrId value"),
        }
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
