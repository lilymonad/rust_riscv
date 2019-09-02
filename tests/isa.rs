extern crate riscv_sandbox;

use riscv_sandbox::isa::{Instruction, OpCode};

#[test]
fn r_ctor() {
    let i = Instruction::create_r(OpCode::JAL, 2, 3, 4, 0b11111);
    assert_eq!(i.get_opcode(), OpCode::JAL.into());
    assert_eq!(i.get_rd(), 2);
    assert_eq!(i.get_rs1(), 3);
    assert_eq!(i.get_rs2(), 4);
    assert_eq!(i.get_funct10(), 0b11111);
}

#[test]
fn i_ctor() {
    let i = Instruction::create_i(OpCode::JALR, 2, 3, 4, 5);
    assert_eq!(i.get_opcode(), OpCode::JALR.into());
    assert_eq!(i.get_rd(), 2);
    assert_eq!(i.get_rs1(), 3);
    assert_eq!(i.get_imm_i(), 4);
    assert_eq!(i.get_funct3(), 5);
}

#[test]
fn s_ctor() {
    let i = Instruction::create_s(OpCode::AUIPC, 2, 3, 0b111111, 5);
    assert_eq!(i.get_opcode(), OpCode::AUIPC.into());
    assert_eq!(i.get_rs1(), 2);
    assert_eq!(i.get_rs2(), 3);
    assert_eq!(i.get_imm_s(), 0b111111);
    assert_eq!(i.get_funct3(), 5);
}

#[test]
fn u_ctor() {
    let i = Instruction::create_u(OpCode::OPREG, 2, 0xF000);
    assert_eq!(i.get_opcode(), OpCode::OPREG.into());
    assert_eq!(i.get_rd(), 2);
    assert_eq!(i.get_imm_u(), 0xF000);
}

#[test]
fn opcode() {
    let mut i = Instruction(0);
    assert_eq!(i.get_opcode(), 0);

    i.set_opcode(10);
    assert_eq!(i.get_opcode(), 10);
}

#[test]
fn rd() {
    let mut i = Instruction(0);
    assert_eq!(i.get_rd(), 0);

    i.set_rd(10);
    assert_eq!(i.get_rd(), 10);
}

#[test]
fn rs1() {
    let mut i = Instruction(0);
    assert_eq!(i.get_rs1(), 0);
    
    i.set_rs1(10);
    assert_eq!(i.get_rs1(), 10);
}

#[test]
fn rs2() {
    let mut i = Instruction(0);
    assert_eq!(i.get_rs2(), 0);

    i.set_rs2(10);
    assert_eq!(i.get_rs2(), 10);
}

#[test]
fn imm_i() {
    let mut i = Instruction(0);
    assert_eq!(i.get_imm_i(), 0);

    i.set_imm_i(1023);
    assert_eq!(i.get_imm_i(), 1023);
}

#[test]
fn imm_s() {
    let mut i = Instruction(0);
    assert_eq!(i.get_imm_s(), 0);

    i.set_imm_s(1023);
    assert_eq!(i.get_imm_s(), 1023);
}

#[test]
fn imm_b() {
    let mut i = Instruction(0);
    assert_eq!(i.get_imm_b(), 0);

    i.set_imm_b(1023);
    assert_eq!(i.get_imm_b(), 1022);
}

#[test]
fn imm_u() {
    let mut i = Instruction(0);
    assert_eq!(i.get_imm_u(), 0);

    i.set_imm_u(0xABCDE000u32 as i32);
    assert_eq!(i.get_imm_u(), 0xABCDE000u32 as i32);
}

#[test]
fn imm_j() {
    let mut i = Instruction(0);
    assert_eq!(i.get_imm_j(), 0);

    i.set_imm_j(0xABCDF);
    assert_eq!(i.get_imm_j(), 0xABCDE);
}

#[test]
fn addi() {
    let i = Instruction::create_i(OpCode::OPIMM, 1, 1, 128, 0);
    assert_eq!(i.get_rd(), 1);
    assert_eq!(i.get_rs1(), 1);
    assert_eq!(i.get_imm_i(), 128);
    assert_eq!(i.get_opcode(), OpCode::OPIMM.into());
    assert_eq!(i.get_funct3(), 0);
}

#[test]
fn imm_i_bit_extend() {
    let i = Instruction::create_i(OpCode::INVALID, 0, 0, 0xFFF, 0);
    assert_eq!(i.get_imm_i(), 0xFFFFFFFFu32 as i32);
}

#[test]
fn display_i() {
    assert_eq!(format!("{}", Instruction::addi(0, 1, 128)), "addi r0 = r1, 128");
    assert_eq!(format!("{}", Instruction::slti(1, 2, 64)), "slti r1 = r2, 64");
    assert_eq!(format!("{}", Instruction::srai(1, 2, 2)), "srai r1 = r2, 2");
}

#[test]
fn display_r() {
    assert_eq!(format!("{}", Instruction::add(0, 1, 2)), "add r0 = r1, r2");
    assert_eq!(format!("{}", Instruction::sra(0, 1, 2)), "sra r0 = r1, r2");
    assert_eq!(format!("{}", Instruction::and(0, 1, 2)), "and r0 = r1, r2");
}

#[test]
fn display_branch() {
    assert_eq!(format!("{}", Instruction::beq(0, 1, 50)), "beq @pc+50 if r0 $ r1");
    assert_eq!(format!("{}", Instruction::bne(4, 2, 512)), "bne @pc+512 if r4 $ r2");
}
