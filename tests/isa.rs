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

#[test]
fn nop_works() {
    assert_eq!(format!("{}", Instruction::nop()), "addi r0 = r0, 0");
}

#[test]
fn compressed() {
    println!("uncompress : {i:016b} ({i:04x})", i = 0x86aa);
    assert_eq!(
        Instruction(0x86aa).uncompressed()
        , Instruction::add(13, 10, 0)); // mv a3,a0
    println!("uncompress : {i:016b} ({i:04x})", i = 0x041c);
    assert_eq!(
        Instruction(0x041c).uncompressed()
        , Instruction::addi(15, 2, 512)); // addi a5,sp,512
    println!("uncompress : {i:016b} ({i:04x})", i = 0x47a9);
    assert_eq!(
        Instruction(0x47a9).uncompressed()
        , Instruction::addi(15, 0, 10)); // li a5,10 (implemented with addi)
    println!("uncompress : {i:016b} ({i:04x})", i = 0x8082);
    assert_eq!(
        Instruction(0x8082).uncompressed()
        , Instruction::jalr(0, 1, 0)); // ret (jalr x0 x1 0)
    println!("uncompress : {i:016b} ({i:04x})", i = 0xb059);
    assert_eq!(
        Instruction(0xb059).uncompressed()
        , Instruction::jal(0, 0x8460 - 0x8bda)); // j 0x8460
    println!("uncompress : {i:016b} ({i:04x})", i = 0xca26);
    assert_eq!(
        Instruction(0xca26).uncompressed()
        , Instruction::sw(2, 9, 20)); // sw r9,20(r2)
    println!("uncompress : {i:016b} ({i:04x})", i = 0xcd41);
    assert_eq!(
        Instruction(0xcd41).uncompressed()
        , Instruction::beq(10, 0, 0x8ca8 - 0x8c10)); // beq r10 r0 0x8ca8
    println!("uncompress : {i:016b} ({i:04x})", i = 0x6709);
    assert_eq!(
        Instruction(0x6709).uncompressed()
        , Instruction::lui(14, 2 << 12)); // lui r14 0x2
    println!("uncompress : {i:016b} ({i:04x})", i = 0x0405);
    assert_eq!(
        Instruction(0x0405).uncompressed()
        , Instruction::addi(8, 8, 1)); // addi r8,r8,1
    println!("uncompress : {i:016b} ({i:04x})", i = 0x0786);
    assert_eq!(
        Instruction(0x0786).uncompressed()
        , Instruction::slli(15, 15, 1)); // slli r15,r15,1
    println!("uncompress : {i:016b} ({i:04x})", i = 0xfbe5);
    assert_eq!(
        Instruction(0xfbe5).uncompressed()
        , Instruction::bne(15, 0, 0x8c1e - 0x8c2e)); // bne r15 r0 0x8c1e
    println!("uncompress : {i:016b} ({i:04x})", i = 0x8ff1);
    assert_eq!(
        Instruction(0x8ff1).uncompressed()
        , Instruction::and(15, 15, 12)); // and r15,r15,r12
    println!("uncompress : {i:016b} ({i:04x})", i = 0x4462);
    assert_eq!(
        Instruction(0x4462).uncompressed()
        , Instruction::lw(8, 2, 24)); // lw r8,24(r2)

    println!("uncompress : {i:016b} ({i:04x})", i = 0x1101);
    assert_eq!(
        Instruction(0x1101).uncompressed()
        , Instruction::addi(2, 2, -32)); // addi 2,2,-32
    println!("uncompress : {i:016b} ({i:04x})", i = 0xcc22);
    assert_eq!(
        Instruction(0xcc22).uncompressed()
        , Instruction::sw(2, 8, 24)); // sw s0,24(sp)
    println!("uncompress : {i:016b} ({i:04x})", i = 0x6441);
    assert_eq!(
        Instruction(0x6441).uncompressed()
        , Instruction::lui(8, 0x10 << 12)); // lui s0,
    println!("uncompress : {i:016b} ({i:04x})", i = 0x8522);
    assert_eq!(
        Instruction(0x8522).uncompressed()
        , Instruction::add(10,8,0)); // lui s0,0x100x10
    println!("uncompress : {i:016b} ({i:04x})", i = 0x7171);
    assert_eq!(
        Instruction(0x7171).uncompressed()
        , Instruction::addi(2,2,-176)); // addi sp,sp,-176
    println!("uncompress : {i:016b} ({i:04x})", i = 0x35f9);
    assert_eq!(
        Instruction(0x35f9).uncompressed()
        , Instruction::jal(1,0x107b6 - 0x108e8)); // jal r1,0x107b6
    println!("uncompress : {i:016b} ({i:04x})", i = 0xd606);
    assert_eq!(
        Instruction(0xd606).uncompressed()
        , Instruction::sw(2, 1, 44)); // sw r1 44(r2)
    println!("uncompress : {i:016b} ({i:04x})", i = 0x41c8);
    assert_eq!(
        Instruction(0x41c8).uncompressed()
        , Instruction::lw(10, 11, 4)); // lw r10 4(r11)
    println!("uncompress : {i:016b} ({i:04x})", i = 0x4610);
    assert_eq!(
        Instruction(0x4610).uncompressed()
        , Instruction::lw(12, 12, 8)); // lw r12 8(r12)
    println!("uncompress : {i:016b} ({i:04x})", i = 0x9732);
    assert_eq!(
        Instruction(0x9732).uncompressed()
        , Instruction::add(14, 14, 12)); // add a4,a4,a2
    println!("uncompress : {i:016b} ({i:04x})", i = 0x060a);
    assert_eq!(
        Instruction(0x060a).uncompressed()
        , Instruction::slli(12, 12, 2)); // slli a2,a2,0x2
    println!("uncompress : {i:016b} ({i:04x})", i = 0x0605);
    assert_eq!(
        Instruction(0x0605).uncompressed()
        , Instruction::addi(12, 12, 1)); // addi a2,a2,1
    println!("uncompress : {i:016b} ({i:04x})", i = 0x4314);
    assert_eq!(
        Instruction(0x4314).uncompressed()
        , Instruction::lw(13, 14, 0)); // lw a3,0(a4)
    println!("uncompress : {i:016b} ({i:04x})", i = 0x17fd);
    assert_eq!(
        Instruction(0x17fd).uncompressed()
        , Instruction::addi(15, 15, -1)); // addi a5,a5,-1
    println!("uncompress : {i:016b} ({i:04x})", i = 0x9636);
    assert_eq!(
        Instruction(0x9636).uncompressed()
        , Instruction::add(12, 12, 13)); // add a2,a2,a3
}
