extern crate riscv_sandbox;

use riscv_sandbox::isa::Instruction;

fn main() {
    println!("{}", Instruction(0xf1402573));
    println!("{}", Instruction(0x30002573));
    println!("{}", Instruction::addi(0, 1, 128));
    println!("{}", Instruction(0x8082).uncompressed());
    println!("{}", Instruction(0x1101).uncompressed());
    println!("{}", Instruction(0xcc22).uncompressed());
}
