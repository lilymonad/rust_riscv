extern crate riscv_sandbox;

use riscv_sandbox::isa::Instruction;

fn main() {
    println!("{}", Instruction::addi(0, 1, 128))
}
