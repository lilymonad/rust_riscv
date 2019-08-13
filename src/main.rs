mod isa;
mod machine;
mod memory;

use isa::Instruction;
use machine::RV32IMachine;


fn main() {
    let machine = RV32IMachine::new(Box::new(vec![0,0,0,0]));
    let ir = Instruction::r(0, 0, 0, 0, 0);
    let ii = Instruction::i(0, 0, 0, 0, 0);
    let is = Instruction::s(0, 0, 0, 0, 0);
    let iu = Instruction::u(0, 0, 0);

    println!("{:?}, {:?}, {:?}, {:?}", ir, ii, is, iu);
}
