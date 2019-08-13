#[derive(Debug)]
pub struct RV32IMachine {
    registers: [i32; 31],
    pc: i32,
}

impl RV32IMachine {

    pub fn new() -> RV32IMachine {
        RV32IMachine { registers : [0; 31], pc: 0 }
    }

    pub fn get_register(&self, i:usize) -> i32 {
        if i <= 0 || i > 31 {
            0
        } else {
            self.registers[i-1]
        }
    }

    pub fn set_register(&mut self, i:usize, x:i32) {
        if i > 0 && i < 32 {
            self.registers[i-1] = x;
        }
    }
}
