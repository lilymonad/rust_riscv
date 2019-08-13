extern crate riscv;

use riscv::machine;

#[test]
fn registers() {
    let mut proc = machine::RV32IMachine::new();

    for i in 0..31 {
        assert_eq!(proc.get_register(i as usize), 0);
        proc.set_register(i as usize, i+1);
    }

    assert_eq!(proc.get_register(0), 0);
    for i in 1..31 {
        assert_eq!(proc.get_register(i as usize), i+1);
    }
}
