extern crate riscv_sandbox;
extern crate elf as elflib;

use riscv_sandbox::elf;

#[test]
fn get_main_pc() {
    let file = elflib::File::open_path("resources/executables/function")
        .unwrap();
    assert_eq!(elf::get_main_pc(&file), Some(0x10228));
}
