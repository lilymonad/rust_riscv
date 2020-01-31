extern crate elf as elflib;
extern crate riscv_sandbox;
#[macro_use]
extern crate clap;

use clap::Values;
use riscv_sandbox::elf;

fn main() {
    let conf = clap_app!(myapp =>
        (@arg file: +required +takes_value "The executable to read")
    ).get_matches();

    let name = conf.value_of("file").unwrap();
    let file = elflib::File::open_path(&name).expect("Couldn't open executable file");

    let mut memory : Vec<u8> = Vec::new();
    //elf::load_dependencies(&file, &mut memory).unwrap();
}
