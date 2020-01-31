extern crate riscv_sandbox;
#[macro_use]
extern crate clap;

use clap::Values;

fn main() {
    let conf = clap_app!(myapp =>
        (version: "1.0")
        (author: "Arthur Blanleuil")
        (about: "A simple example of clap usage")
        (@arg TPW: +required +takes_value "Sets the number of threads per warps")
        (@arg NBW: +required +takes_value "Sets the number of warps")
        (@arg monitored: -m --monitor [pc]... "Provide a list of pc to parse")
        (@arg command: * ... "The command to run")
    ).get_matches();

    let tpw : usize = conf.value_of("TPW").unwrap().parse()
        .expect("TPW must be a number");
    let nbw : usize = conf.value_of("NBW").unwrap().parse()
        .expect("NBW must be a number");
    let monitored = conf.values_of("monitored")
        .or(Some(Values::default())).unwrap();
    println!("{} {} {:?}", tpw, nbw, monitored);
}
