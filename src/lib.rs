#![feature(vec_remove_item)]
//! This crate is used for educational purposes only. Clone the
//! [github repository](https://github.com/ablanleuil/rust_riscv) and create
//! anything you want on top of this base. This crate was created only with the
//! [RISC-V ISA specification](https://riscv.org/specifications/).

extern crate elf as elflib;
extern crate crossbeam;

/// The ISA module containing everything related to instruction format.
pub mod isa;

/// Contains implementations of simple RISC-V machines based on the standard.
/// Also contains traits to use if you want to implement your own machine.
pub mod machine;

/// Memory interface abstraction used to implement any memory interface you want.
pub mod memory;

/// Types used for flexibility in simulator's traits datatypes
pub mod types;

/// Helper functions for elf file reading
pub mod elf;

pub use std::thread;
