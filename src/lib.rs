//! This crate is used for educational purposes only. Clone the
//! [github repository](https://github.com/ablanleuil/rust_riscv) and create
//! anything you want on top of this base. This crate was created only with the
//! [RISC-V ISA specification](https://riscv.org/specifications/).

/// The ISA module containing everything related to instruction format.
pub mod isa;

/// Contains implementations of simple RISC-V machines based on the standard.
pub mod machine;

/// Memory interface abstraction used to implement any memory interface you want.
pub mod memory;

/// Helper for MachineInteger traits constraints
pub mod types;
