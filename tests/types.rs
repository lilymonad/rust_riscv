extern crate riscv_sandbox;
use riscv_sandbox::types::*;

#[test]
fn bits() {
    let bitset : u32 = 0b0010110;
    let vec = vec![false, true, true, false, true, false, false];
    for (x, y) in bitset.bits().zip(vec.into_iter()) {
        assert_eq!(x, y)
    }
}

#[test]
fn zeroes() {
    let bitset : u32 = 0b0010110;
    let vec : Vec<u32> = vec![0, 3, 5, 6];
    for (x, y) in bitset.bits().zeroes().zip(vec.into_iter()) {
        assert_eq!(x, y)
    }
}

#[test]
fn ones() {
    let bitset : u32 = 0b0010110;
    let vec : Vec<u32> = vec![1, 2, 4];
    for (x, y) in bitset.bits().ones().zip(vec.into_iter()) {
        assert_eq!(x, y)
    }
}

#[test]
fn count_ones() {
    let bitset : u32 = 0x99999999;
    assert_eq!(bitset.bits().ones().count(), 16);
    assert_eq!(bitset.bits().take(16).ones().count(), 8)
}


