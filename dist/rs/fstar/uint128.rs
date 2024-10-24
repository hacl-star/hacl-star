#![allow(non_camel_case_types)]

pub type uint128 = u128;

pub fn add(x: uint128, y: uint128) -> uint128 {
    x.wrapping_add(y)
}
pub fn add_mod(x: uint128, y: uint128) -> uint128 {
    x.wrapping_add(y)
}
pub fn sub(x: uint128, y: uint128) -> uint128 {
    x.wrapping_sub(y)
}
pub fn sub_mod(x: uint128, y: uint128) -> uint128 {
    x.wrapping_sub(y)
}
pub fn logand(x: uint128, y: uint128) -> uint128 {
    x & y
}
pub fn logxor(x: uint128, y: uint128) -> uint128 {
    x ^ y
}
pub fn logor(x: uint128, y: uint128) -> uint128 {
    x | y
}
pub fn lognot(x: uint128) -> uint128 {
    !x
}
pub fn shift_left(x: uint128, y: u32) -> uint128 {
    x.wrapping_shl(y)
}
pub fn shift_right(x: uint128, y: u32) -> uint128 {
    x.wrapping_shr(y)
}
pub fn eq(x: uint128, y: uint128) -> bool {
    x == y
}
pub fn gt(x: uint128, y: uint128) -> bool {
    x > y
}
pub fn lt(x: uint128, y: uint128) -> bool {
    x < y
}
pub fn gte(x: uint128, y: uint128) -> bool {
    x >= y
}
pub fn lte(x: uint128, y: uint128) -> bool {
    x <= y
}
pub fn eq_mask(a: uint128, b: uint128) -> uint128 {
    let x = a ^ b;
    let minus_x = (!x).wrapping_add(1u128);
    let x_or_minus_x = x | minus_x;
    let xnx = x_or_minus_x.wrapping_shr(127);
    xnx.wrapping_sub(1u128)
}
pub fn gte_mask(a: uint128, b: uint128) -> uint128 {
    let x = a;
    let y = b;
    let x_xor_y = x ^ y;
    let x_sub_y = x.wrapping_sub(y);
    let x_sub_y_xor_y = x_sub_y ^ y;
    let q = x_xor_y | x_sub_y_xor_y;
    let x_xor_q = x ^ q;
    let x_xor_q_ = x_xor_q.wrapping_shr(127);
    x_xor_q_.wrapping_sub(1u128)
}
pub fn uint64_to_uint128(x: u64) -> uint128 {
    x as u128
}
pub fn uint128_to_uint64(x: uint128) -> u64 {
    x as u64
}
pub fn mul32(x: u64, y: u32) -> uint128 {
    (x as u128) * (y as u128)
}
pub fn mul_wide(x: u64, y: u64) -> uint128 {
    (x as u128) * (y as u128)
}
