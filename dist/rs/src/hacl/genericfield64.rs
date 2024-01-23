#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

pub fn field_modulus_check(len: u32, n: &mut [u64]) -> bool
{
    let m: u64 = crate::hacl::bignum::bn_check_modulus_u64(len, n);
    m == 0xFFFFFFFFFFFFFFFFu64
}
