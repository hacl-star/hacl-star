pub fn field_modulus_check(len: u32, n: &mut [u64]) -> bool
{
    let m: u64 = crate::hacl::bignum_montgomery::bn_check_modulus_u64(len, n);
    m == 0xFFFFFFFFFFFFFFFFu64
}
