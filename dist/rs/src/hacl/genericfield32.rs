pub fn field_modulus_check(len: u32, n: &mut [u32]) -> bool
{
    let m: u32 = crate::hacl::bignum_montgomery::bn_check_modulus_u32(len, n);
    m == 0xFFFFFFFFu32
}
