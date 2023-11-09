pub fn field_modulus_check(len: u32, n: &mut [u32]) -> bool
{
    let m: u32 = crate::hacl::bignum::montgomery::bn_check_modulus_u32(len, n);
    m == 0xFFFFFFFFu32
}

pub fn op_Bang_Star__Hacl_Bignum_MontArithmetic_bn_mont_ctx'  uint32_t* uint32_t(
    p: &mut [crate::hacl::bignum::montarithmetic::bn_mont_ctx_u32]
) ->
    crate::hacl::bignum::montarithmetic::bn_mont_ctx_u32
{ p[0usize] }