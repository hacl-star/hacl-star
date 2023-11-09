pub fn felem_add(a: &mut [u64], b: &mut [u64], out: &mut [u64]) -> ()
{
    crate::hacl::bignum_k256::fadd(out, a, b);
    crate::hacl::bignum_k256::fnormalize_weak(out, out)
}

pub fn felem_sub(a: &mut [u64], b: &mut [u64], out: &mut [u64]) -> ()
{
    crate::hacl::bignum_k256::fsub(out, a, b, 2u64);
    crate::hacl::bignum_k256::fnormalize_weak(out, out)
}

pub fn felem_mul(a: &mut [u64], b: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::bignum_k256::fmul(out, a, b) }

pub fn felem_sqr(a: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::bignum_k256::fsqr(out, a) }

pub fn felem_inv(a: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::bignum_k256::finv(out, a) }

pub fn felem_load(b: &mut [u8], out: &mut [u64]) -> ()
{ crate::hacl::bignum_k256::load_felem(out, b) }

pub fn felem_store(a: &mut [u64], out: &mut [u8]) -> ()
{
    let mut tmp: [u64; 5] = [0u64; 5u32 as usize];
    crate::hacl::bignum_k256::fnormalize(&mut tmp, a);
    crate::hacl::bignum_k256::store_felem(out, &mut tmp)
}

pub fn mk_point_at_inf(p: &mut [u64]) -> ()
{ crate::hacl::impl::k256::point::make_point_at_inf(p) }

pub fn point_negate(p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::k256_ecdsa::point_negate(out, p) }

pub fn point_add(p: &mut [u64], q: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::k256_ecdsa::point_add(out, p, q) }

pub fn point_double(p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::k256_ecdsa::point_double(out, p) }

pub fn point_mul(scalar: &mut [u8], p: &mut [u64], out: &mut [u64]) -> ()
{
    let mut scalar_q: [u64; 4] = [0u64; 4u32 as usize];
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = (&mut scalar_q).split_at_mut(0usize);
        let u: u64 =
            crate::lowstar::endianness::load64_be(
                &mut scalar[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
            );
        let x: u64 = u;
        os.1[i as usize] = x
    };
    crate::hacl::impl::k256::pointmul::point_mul(out, &mut scalar_q, p)
}

pub fn point_store(p: &mut [u64], out: &mut [u8]) -> ()
{ crate::hacl::k256_ecdsa::point_store(out, p) }

pub fn is_point_valid(b: &mut [u8]) -> bool
{
    let mut p: [u64; 10] = [0u64; 10u32 as usize];
    let res: bool = crate::hacl::k256_ecdsa::aff_point_load_vartime(&mut p, b);
    res
}