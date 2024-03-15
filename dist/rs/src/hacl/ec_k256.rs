#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn mk_felem_zero(f: &mut [u64]) -> ()
{ (f[0usize..5usize]).copy_from_slice(&[0u64; 5usize]) }

pub fn mk_felem_one(f: &mut [u64]) -> ()
{
    (f[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    f[0usize] = 1u64
}

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
    let mut tmp: [u64; 5] = [0u64; 5usize];
    crate::hacl::bignum_k256::fnormalize(&mut tmp, a);
    crate::hacl::bignum_k256::store_felem(out, &mut tmp)
}

pub fn mk_point_at_inf(p: &mut [u64]) -> () { crate::hacl::k256_ecdsa::make_point_at_inf(p) }

pub fn mk_base_point(p: &mut [u64]) -> ()
{
    let gx: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = gx.1.split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = gy.1.split_at_mut(5usize);
    gy.0[0usize] = 0x2815b16f81798u64;
    gy.0[1usize] = 0xdb2dce28d959fu64;
    gy.0[2usize] = 0xe870b07029bfcu64;
    gy.0[3usize] = 0xbbac55a06295cu64;
    gy.0[4usize] = 0x79be667ef9dcu64;
    gz.0[0usize] = 0x7d08ffb10d4b8u64;
    gz.0[1usize] = 0x48a68554199c4u64;
    gz.0[2usize] = 0xe1108a8fd17b4u64;
    gz.0[3usize] = 0xc4655da4fbfc0u64;
    gz.0[4usize] = 0x483ada7726a3u64;
    (gz.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    gz.1[0usize] = 1u64
}

pub fn point_negate(p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::k256_ecdsa::point_negate(out, p) }

pub fn point_add(p: &mut [u64], q: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::k256_ecdsa::point_add(out, p, q) }

pub fn point_double(p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::k256_ecdsa::point_double(out, p) }

pub fn point_mul(scalar: &mut [u8], p: &mut [u64], out: &mut [u64]) -> ()
{
    let mut scalar_q: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let u: u64 =
            crate::lowstar::endianness::load64_be(
                &mut scalar[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
            );
        let x: u64 = u;
        let os: (&mut [u64], &mut [u64]) = (&mut scalar_q).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    crate::hacl::k256_ecdsa::point_mul(out, &mut scalar_q, p)
}

pub fn point_store(p: &mut [u64], out: &mut [u8]) -> ()
{ crate::hacl::k256_ecdsa::point_store(out, p) }

pub fn point_load(b: &mut [u8], out: &mut [u64]) -> ()
{
    let mut p_aff: [u64; 10] = [0u64; 10usize];
    let px: (&mut [u64], &mut [u64]) = (&mut p_aff).split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(5usize);
    let pxb: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    let pyb: (&mut [u8], &mut [u8]) = pxb.1.split_at_mut(32usize);
    crate::hacl::bignum_k256::load_felem(py.0, pyb.0);
    crate::hacl::bignum_k256::load_felem(py.1, pyb.1);
    let x: (&mut [u64], &mut [u64]) = py.0.split_at_mut(0usize);
    let y: (&mut [u64], &mut [u64]) = py.1.split_at_mut(0usize);
    let x1: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
    let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
    (y1.0[0usize..5usize]).copy_from_slice(&x.1[0usize..5usize]);
    (z1.0[0usize..5usize]).copy_from_slice(&y.1[0usize..5usize]);
    (z1.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    z1.1[0usize] = 1u64
}

pub fn is_point_valid(b: &mut [u8]) -> bool
{
    let mut p: [u64; 10] = [0u64; 10usize];
    let res: bool = crate::hacl::k256_ecdsa::aff_point_load_vartime(&mut p, b);
    res
}
