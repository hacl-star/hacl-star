#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn mk_felem_zero(b: &mut [u64]) -> ()
{
    b[0usize] = 0u64;
    b[1usize] = 0u64;
    b[2usize] = 0u64;
    b[3usize] = 0u64;
    b[4usize] = 0u64
}

pub fn mk_felem_one(b: &mut [u64]) -> ()
{
    b[0usize] = 1u64;
    b[1usize] = 0u64;
    b[2usize] = 0u64;
    b[3usize] = 0u64;
    b[4usize] = 0u64
}

pub fn felem_add(a: &mut [u64], b: &mut [u64], out: &mut [u64]) -> ()
{
    crate::hacl::bignum25519_51::fadd(out, a, b);
    crate::hacl::ed25519::reduce_513(out)
}

pub fn felem_sub(a: &mut [u64], b: &mut [u64], out: &mut [u64]) -> ()
{
    crate::hacl::bignum25519_51::fsub(out, a, b);
    crate::hacl::ed25519::reduce_513(out)
}

pub fn felem_mul(a: &mut [u64], b: &mut [u64], out: &mut [u64]) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 10] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 10usize];
    crate::hacl::bignum25519_51::fmul(out, a, b, &mut tmp)
}

pub fn felem_sqr(a: &mut [u64], out: &mut [u64]) -> ()
{
    let mut tmp: [crate::fstar::uint128::uint128; 5] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 5usize];
    crate::hacl::bignum25519_51::fsqr(out, a, &mut tmp)
}

pub fn felem_inv(a: &mut [u64], out: &mut [u64]) -> ()
{
    crate::hacl::ed25519::inverse(out, a);
    crate::hacl::ed25519::reduce_513(out)
}

pub fn felem_load(b: &mut [u8], out: &mut [u64]) -> ()
{ crate::hacl::ed25519::load_51(out, b) }

pub fn felem_store(a: &mut [u64], out: &mut [u8]) -> ()
{ crate::hacl::ed25519::store_51(out, a) }

pub fn mk_point_at_inf(p: &mut [u64]) -> () { crate::hacl::ed25519::make_point_inf(p) }

pub fn mk_base_point(p: &mut [u64]) -> ()
{
    let gx: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
    let gy: (&mut [u64], &mut [u64]) = gx.1.split_at_mut(5usize);
    let gz: (&mut [u64], &mut [u64]) = gy.1.split_at_mut(5usize);
    let gt: (&mut [u64], &mut [u64]) = gz.1.split_at_mut(5usize);
    gy.0[0usize] = 0x00062d608f25d51au64;
    gy.0[1usize] = 0x000412a4b4f6592au64;
    gy.0[2usize] = 0x00075b7171a4b31du64;
    gy.0[3usize] = 0x0001ff60527118feu64;
    gy.0[4usize] = 0x000216936d3cd6e5u64;
    gz.0[0usize] = 0x0006666666666658u64;
    gz.0[1usize] = 0x0004ccccccccccccu64;
    gz.0[2usize] = 0x0001999999999999u64;
    gz.0[3usize] = 0x0003333333333333u64;
    gz.0[4usize] = 0x0006666666666666u64;
    gt.0[0usize] = 1u64;
    gt.0[1usize] = 0u64;
    gt.0[2usize] = 0u64;
    gt.0[3usize] = 0u64;
    gt.0[4usize] = 0u64;
    gt.1[0usize] = 0x00068ab3a5b7dda3u64;
    gt.1[1usize] = 0x00000eea2a5eadbbu64;
    gt.1[2usize] = 0x0002af8df483c27eu64;
    gt.1[3usize] = 0x000332b375274732u64;
    gt.1[4usize] = 0x00067875f0fd78b7u64
}

pub fn point_negate(p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::ed25519::point_negate(p, out) }

pub fn point_add(p: &mut [u64], q: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::ed25519::point_add(out, p, q) }

pub fn point_double(p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::ed25519::point_double(out, p) }

pub fn point_mul(scalar: &mut [u8], p: &mut [u64], out: &mut [u64]) -> ()
{ crate::hacl::ed25519::point_mul(out, scalar, p) }

pub fn point_eq(p: &mut [u64], q: &mut [u64]) -> bool
{ crate::hacl::ed25519::point_equal(p, q) }

pub fn point_compress(p: &mut [u64], out: &mut [u8]) -> ()
{ crate::hacl::ed25519::point_compress(out, p) }

pub fn point_decompress(s: &mut [u8], out: &mut [u64]) -> bool
{ crate::hacl::ed25519::point_decompress(out, s) }
