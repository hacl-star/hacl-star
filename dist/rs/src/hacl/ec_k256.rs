#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

/**
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
pub fn
mk_felem_zero(f: &mut [u64])
{ (f[0usize..5usize]).copy_from_slice(&[0u64; 5usize]) }

/**
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
pub fn
mk_felem_one(f: &mut [u64])
{
    (f[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    f[0usize] = 1u64
}

/**
Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
pub fn
felem_add(a: &[u64], b: &[u64], out: &mut [u64])
{
    crate::hacl::bignum_k256::fadd(out, a, b);
    crate::hacl::bignum_k256::fnormalize_weak(out, out)
}

/**
Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
pub fn
felem_sub(a: &[u64], b: &[u64], out: &mut [u64])
{
    crate::hacl::bignum_k256::fsub(out, a, b, 2u64);
    crate::hacl::bignum_k256::fnormalize_weak(out, out)
}

/**
Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
pub fn
felem_mul(a: &[u64], b: &[u64], out: &mut [u64])
{ crate::hacl::bignum_k256::fmul(out, a, b) }

/**
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
pub fn
felem_sqr(a: &[u64], out: &mut [u64])
{ crate::hacl::bignum_k256::fsqr(out, a) }

/**
Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
pub fn
felem_inv(a: &[u64], out: &mut [u64])
{ crate::hacl::bignum_k256::finv(out, a) }

/**
Load a bid-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint
*/
pub fn
felem_load(b: &[u8], out: &mut [u64])
{ crate::hacl::bignum_k256::load_felem(out, b) }

/**
Serialize a field element into big-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
pub fn
felem_store(a: &[u64], out: &mut [u8])
{
    let mut tmp: [u64; 5] = [0u64; 5usize];
    crate::hacl::bignum_k256::fnormalize(&mut tmp, a);
    crate::hacl::bignum_k256::store_felem(out, &tmp)
}

/**
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
pub fn
mk_point_at_inf(p: &mut [u64])
{ crate::hacl::k256_ecdsa::make_point_at_inf(p) }

/**
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
pub fn
mk_base_point(p: &mut [u64])
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

/**
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
pub fn
point_negate(p: &[u64], out: &mut [u64])
{ crate::hacl::k256_ecdsa::point_negate(out, p) }

/**
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
pub fn
point_add(p: &[u64], q: &[u64], out: &mut [u64])
{ crate::hacl::k256_ecdsa::point_add(out, p, q) }

/**
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
pub fn
point_double(p: &[u64], out: &mut [u64])
{ crate::hacl::k256_ecdsa::point_double(out, p) }

/**
Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a bid-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint
*/
pub fn
point_mul(scalar: &[u8], p: &[u64], out: &mut [u64])
{
    let mut scalar_q: [u64; 4] = [0u64; 4usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let u: u64 =
                crate::lowstar::endianness::load64_be(
                    &scalar[4u32.wrapping_sub(i).wrapping_sub(1u32).wrapping_mul(8u32) as usize..]
                );
            let x: u64 = u;
            let os: (&mut [u64], &mut [u64]) = (&mut scalar_q).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    crate::hacl::k256_ecdsa::point_mul(out, &scalar_q, p)
}

/**
Convert a point from projective coordinates to its raw form.

  The argument `p` points to a point of 15 limbs in size, i.e., uint64_t[15].
  The outparam `out` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first converts a given point `p` from projective to affine coordinates
  and then writes [ `x`; `y` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint.
*/
pub fn
point_store(p: &[u64], out: &mut [u8])
{ crate::hacl::k256_ecdsa::point_store(out, p) }

/**
Convert a point to projective coordinates from its raw form.

  The argument `b` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The outparam `out` points to a point of 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` is valid point, i.e., x < prime and y < prime and (x, y) is on the curve
  • `b` and `out` are disjoint.
*/
pub fn
point_load(b: &[u8], out: &mut [u64])
{
    let mut p_aff: [u64; 10] = [0u64; 10usize];
    let px: (&mut [u64], &mut [u64]) = (&mut p_aff).split_at_mut(0usize);
    let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(5usize);
    let pxb: (&[u8], &[u8]) = b.split_at(0usize);
    let pyb: (&[u8], &[u8]) = pxb.1.split_at(32usize);
    crate::hacl::bignum_k256::load_felem(py.0, pyb.0);
    crate::hacl::bignum_k256::load_felem(py.1, pyb.1);
    let x: (&[u64], &[u64]) = py.0.split_at(0usize);
    let y: (&[u64], &[u64]) = py.1.split_at(0usize);
    let x1: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
    let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
    let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
    (y1.0[0usize..5usize]).copy_from_slice(&x.1[0usize..5usize]);
    (z1.0[0usize..5usize]).copy_from_slice(&y.1[0usize..5usize]);
    (z1.1[0usize..5usize]).copy_from_slice(&[0u64; 5usize]);
    z1.1[0usize] = 1u64
}

/**
Check whether a point is valid.

  The function returns `true` if a point is valid and `false` otherwise.

  The argument `b` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The point (x || y) is valid:
    • x < prime and y < prime
    • (x, y) is on the curve.

  This function is NOT constant-time.
*/
pub fn
is_point_valid(b: &[u8]) ->
    bool
{
    let mut p: [u64; 10] = [0u64; 10usize];
    let res: bool = crate::hacl::k256_ecdsa::aff_point_load_vartime(&mut p, b);
    res
}
