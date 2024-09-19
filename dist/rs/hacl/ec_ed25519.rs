#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

/**
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
pub fn
mk_felem_zero(b: &mut [u64])
{
    b[0usize] = 0u64;
    b[1usize] = 0u64;
    b[2usize] = 0u64;
    b[3usize] = 0u64;
    b[4usize] = 0u64
}

/**
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
pub fn
mk_felem_one(b: &mut [u64])
{
    b[0usize] = 1u64;
    b[1usize] = 0u64;
    b[2usize] = 0u64;
    b[3usize] = 0u64;
    b[4usize] = 0u64
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
    bignum::bignum25519_51::fadd(out, a, b);
    crate::ed25519::reduce_513(out)
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
    bignum::bignum25519_51::fsub(out, a, b);
    crate::ed25519::reduce_513(out)
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
{
    let tmp: [fstar::uint128::uint128; 10] =
        [fstar::uint128::uint64_to_uint128(0u64); 10usize];
    bignum::bignum25519_51::fmul(out, a, b, &tmp)
}

/**
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
pub fn
felem_sqr(a: &[u64], out: &mut [u64])
{
    let tmp: [fstar::uint128::uint128; 5] =
        [fstar::uint128::uint64_to_uint128(0u64); 5usize];
    bignum::bignum25519_51::fsqr(out, a, &tmp)
}

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
{
    crate::ed25519::inverse(out, a);
    crate::ed25519::reduce_513(out)
}

/**
Load a little-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint

  NOTE that the function also performs the reduction modulo 2^255.
*/
pub fn
felem_load(b: &[u8], out: &mut [u64])
{ crate::ed25519::load_51(out, b) }

/**
Serialize a field element into little-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
pub fn
felem_store(a: &[u64], out: &mut [u8])
{ crate::ed25519::store_51(out, a) }

/**
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20].
*/
pub fn
mk_point_at_inf(p: &mut [u64])
{ crate::ed25519::make_point_inf(p) }

/**
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20].
*/
pub fn
mk_base_point(p: &mut [u64])
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

/**
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint
*/
pub fn
point_negate(p: &[u64], out: &mut [u64])
{ crate::ed25519::point_negate(p, out) }

/**
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
pub fn
point_add(p: &[u64], q: &[u64], out: &mut [u64])
{ crate::ed25519::point_add(out, p, q) }

/**
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either pairwise disjoint or equal
*/
pub fn
point_double(p: &[u64], out: &mut [u64])
{ crate::ed25519::point_double(out, p) }

/**
Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a little-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint
*/
pub fn
point_mul(scalar: &[u8], p: &[u64], out: &mut [u64])
{ crate::ed25519::point_mul(out, scalar, p) }

/**
Checks whether `p` is equal to `q` (point equality).

  The function returns `true` if `p` is equal to `q` and `false` otherwise.

  The arguments `p` and `q` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `q` are either disjoint or equal
*/
pub fn
point_eq(p: &[u64], q: &[u64]) ->
    bool
{ crate::ed25519::point_equal(p, q) }

/**
Compress a point in extended homogeneous coordinates to its compressed form.

  The argument `p` points to a point of 20 limbs in size, i.e., uint64_t[20].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first converts a given point `p` from extended homogeneous to affine coordinates
  and then writes [ 2^255 * (`x` % 2) + `y` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint
*/
pub fn
point_compress(p: &[u64], out: &mut [u8])
{ crate::ed25519::point_compress(out, p) }

/**
Decompress a point in extended homogeneous coordinates from its compressed form.

  The function returns `true` for successful decompression of a compressed point
  and `false` otherwise.

  The argument `s` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a point of 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `s` and `out` are disjoint
*/
pub fn
point_decompress(s: &[u8], out: &mut [u64]) ->
    bool
{ crate::ed25519::point_decompress(out, s) }
