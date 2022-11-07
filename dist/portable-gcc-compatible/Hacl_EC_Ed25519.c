/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_EC_Ed25519.h"

#include "internal/Hacl_Ed25519.h"

/* SNIPPET_START: Hacl_EC_Ed25519_mk_felem_zero */

/*******************************************************************************
  Verified field arithmetic modulo p = 2^255 - 19.

  This is a 64-bit optimized version, where a field element in radix-2^{51} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/


/**
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_Ed25519_mk_felem_zero(uint64_t *b)
{
  b[0U] = (uint64_t)0U;
  b[1U] = (uint64_t)0U;
  b[2U] = (uint64_t)0U;
  b[3U] = (uint64_t)0U;
  b[4U] = (uint64_t)0U;
}

/* SNIPPET_END: Hacl_EC_Ed25519_mk_felem_zero */

/* SNIPPET_START: Hacl_EC_Ed25519_mk_felem_one */

/**
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_Ed25519_mk_felem_one(uint64_t *b)
{
  b[0U] = (uint64_t)1U;
  b[1U] = (uint64_t)0U;
  b[2U] = (uint64_t)0U;
  b[3U] = (uint64_t)0U;
  b[4U] = (uint64_t)0U;
}

/* SNIPPET_END: Hacl_EC_Ed25519_mk_felem_one */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_add */

/**
Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_felem_add(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_Impl_Curve25519_Field51_fadd(out, a, b);
  Hacl_Bignum25519_reduce_513(out);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_add */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_sub */

/**
Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_Impl_Curve25519_Field51_fsub(out, a, b);
  Hacl_Bignum25519_reduce_513(out);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_sub */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_mul */

/**
Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out)
{
  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fmul(out, a, b, tmp);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_mul */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_sqr */

/**
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
void Hacl_EC_Ed25519_felem_sqr(uint64_t *a, uint64_t *out)
{
  FStar_UInt128_uint128 tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_sqr */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_inv */

/**
Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_Ed25519_felem_inv(uint64_t *a, uint64_t *out)
{
  Hacl_Bignum25519_inverse(out, a);
  Hacl_Bignum25519_reduce_513(out);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_inv */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_load */

/**
Load a little-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint

  NOTE that the function also performs the reduction modulo 2^255.
*/
void Hacl_EC_Ed25519_felem_load(uint8_t *b, uint64_t *out)
{
  Hacl_Bignum25519_load_51(out, b);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_load */

/* SNIPPET_START: Hacl_EC_Ed25519_felem_store */

/**
Serialize a field element into little-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_Ed25519_felem_store(uint64_t *a, uint8_t *out)
{
  Hacl_Bignum25519_store_51(out, a);
}

/* SNIPPET_END: Hacl_EC_Ed25519_felem_store */

/* SNIPPET_START: Hacl_EC_Ed25519_mk_point_at_inf */

/*******************************************************************************
  Verified group operations for the edwards25519 elliptic curve of the form
  −x^2 + y^2 = 1 − (121665/121666) * x^2 * y^2.

  This is a 64-bit optimized version, where a group element in extended homogeneous
  coordinates (X, Y, Z, T) is represented as an array of 20 unsigned 64-bit
  integers, i.e., uint64_t[20].
*******************************************************************************/


/**
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20].
*/
void Hacl_EC_Ed25519_mk_point_at_inf(uint64_t *p)
{
  Hacl_Impl_Ed25519_PointConstants_make_point_inf(p);
}

/* SNIPPET_END: Hacl_EC_Ed25519_mk_point_at_inf */

/* SNIPPET_START: Hacl_EC_Ed25519_mk_base_point */

/**
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20].
*/
void Hacl_EC_Ed25519_mk_base_point(uint64_t *p)
{
  uint64_t *gx = p;
  uint64_t *gy = p + (uint32_t)5U;
  uint64_t *gz = p + (uint32_t)10U;
  uint64_t *gt = p + (uint32_t)15U;
  gx[0U] = (uint64_t)0x00062d608f25d51aU;
  gx[1U] = (uint64_t)0x000412a4b4f6592aU;
  gx[2U] = (uint64_t)0x00075b7171a4b31dU;
  gx[3U] = (uint64_t)0x0001ff60527118feU;
  gx[4U] = (uint64_t)0x000216936d3cd6e5U;
  gy[0U] = (uint64_t)0x0006666666666658U;
  gy[1U] = (uint64_t)0x0004ccccccccccccU;
  gy[2U] = (uint64_t)0x0001999999999999U;
  gy[3U] = (uint64_t)0x0003333333333333U;
  gy[4U] = (uint64_t)0x0006666666666666U;
  gz[0U] = (uint64_t)1U;
  gz[1U] = (uint64_t)0U;
  gz[2U] = (uint64_t)0U;
  gz[3U] = (uint64_t)0U;
  gz[4U] = (uint64_t)0U;
  gt[0U] = (uint64_t)0x00068ab3a5b7dda3U;
  gt[1U] = (uint64_t)0x00000eea2a5eadbbU;
  gt[2U] = (uint64_t)0x0002af8df483c27eU;
  gt[3U] = (uint64_t)0x000332b375274732U;
  gt[4U] = (uint64_t)0x00067875f0fd78b7U;
}

/* SNIPPET_END: Hacl_EC_Ed25519_mk_base_point */

/* SNIPPET_START: Hacl_EC_Ed25519_point_negate */

/**
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint
*/
void Hacl_EC_Ed25519_point_negate(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_Ed25519_PointNegate_point_negate(p, out);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_negate */

/* SNIPPET_START: Hacl_EC_Ed25519_point_add */

/**
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_point_add(uint64_t *p, uint64_t *q, uint64_t *out)
{
  Hacl_Impl_Ed25519_PointAdd_point_add(out, p, q);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_add */

/* SNIPPET_START: Hacl_EC_Ed25519_point_double */

/**
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_point_double(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_Ed25519_PointDouble_point_double(out, p);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_double */

/* SNIPPET_START: Hacl_EC_Ed25519_point_mul */

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
void Hacl_EC_Ed25519_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out)
{
  Hacl_Impl_Ed25519_Ladder_point_mul(out, scalar, p);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_mul */

/* SNIPPET_START: Hacl_EC_Ed25519_point_eq */

/**
Checks whether `p` is equal to `q` (point equality).

  The function returns `true` if `p` is equal to `q` and `false` otherwise.

  The arguments `p` and `q` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `q` are either disjoint or equal
*/
bool Hacl_EC_Ed25519_point_eq(uint64_t *p, uint64_t *q)
{
  return Hacl_Impl_Ed25519_PointEqual_point_equal(p, q);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_eq */

/* SNIPPET_START: Hacl_EC_Ed25519_point_compress */

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
void Hacl_EC_Ed25519_point_compress(uint64_t *p, uint8_t *out)
{
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, p);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_compress */

/* SNIPPET_START: Hacl_EC_Ed25519_point_decompress */

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
bool Hacl_EC_Ed25519_point_decompress(uint8_t *s, uint64_t *out)
{
  return Hacl_Impl_Ed25519_PointDecompress_point_decompress(out, s);
}

/* SNIPPET_END: Hacl_EC_Ed25519_point_decompress */

