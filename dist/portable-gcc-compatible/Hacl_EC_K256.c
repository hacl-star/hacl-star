/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#include "Hacl_EC_K256.h"

#include "internal/Hacl_K256_ECDSA.h"
#include "internal/Hacl_Bignum_K256.h"

/* SNIPPET_START: Hacl_EC_K256_mk_felem_zero */

/*******************************************************************************
  Verified field arithmetic modulo p = 2^256 - 0x1000003D1.

  This is a 64-bit optimized version, where a field element in radix-2^{52} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/


/**
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_K256_mk_felem_zero(uint64_t *f)
{
  memset(f, 0U, (uint32_t)5U * sizeof (uint64_t));
}

/* SNIPPET_END: Hacl_EC_K256_mk_felem_zero */

/* SNIPPET_START: Hacl_EC_K256_mk_felem_one */

/**
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_K256_mk_felem_one(uint64_t *f)
{
  memset(f, 0U, (uint32_t)5U * sizeof (uint64_t));
  f[0U] = (uint64_t)1U;
}

/* SNIPPET_END: Hacl_EC_K256_mk_felem_one */

/* SNIPPET_START: Hacl_EC_K256_felem_add */

/**
Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_add(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_K256_Field_fadd(out, a, b);
  Hacl_K256_Field_fnormalize_weak(out, out);
}

/* SNIPPET_END: Hacl_EC_K256_felem_add */

/* SNIPPET_START: Hacl_EC_K256_felem_sub */

/**
Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_K256_Field_fsub(out, a, b, (uint64_t)2U);
  Hacl_K256_Field_fnormalize_weak(out, out);
}

/* SNIPPET_END: Hacl_EC_K256_felem_sub */

/* SNIPPET_START: Hacl_EC_K256_felem_mul */

/**
Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_K256_Field_fmul(out, a, b);
}

/* SNIPPET_END: Hacl_EC_K256_felem_mul */

/* SNIPPET_START: Hacl_EC_K256_felem_sqr */

/**
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_felem_sqr(uint64_t *a, uint64_t *out)
{
  Hacl_K256_Field_fsqr(out, a);
}

/* SNIPPET_END: Hacl_EC_K256_felem_sqr */

/* SNIPPET_START: Hacl_EC_K256_felem_inv */

/**
Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_K256_felem_inv(uint64_t *a, uint64_t *out)
{
  Hacl_Impl_K256_Finv_finv(out, a);
}

/* SNIPPET_END: Hacl_EC_K256_felem_inv */

/* SNIPPET_START: Hacl_EC_K256_felem_load */

/**
Load a bid-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint
*/
void Hacl_EC_K256_felem_load(uint8_t *b, uint64_t *out)
{
  Hacl_K256_Field_load_felem(out, b);
}

/* SNIPPET_END: Hacl_EC_K256_felem_load */

/* SNIPPET_START: Hacl_EC_K256_felem_store */

/**
Serialize a field element into big-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_K256_felem_store(uint64_t *a, uint8_t *out)
{
  uint64_t tmp[5U] = { 0U };
  Hacl_K256_Field_fnormalize(tmp, a);
  Hacl_K256_Field_store_felem(out, tmp);
}

/* SNIPPET_END: Hacl_EC_K256_felem_store */

/* SNIPPET_START: Hacl_EC_K256_mk_point_at_inf */

/*******************************************************************************
  Verified group operations for the secp256k1 curve of the form y^2 = x^3 + 7.

  This is a 64-bit optimized version, where a group element in projective coordinates
  is represented as an array of 15 unsigned 64-bit integers, i.e., uint64_t[15].
*******************************************************************************/


/**
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
void Hacl_EC_K256_mk_point_at_inf(uint64_t *p)
{
  Hacl_Impl_K256_Point_make_point_at_inf(p);
}

/* SNIPPET_END: Hacl_EC_K256_mk_point_at_inf */

/* SNIPPET_START: Hacl_EC_K256_mk_base_point */

/**
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
void Hacl_EC_K256_mk_base_point(uint64_t *p)
{
  uint64_t *gx = p;
  uint64_t *gy = p + (uint32_t)5U;
  uint64_t *gz = p + (uint32_t)10U;
  gx[0U] = (uint64_t)0x2815b16f81798U;
  gx[1U] = (uint64_t)0xdb2dce28d959fU;
  gx[2U] = (uint64_t)0xe870b07029bfcU;
  gx[3U] = (uint64_t)0xbbac55a06295cU;
  gx[4U] = (uint64_t)0x79be667ef9dcU;
  gy[0U] = (uint64_t)0x7d08ffb10d4b8U;
  gy[1U] = (uint64_t)0x48a68554199c4U;
  gy[2U] = (uint64_t)0xe1108a8fd17b4U;
  gy[3U] = (uint64_t)0xc4655da4fbfc0U;
  gy[4U] = (uint64_t)0x483ada7726a3U;
  memset(gz, 0U, (uint32_t)5U * sizeof (uint64_t));
  gz[0U] = (uint64_t)1U;
}

/* SNIPPET_END: Hacl_EC_K256_mk_base_point */

/* SNIPPET_START: Hacl_EC_K256_point_negate */

/**
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_point_negate(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_K256_Point_point_negate(out, p);
}

/* SNIPPET_END: Hacl_EC_K256_point_negate */

/* SNIPPET_START: Hacl_EC_K256_point_add */

/**
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_point_add(uint64_t *p, uint64_t *q, uint64_t *out)
{
  Hacl_Impl_K256_PointAdd_point_add(out, p, q);
}

/* SNIPPET_END: Hacl_EC_K256_point_add */

/* SNIPPET_START: Hacl_EC_K256_point_double */

/**
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_point_double(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_K256_PointDouble_point_double(out, p);
}

/* SNIPPET_END: Hacl_EC_K256_point_double */

/* SNIPPET_START: Hacl_EC_K256_point_mul */

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
void Hacl_EC_K256_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out)
{
  uint64_t scalar_q[4U] = { 0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = scalar_q;
    uint64_t u = load64_be(scalar + ((uint32_t)4U - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;);
  Hacl_Impl_K256_PointMul_point_mul(out, scalar_q, p);
}

/* SNIPPET_END: Hacl_EC_K256_point_mul */

/* SNIPPET_START: Hacl_EC_K256_point_store */

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
void Hacl_EC_K256_point_store(uint64_t *p, uint8_t *out)
{
  Hacl_Impl_K256_Point_point_store(out, p);
}

/* SNIPPET_END: Hacl_EC_K256_point_store */

/* SNIPPET_START: Hacl_EC_K256_point_load */

/**
Convert a point to projective coordinates from its raw form.

  The argument `b` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The outparam `out` points to a point of 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` is valid point, i.e., x < prime and y < prime and (x, y) is on the curve
  • `b` and `out` are disjoint.
*/
void Hacl_EC_K256_point_load(uint8_t *b, uint64_t *out)
{
  uint64_t p_aff[10U] = { 0U };
  uint64_t *px = p_aff;
  uint64_t *py = p_aff + (uint32_t)5U;
  uint8_t *pxb = b;
  uint8_t *pyb = b + (uint32_t)32U;
  Hacl_K256_Field_load_felem(px, pxb);
  Hacl_K256_Field_load_felem(py, pyb);
  uint64_t *x = p_aff;
  uint64_t *y = p_aff + (uint32_t)5U;
  uint64_t *x1 = out;
  uint64_t *y1 = out + (uint32_t)5U;
  uint64_t *z1 = out + (uint32_t)10U;
  memcpy(x1, x, (uint32_t)5U * sizeof (uint64_t));
  memcpy(y1, y, (uint32_t)5U * sizeof (uint64_t));
  memset(z1, 0U, (uint32_t)5U * sizeof (uint64_t));
  z1[0U] = (uint64_t)1U;
}

/* SNIPPET_END: Hacl_EC_K256_point_load */

/* SNIPPET_START: Hacl_EC_K256_is_point_valid */

/**
Check whether a point is valid.

  The function returns `true` if a point is valid and `false` otherwise.

  The argument `b` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The point (x || y) is valid:
    • x < prime and y < prime
    • (x, y) is on the curve.

  This function is NOT constant-time.
*/
bool Hacl_EC_K256_is_point_valid(uint8_t *b)
{
  uint64_t p[10U] = { 0U };
  bool res = Hacl_Impl_K256_Point_aff_point_load_vartime(p, b);
  return res;
}

/* SNIPPET_END: Hacl_EC_K256_is_point_valid */

