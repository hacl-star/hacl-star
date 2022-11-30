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


#include "Hacl_Bignum256_32.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************

A verified 256-bit bignum library.

This is a 32-bit optimized version, where bignums are represented as an array
of eight unsigned 32-bit integers, i.e. uint32_t[8]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint32_t sixteen[8] = { 0x10; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00 }

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 64-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/**
Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint32_t[8]
*/
uint32_t Hacl_Bignum256_32_add(uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i););
  return c;
}

/**
Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint32_t[8]
*/
uint32_t Hacl_Bignum256_32_sub(uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i););
  return c;
}

/**
Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum256_32_add_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i););
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = res[(uint32_t)4U * i];
    uint32_t t20 = n[(uint32_t)4U * i];
    uint32_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i););
  uint32_t c1 = c;
  uint32_t c2 = c00 - c1;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;);
}

/**
Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum256_32_sub_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = a[(uint32_t)4U * i];
    uint32_t t20 = b[(uint32_t)4U * i];
    uint32_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i););
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = res[(uint32_t)4U * i];
    uint32_t t20 = n[(uint32_t)4U * i];
    uint32_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i););
  uint32_t c1 = c;
  uint32_t c2 = (uint32_t)0U - c00;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x;);
}

/**
Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16].
*/
void Hacl_Bignum256_32_mul(uint32_t *a, uint32_t *b, uint32_t *res)
{
  memset(res, 0U, (uint32_t)16U * sizeof (uint32_t));
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t bj = b[i0];
    uint32_t *res_j = res + i0;
    uint32_t c = (uint32_t)0U;
    KRML_MAYBE_FOR2(i,
      (uint32_t)0U,
      (uint32_t)2U,
      (uint32_t)1U,
      uint32_t a_i = a[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i););
    uint32_t r = c;
    res[(uint32_t)8U + i0] = r;);
}

/**
Write `a * a` in `res`.

  The argument a is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16].
*/
void Hacl_Bignum256_32_sqr(uint32_t *a, uint32_t *res)
{
  memset(res, 0U, (uint32_t)16U * sizeof (uint32_t));
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *ab = a;
    uint32_t a_j = a[i0];
    uint32_t *res_j = res + i0;
    uint32_t c = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[i0 + i0] = r;);
  uint32_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, res, res, res);
  uint32_t tmp[16U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t res1 = (uint64_t)a[i] * (uint64_t)a[i];
    uint32_t hi = (uint32_t)(res1 >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res1;
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;);
  uint32_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, res, tmp, res);
}

static inline void precompr2(uint32_t nBits, uint32_t *n, uint32_t *res)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t i = nBits / (uint32_t)32U;
  uint32_t j = nBits % (uint32_t)32U;
  res[i] = res[i] | (uint32_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)512U - nBits; i0++)
  {
    Hacl_Bignum256_32_add_mod(n, res, res, res);
  }
}

static inline void reduction(uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = (uint32_t)0U;
    KRML_MAYBE_FOR2(i,
      (uint32_t)0U,
      (uint32_t)2U,
      (uint32_t)1U,
      uint32_t a_i = n[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i););
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + i0;
    uint32_t res_j = c[(uint32_t)8U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb););
  memcpy(res, c + (uint32_t)8U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = (uint32_t)0U;
  KRML_MAYBE_FOR2(i,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint32_t t1 = res[(uint32_t)4U * i];
    uint32_t t20 = n[(uint32_t)4U * i];
    uint32_t *res_i0 = tmp + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t20, res_i0);
    uint32_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint32_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t10, t21, res_i1);
    uint32_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint32_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t11, t22, res_i2);
    uint32_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint32_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t12, t2, res_i););
  uint32_t c10 = c1;
  uint32_t c2 = c00 - c10;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;);
}

static inline void from(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *a)
{
  uint32_t tmp[16U] = { 0U };
  memcpy(tmp, aM, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, nInv_u64, tmp, a);
}

static inline void areduction(uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = (uint32_t)0U;
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = (uint32_t)0U;
    KRML_MAYBE_FOR2(i,
      (uint32_t)0U,
      (uint32_t)2U,
      (uint32_t)1U,
      uint32_t a_i = n[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i););
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + (uint32_t)8U + i0;
    uint32_t res_j = c[(uint32_t)8U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb););
  memcpy(res, c + (uint32_t)8U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = Hacl_Bignum256_32_sub(res, n, tmp);
  uint32_t m = (uint32_t)0U - c00;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = res;
    uint32_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;);
}

static inline void
amont_mul(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *bM, uint32_t *resM)
{
  uint32_t c[16U] = { 0U };
  memset(c, 0U, (uint32_t)16U * sizeof (uint32_t));
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t bj = bM[i0];
    uint32_t *res_j = c + i0;
    uint32_t c1 = (uint32_t)0U;
    KRML_MAYBE_FOR2(i,
      (uint32_t)0U,
      (uint32_t)2U,
      (uint32_t)1U,
      uint32_t a_i = aM[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c1, res_i0);
      uint32_t a_i0 = aM[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c1, res_i1);
      uint32_t a_i1 = aM[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c1, res_i2);
      uint32_t a_i2 = aM[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c1, res_i););
    uint32_t r = c1;
    c[(uint32_t)8U + i0] = r;);
  areduction(n, nInv_u64, c, resM);
}

static inline void amont_sqr(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *resM)
{
  uint32_t c[16U] = { 0U };
  memset(c, 0U, (uint32_t)16U * sizeof (uint32_t));
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *ab = aM;
    uint32_t a_j = aM[i0];
    uint32_t *res_j = c + i0;
    uint32_t c1 = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
    {
      uint32_t a_i = ab[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i0);
      uint32_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c1, res_i1);
      uint32_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c1, res_i2);
      uint32_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c1, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c1, res_i);
    }
    uint32_t r = c1;
    c[i0 + i0] = r;);
  uint32_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, c, c, c);
  uint32_t tmp[16U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t res = (uint64_t)aM[i] * (uint64_t)aM[i];
    uint32_t hi = (uint32_t)(res >> (uint32_t)32U);
    uint32_t lo = (uint32_t)res;
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;);
  uint32_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u32((uint32_t)16U, c, tmp, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void
bn_slow_precomp(uint32_t *n, uint32_t mu, uint32_t *r2, uint32_t *a, uint32_t *res)
{
  uint32_t a_mod[8U] = { 0U };
  uint32_t a1[16U] = { 0U };
  memcpy(a1, a, (uint32_t)16U * sizeof (uint32_t));
  uint32_t c0 = (uint32_t)0U;
  KRML_MAYBE_FOR8(i0,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t qj = mu * a1[i0];
    uint32_t *res_j0 = a1 + i0;
    uint32_t c = (uint32_t)0U;
    KRML_MAYBE_FOR2(i,
      (uint32_t)0U,
      (uint32_t)2U,
      (uint32_t)1U,
      uint32_t a_i = n[(uint32_t)4U * i];
      uint32_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c, res_i0);
      uint32_t a_i0 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c, res_i1);
      uint32_t a_i1 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c, res_i2);
      uint32_t a_i2 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c, res_i););
    uint32_t r = c;
    uint32_t c1 = r;
    uint32_t *resb = a1 + (uint32_t)8U + i0;
    uint32_t res_j = a1[(uint32_t)8U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c1, res_j, resb););
  memcpy(a_mod, a1 + (uint32_t)8U, (uint32_t)8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = Hacl_Bignum256_32_sub(a_mod, n, tmp);
  uint32_t m = (uint32_t)0U - c00;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = a_mod;
    uint32_t x = (m & tmp[i]) | (~m & a_mod[i]);
    os[i] = x;);
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_mul(a_mod, r2, c);
  reduction(n, mu, c, res);
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint32_t[16].
  The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1
*/
bool Hacl_Bignum256_32_mod(uint32_t *n, uint32_t *a, uint32_t *res)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, (uint32_t)8U * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc = (uint32_t)0U;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U))););
  uint32_t m1 = acc;
  uint32_t is_valid_m = m0 & m1;
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    uint32_t r2[8U] = { 0U };
    precompr2(nBits, n, r2);
    uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
    bn_slow_precomp(n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

static uint32_t exp_check(uint32_t *n, uint32_t *a, uint32_t bBits, uint32_t *b)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, (uint32_t)8U * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc0 = (uint32_t)0U;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U))););
  uint32_t m10 = acc0;
  uint32_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t m1;
  if (bBits < (uint32_t)32U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), bLen);
    uint32_t *b2 = (uint32_t *)alloca(bLen * sizeof (uint32_t));
    memset(b2, 0U, bLen * sizeof (uint32_t));
    uint32_t i0 = bBits / (uint32_t)32U;
    uint32_t j = bBits % (uint32_t)32U;
    b2[i0] = b2[i0] | (uint32_t)1U << j;
    uint32_t acc = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < bLen; i++)
    {
      uint32_t beq = FStar_UInt32_eq_mask(b[i], b2[i]);
      uint32_t blt = ~FStar_UInt32_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U)));
    }
    uint32_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = (uint32_t)0xFFFFFFFFU;
  }
  uint32_t acc = (uint32_t)0U;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U))););
  uint32_t m2 = acc;
  uint32_t m = m1 & m2;
  return m00 & m;
}

static inline void
exp_vartime_precomp(
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    uint32_t aM[8U] = { 0U };
    uint32_t c[16U] = { 0U };
    Hacl_Bignum256_32_mul(a, r2, c);
    reduction(n, mu, c, aM);
    uint32_t resM[8U] = { 0U };
    uint32_t ctx[16U] = { 0U };
    memcpy(ctx, n, (uint32_t)8U * sizeof (uint32_t));
    memcpy(ctx + (uint32_t)8U, r2, (uint32_t)8U * sizeof (uint32_t));
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + (uint32_t)8U;
    from(ctx_n, mu, ctx_r2, resM);
    for (uint32_t i = (uint32_t)0U; i < bBits; i++)
    {
      uint32_t i1 = i / (uint32_t)32U;
      uint32_t j = i % (uint32_t)32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & (uint32_t)1U;
      if (!(bit == (uint32_t)0U))
      {
        uint32_t *ctx_n0 = ctx;
        amont_mul(ctx_n0, mu, resM, aM, resM);
      }
      uint32_t *ctx_n0 = ctx;
      amont_sqr(ctx_n0, mu, aM, aM);
    }
    uint32_t tmp[16U] = { 0U };
    memcpy(tmp, resM, (uint32_t)8U * sizeof (uint32_t));
    reduction(n, mu, tmp, res);
    return;
  }
  uint32_t aM[8U] = { 0U };
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_mul(a, r2, c);
  reduction(n, mu, c, aM);
  uint32_t resM[8U] = { 0U };
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t ctx[16U] = { 0U };
  memcpy(ctx, n, (uint32_t)8U * sizeof (uint32_t));
  memcpy(ctx + (uint32_t)8U, r2, (uint32_t)8U * sizeof (uint32_t));
  uint32_t table[128U] = { 0U };
  uint32_t tmp[8U] = { 0U };
  uint32_t *t0 = table;
  uint32_t *t1 = table + (uint32_t)8U;
  uint32_t *ctx_n0 = ctx;
  uint32_t *ctx_r20 = ctx + (uint32_t)8U;
  from(ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, (uint32_t)8U * sizeof (uint32_t));
  KRML_MAYBE_FOR7(i,
    (uint32_t)0U,
    (uint32_t)7U,
    (uint32_t)1U,
    uint32_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)8U;
    uint32_t *ctx_n1 = ctx;
    amont_sqr(ctx_n1, mu, t11, tmp);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)8U,
      tmp,
      (uint32_t)8U * sizeof (uint32_t));
    uint32_t *t2 = table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)8U;
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, aM, t2, tmp);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)8U,
      tmp,
      (uint32_t)8U * sizeof (uint32_t)););
  if (bBits % (uint32_t)4U != (uint32_t)0U)
  {
    uint32_t mask_l = (uint32_t)15U;
    uint32_t i = bBits / (uint32_t)4U * (uint32_t)4U / (uint32_t)32U;
    uint32_t j = bBits / (uint32_t)4U * (uint32_t)4U % (uint32_t)32U;
    uint32_t p1 = b[i] >> j;
    uint32_t ite;
    if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_c = ite & mask_l;
    uint32_t bits_l32 = bits_c;
    const uint32_t *a_bits_l = table + bits_l32 * (uint32_t)8U;
    memcpy(resM, (uint32_t *)a_bits_l, (uint32_t)8U * sizeof (uint32_t));
  }
  else
  {
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + (uint32_t)8U;
    from(ctx_n, mu, ctx_r2, resM);
  }
  uint32_t tmp0[8U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < bBits / (uint32_t)4U; i++)
  {
    KRML_MAYBE_FOR4(i0,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      uint32_t *ctx_n = ctx;
      amont_sqr(ctx_n, mu, resM, resM););
    uint32_t bk = bBits - bBits % (uint32_t)4U;
    uint32_t mask_l = (uint32_t)15U;
    uint32_t i1 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)32U;
    uint32_t j = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)32U;
    uint32_t p1 = b[i1] >> j;
    uint32_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_l = ite & mask_l;
    uint32_t bits_l32 = bits_l;
    const uint32_t *a_bits_l = table + bits_l32 * (uint32_t)8U;
    memcpy(tmp0, (uint32_t *)a_bits_l, (uint32_t)8U * sizeof (uint32_t));
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, resM, tmp0, resM);
  }
  uint32_t tmp1[16U] = { 0U };
  memcpy(tmp1, resM, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, mu, tmp1, res);
}

static inline void
exp_consttime_precomp(
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < (uint32_t)200U)
  {
    uint32_t aM[8U] = { 0U };
    uint32_t c[16U] = { 0U };
    Hacl_Bignum256_32_mul(a, r2, c);
    reduction(n, mu, c, aM);
    uint32_t resM[8U] = { 0U };
    uint32_t ctx[16U] = { 0U };
    memcpy(ctx, n, (uint32_t)8U * sizeof (uint32_t));
    memcpy(ctx + (uint32_t)8U, r2, (uint32_t)8U * sizeof (uint32_t));
    uint32_t sw = (uint32_t)0U;
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + (uint32_t)8U;
    from(ctx_n, mu, ctx_r2, resM);
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)32U;
      uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & (uint32_t)1U;
      uint32_t sw1 = bit ^ sw;
      KRML_MAYBE_FOR8(i,
        (uint32_t)0U,
        (uint32_t)8U,
        (uint32_t)1U,
        uint32_t dummy = ((uint32_t)0U - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;);
      uint32_t *ctx_n0 = ctx;
      amont_mul(ctx_n0, mu, aM, resM, aM);
      uint32_t *ctx_n1 = ctx;
      amont_sqr(ctx_n1, mu, resM, resM);
      sw = bit;
    }
    uint32_t sw0 = sw;
    KRML_MAYBE_FOR8(i,
      (uint32_t)0U,
      (uint32_t)8U,
      (uint32_t)1U,
      uint32_t dummy = ((uint32_t)0U - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;);
    uint32_t tmp[16U] = { 0U };
    memcpy(tmp, resM, (uint32_t)8U * sizeof (uint32_t));
    reduction(n, mu, tmp, res);
    return;
  }
  uint32_t aM[8U] = { 0U };
  uint32_t c0[16U] = { 0U };
  Hacl_Bignum256_32_mul(a, r2, c0);
  reduction(n, mu, c0, aM);
  uint32_t resM[8U] = { 0U };
  uint32_t bLen;
  if (bBits == (uint32_t)0U)
  {
    bLen = (uint32_t)1U;
  }
  else
  {
    bLen = (bBits - (uint32_t)1U) / (uint32_t)32U + (uint32_t)1U;
  }
  uint32_t ctx[16U] = { 0U };
  memcpy(ctx, n, (uint32_t)8U * sizeof (uint32_t));
  memcpy(ctx + (uint32_t)8U, r2, (uint32_t)8U * sizeof (uint32_t));
  uint32_t table[128U] = { 0U };
  uint32_t tmp[8U] = { 0U };
  uint32_t *t0 = table;
  uint32_t *t1 = table + (uint32_t)8U;
  uint32_t *ctx_n0 = ctx;
  uint32_t *ctx_r20 = ctx + (uint32_t)8U;
  from(ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, (uint32_t)8U * sizeof (uint32_t));
  KRML_MAYBE_FOR7(i,
    (uint32_t)0U,
    (uint32_t)7U,
    (uint32_t)1U,
    uint32_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)8U;
    uint32_t *ctx_n1 = ctx;
    amont_sqr(ctx_n1, mu, t11, tmp);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)8U,
      tmp,
      (uint32_t)8U * sizeof (uint32_t));
    uint32_t *t2 = table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)8U;
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, aM, t2, tmp);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)8U,
      tmp,
      (uint32_t)8U * sizeof (uint32_t)););
  if (bBits % (uint32_t)4U != (uint32_t)0U)
  {
    uint32_t mask_l = (uint32_t)15U;
    uint32_t i0 = bBits / (uint32_t)4U * (uint32_t)4U / (uint32_t)32U;
    uint32_t j = bBits / (uint32_t)4U * (uint32_t)4U % (uint32_t)32U;
    uint32_t p1 = b[i0] >> j;
    uint32_t ite;
    if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_c = ite & mask_l;
    memcpy(resM, (uint32_t *)table, (uint32_t)8U * sizeof (uint32_t));
    KRML_MAYBE_FOR15(i1,
      (uint32_t)0U,
      (uint32_t)15U,
      (uint32_t)1U,
      uint32_t c = FStar_UInt32_eq_mask(bits_c, i1 + (uint32_t)1U);
      const uint32_t *res_j = table + (i1 + (uint32_t)1U) * (uint32_t)8U;
      KRML_MAYBE_FOR8(i,
        (uint32_t)0U,
        (uint32_t)8U,
        (uint32_t)1U,
        uint32_t *os = resM;
        uint32_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;););
  }
  else
  {
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + (uint32_t)8U;
    from(ctx_n, mu, ctx_r2, resM);
  }
  uint32_t tmp0[8U] = { 0U };
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits / (uint32_t)4U; i0++)
  {
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      uint32_t *ctx_n = ctx;
      amont_sqr(ctx_n, mu, resM, resM););
    uint32_t bk = bBits - bBits % (uint32_t)4U;
    uint32_t mask_l = (uint32_t)15U;
    uint32_t i1 = (bk - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)32U;
    uint32_t j = (bk - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)32U;
    uint32_t p1 = b[i1] >> j;
    uint32_t ite;
    if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)32U - j);
    }
    else
    {
      ite = p1;
    }
    uint32_t bits_l = ite & mask_l;
    memcpy(tmp0, (uint32_t *)table, (uint32_t)8U * sizeof (uint32_t));
    KRML_MAYBE_FOR15(i2,
      (uint32_t)0U,
      (uint32_t)15U,
      (uint32_t)1U,
      uint32_t c = FStar_UInt32_eq_mask(bits_l, i2 + (uint32_t)1U);
      const uint32_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)8U;
      KRML_MAYBE_FOR8(i,
        (uint32_t)0U,
        (uint32_t)8U,
        (uint32_t)1U,
        uint32_t *os = tmp0;
        uint32_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;););
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, resM, tmp0, resM);
  }
  uint32_t tmp1[16U] = { 0U };
  memcpy(tmp1, resM, (uint32_t)8U * sizeof (uint32_t));
  reduction(n, mu, tmp1, res);
}

static inline void
exp_vartime(
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t r2[8U] = { 0U };
  precompr2(nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  exp_vartime_precomp(n, mu, r2, a, bBits, b, res);
}

static inline void
exp_consttime(
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t r2[8U] = { 0U };
  precompr2(nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  exp_consttime_precomp(n, mu, r2, a, bBits, b, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
bool
Hacl_Bignum256_32_mod_exp_vartime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    exp_vartime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
bool
Hacl_Bignum256_32_mod_exp_consttime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    exp_consttime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}

/**
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n
*/
bool Hacl_Bignum256_32_mod_inv_prime_vartime(uint32_t *n, uint32_t *a, uint32_t *res)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, (uint32_t)8U * sizeof (uint32_t));
  one[0U] = (uint32_t)1U;
  uint32_t bit0 = n[0U] & (uint32_t)1U;
  uint32_t m0 = (uint32_t)0U - bit0;
  uint32_t acc0 = (uint32_t)0U;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U))););
  uint32_t m1 = acc0;
  uint32_t m00 = m0 & m1;
  uint32_t bn_zero[8U] = { 0U };
  uint32_t mask = (uint32_t)0xFFFFFFFFU;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;);
  uint32_t mask1 = mask;
  uint32_t res10 = mask1;
  uint32_t m10 = res10;
  uint32_t acc = (uint32_t)0U;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U))););
  uint32_t m2 = acc;
  uint32_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  if (is_valid_m == (uint32_t)0xFFFFFFFFU)
  {
    uint32_t n2[8U] = { 0U };
    uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32((uint32_t)0U, n[0U], (uint32_t)2U, n2);
    uint32_t *a1 = n + (uint32_t)1U;
    uint32_t *res1 = n2 + (uint32_t)1U;
    uint32_t c = c0;
    {
      uint32_t t1 = a1[(uint32_t)4U * (uint32_t)0U];
      uint32_t *res_i0 = res1 + (uint32_t)4U * (uint32_t)0U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i0);
      uint32_t t10 = a1[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint32_t *res_i1 = res1 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, (uint32_t)0U, res_i1);
      uint32_t t11 = a1[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint32_t *res_i2 = res1 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, (uint32_t)0U, res_i2);
      uint32_t t12 = a1[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint32_t *res_i = res1 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, (uint32_t)0U, res_i);
    }
    KRML_MAYBE_FOR3(i,
      (uint32_t)4U,
      (uint32_t)7U,
      (uint32_t)1U,
      uint32_t t1 = a1[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i););
    uint32_t c1 = c;
    uint32_t c2 = c1;
    exp_vartime(nBits, n, a, (uint32_t)256U, n2, res);
  }
  else
  {
    memset(res, 0U, (uint32_t)8U * sizeof (uint32_t));
  }
  return is_valid_m == (uint32_t)0xFFFFFFFFU;
}


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be a 256-bit bignum, i.e. uint32_t[8].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum256_mont_ctx_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *Hacl_Bignum256_32_mont_ctx_init(uint32_t *n)
{
  uint32_t *r2 = (uint32_t *)KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  uint32_t *n1 = (uint32_t *)KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  uint32_t *r21 = r2;
  uint32_t *n11 = n1;
  memcpy(n11, n, (uint32_t)8U * sizeof (uint32_t));
  uint32_t nBits = (uint32_t)32U * Hacl_Bignum_Lib_bn_get_top_index_u32((uint32_t)8U, n);
  precompr2(nBits, n, r21);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
  res = { .len = (uint32_t)8U, .n = n11, .mu = mu, .r2 = r21 };
  KRML_CHECK_SIZE(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32), (uint32_t)1U);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
  *buf =
    (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *)KRML_HOST_MALLOC(sizeof (
        Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
      ));
  buf[0U] = res;
  return buf;
}

/**
Deallocate the memory previously allocated by Hacl_Bignum256_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.
*/
void Hacl_Bignum256_32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  uint32_t *n = k1.n;
  uint32_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be a 512-bit bignum, i.e. uint32_t[16].
  The outparam res is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.
*/
void
Hacl_Bignum256_32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  bn_slow_precomp(k1.n, k1.mu, k1.r2, a, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum256_32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum256_32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  exp_consttime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/**
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 256-bit bignums, i.e. uint32_t[8].
  The argument k is a montgomery context obtained through Hacl_Bignum256_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n
*/
void
Hacl_Bignum256_32_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  uint32_t n2[8U] = { 0U };
  uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32((uint32_t)0U, k1.n[0U], (uint32_t)2U, n2);
  uint32_t *a1 = k1.n + (uint32_t)1U;
  uint32_t *res1 = n2 + (uint32_t)1U;
  uint32_t c = c0;
  {
    uint32_t t1 = a1[(uint32_t)4U * (uint32_t)0U];
    uint32_t *res_i0 = res1 + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i0);
    uint32_t t10 = a1[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint32_t *res_i1 = res1 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, (uint32_t)0U, res_i1);
    uint32_t t11 = a1[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint32_t *res_i2 = res1 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, (uint32_t)0U, res_i2);
    uint32_t t12 = a1[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint32_t *res_i = res1 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, (uint32_t)0U, res_i);
  }
  KRML_MAYBE_FOR3(i,
    (uint32_t)4U,
    (uint32_t)7U,
    (uint32_t)1U,
    uint32_t t1 = a1[i];
    uint32_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, (uint32_t)0U, res_i););
  uint32_t c1 = c;
  uint32_t c2 = c1;
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, (uint32_t)256U, n2, res);
}


/********************/
/* Loads and stores */
/********************/


/**
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum256_32_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U <= (uint32_t)1073741823U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U);
  uint32_t
  *res =
    (uint32_t *)KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U,
      sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint32_t *os = res2;
    uint32_t u = load32_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)4U);
    uint32_t x = u;
    os[i] = x;
  }
  return res2;
}

/**
Load a little-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum256_32_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U <= (uint32_t)1073741823U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U);
  uint32_t
  *res =
    (uint32_t *)KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U,
      sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (len - (uint32_t)1U) / (uint32_t)4U + (uint32_t)1U; i++)
  {
    uint32_t *os = res2;
    uint8_t *bj = tmp + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r1 = u;
    uint32_t x = r1;
    os[i] = x;
  }
  return res2;
}

/**
Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_32_bn_to_bytes_be(uint32_t *b, uint8_t *res)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    store32_be(res + i * (uint32_t)4U, b[(uint32_t)8U - i - (uint32_t)1U]););
}

/**
Serialize a bignum into little-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_32_bn_to_bytes_le(uint32_t *b, uint8_t *res)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    store32_le(res + i * (uint32_t)4U, b[i]););
}


/***************/
/* Comparisons */
/***************/


/**
Returns 2^32 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
*/
uint32_t Hacl_Bignum256_32_lt_mask(uint32_t *a, uint32_t *b)
{
  uint32_t acc = (uint32_t)0U;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t beq = FStar_UInt32_eq_mask(a[i], b[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint32_t)0xFFFFFFFFU) | (~blt & (uint32_t)0U))););
  return acc;
}

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
*/
uint32_t Hacl_Bignum256_32_eq_mask(uint32_t *a, uint32_t *b)
{
  uint32_t mask = (uint32_t)0xFFFFFFFFU;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], b[i]);
    mask = uu____0 & mask;);
  uint32_t mask1 = mask;
  return mask1;
}

