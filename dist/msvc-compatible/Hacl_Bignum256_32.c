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


#include "Hacl_Bignum256_32.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
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
  uint32_t c = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = a[4U * i];
    uint32_t t20 = b[4U * i];
    uint32_t *res_i0 = res + 4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[4U * i + 1U];
    uint32_t t21 = b[4U * i + 1U];
    uint32_t *res_i1 = res + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[4U * i + 2U];
    uint32_t t22 = b[4U * i + 2U];
    uint32_t *res_i2 = res + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[4U * i + 3U];
    uint32_t t2 = b[4U * i + 3U];
    uint32_t *res_i = res + 4U * i + 3U;
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
  uint32_t c = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = a[4U * i];
    uint32_t t20 = b[4U * i];
    uint32_t *res_i0 = res + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = a[4U * i + 1U];
    uint32_t t21 = b[4U * i + 1U];
    uint32_t *res_i1 = res + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = a[4U * i + 2U];
    uint32_t t22 = b[4U * i + 2U];
    uint32_t *res_i2 = res + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = a[4U * i + 3U];
    uint32_t t2 = b[4U * i + 3U];
    uint32_t *res_i = res + 4U * i + 3U;
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
  uint32_t c0 = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = a[4U * i];
    uint32_t t20 = b[4U * i];
    uint32_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[4U * i + 1U];
    uint32_t t21 = b[4U * i + 1U];
    uint32_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[4U * i + 2U];
    uint32_t t22 = b[4U * i + 2U];
    uint32_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[4U * i + 3U];
    uint32_t t2 = b[4U * i + 3U];
    uint32_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i););
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = res[4U * i];
    uint32_t t20 = n[4U * i];
    uint32_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[4U * i + 1U];
    uint32_t t21 = n[4U * i + 1U];
    uint32_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[4U * i + 2U];
    uint32_t t22 = n[4U * i + 2U];
    uint32_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[4U * i + 3U];
    uint32_t t2 = n[4U * i + 3U];
    uint32_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i););
  uint32_t c1 = c;
  uint32_t c2 = c00 - c1;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
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
  uint32_t c0 = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = a[4U * i];
    uint32_t t20 = b[4U * i];
    uint32_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[4U * i + 1U];
    uint32_t t21 = b[4U * i + 1U];
    uint32_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[4U * i + 2U];
    uint32_t t22 = b[4U * i + 2U];
    uint32_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[4U * i + 3U];
    uint32_t t2 = b[4U * i + 3U];
    uint32_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i););
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = res[4U * i];
    uint32_t t20 = n[4U * i];
    uint32_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[4U * i + 1U];
    uint32_t t21 = n[4U * i + 1U];
    uint32_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[4U * i + 2U];
    uint32_t t22 = n[4U * i + 2U];
    uint32_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[4U * i + 3U];
    uint32_t t2 = n[4U * i + 3U];
    uint32_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i););
  uint32_t c1 = c;
  KRML_MAYBE_UNUSED_VAR(c1);
  uint32_t c2 = 0U - c00;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
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
  memset(res, 0U, 16U * sizeof (uint32_t));
  KRML_MAYBE_FOR8(i0,
    0U,
    8U,
    1U,
    uint32_t bj = b[i0];
    uint32_t *res_j = res + i0;
    uint32_t c = 0U;
    KRML_MAYBE_FOR2(i,
      0U,
      2U,
      1U,
      uint32_t a_i = a[4U * i];
      uint32_t *res_i0 = res_j + 4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
      uint32_t a_i0 = a[4U * i + 1U];
      uint32_t *res_i1 = res_j + 4U * i + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
      uint32_t a_i1 = a[4U * i + 2U];
      uint32_t *res_i2 = res_j + 4U * i + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
      uint32_t a_i2 = a[4U * i + 3U];
      uint32_t *res_i = res_j + 4U * i + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i););
    uint32_t r = c;
    res[8U + i0] = r;);
}

/**
Write `a * a` in `res`.

  The argument a is meant to be a 256-bit bignum, i.e. uint32_t[8].
  The outparam res is meant to be a 512-bit bignum, i.e. uint32_t[16].
*/
void Hacl_Bignum256_32_sqr(uint32_t *a, uint32_t *res)
{
  memset(res, 0U, 16U * sizeof (uint32_t));
  KRML_MAYBE_FOR8(i0,
    0U,
    8U,
    1U,
    uint32_t *ab = a;
    uint32_t a_j = a[i0];
    uint32_t *res_j = res + i0;
    uint32_t c = 0U;
    for (uint32_t i = 0U; i < i0 / 4U; i++)
    {
      uint32_t a_i = ab[4U * i];
      uint32_t *res_i0 = res_j + 4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
      uint32_t a_i0 = ab[4U * i + 1U];
      uint32_t *res_i1 = res_j + 4U * i + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
      uint32_t a_i1 = ab[4U * i + 2U];
      uint32_t *res_i2 = res_j + 4U * i + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
      uint32_t a_i2 = ab[4U * i + 3U];
      uint32_t *res_i = res_j + 4U * i + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / 4U * 4U; i < i0; i++)
    {
      uint32_t a_i = ab[i];
      uint32_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i);
    }
    uint32_t r = c;
    res[i0 + i0] = r;);
  uint32_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u32(16U, res, res, res);
  KRML_MAYBE_UNUSED_VAR(c0);
  uint32_t tmp[16U] = { 0U };
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint64_t res1 = (uint64_t)a[i] * (uint64_t)a[i];
    uint32_t hi = (uint32_t)(res1 >> 32U);
    uint32_t lo = (uint32_t)res1;
    tmp[2U * i] = lo;
    tmp[2U * i + 1U] = hi;);
  uint32_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u32(16U, res, tmp, res);
  KRML_MAYBE_UNUSED_VAR(c1);
}

static inline void precompr2(uint32_t nBits, uint32_t *n, uint32_t *res)
{
  memset(res, 0U, 8U * sizeof (uint32_t));
  uint32_t i = nBits / 32U;
  uint32_t j = nBits % 32U;
  res[i] = res[i] | 1U << j;
  for (uint32_t i0 = 0U; i0 < 512U - nBits; i0++)
  {
    Hacl_Bignum256_32_add_mod(n, res, res, res);
  }
}

static inline void reduction(uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = 0U;
  KRML_MAYBE_FOR8(i0,
    0U,
    8U,
    1U,
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = 0U;
    KRML_MAYBE_FOR2(i,
      0U,
      2U,
      1U,
      uint32_t a_i = n[4U * i];
      uint32_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[4U * i + 1U];
      uint32_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[4U * i + 2U];
      uint32_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[4U * i + 3U];
      uint32_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i););
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + 8U + i0;
    uint32_t res_j = c[8U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb););
  memcpy(res, c + 8U, 8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = 0U;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t t1 = res[4U * i];
    uint32_t t20 = n[4U * i];
    uint32_t *res_i0 = tmp + 4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t20, res_i0);
    uint32_t t10 = res[4U * i + 1U];
    uint32_t t21 = n[4U * i + 1U];
    uint32_t *res_i1 = tmp + 4U * i + 1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t10, t21, res_i1);
    uint32_t t11 = res[4U * i + 2U];
    uint32_t t22 = n[4U * i + 2U];
    uint32_t *res_i2 = tmp + 4U * i + 2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t11, t22, res_i2);
    uint32_t t12 = res[4U * i + 3U];
    uint32_t t2 = n[4U * i + 3U];
    uint32_t *res_i = tmp + 4U * i + 3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t12, t2, res_i););
  uint32_t c10 = c1;
  uint32_t c2 = c00 - c10;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;);
}

static inline void to(uint32_t *n, uint32_t nInv, uint32_t *r2, uint32_t *a, uint32_t *aM)
{
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_mul(a, r2, c);
  reduction(n, nInv, c, aM);
}

static inline void from(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *a)
{
  uint32_t tmp[16U] = { 0U };
  memcpy(tmp, aM, 8U * sizeof (uint32_t));
  reduction(n, nInv_u64, tmp, a);
}

static inline void areduction(uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = 0U;
  KRML_MAYBE_FOR8(i0,
    0U,
    8U,
    1U,
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = 0U;
    KRML_MAYBE_FOR2(i,
      0U,
      2U,
      1U,
      uint32_t a_i = n[4U * i];
      uint32_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[4U * i + 1U];
      uint32_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[4U * i + 2U];
      uint32_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[4U * i + 3U];
      uint32_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i););
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + 8U + i0;
    uint32_t res_j = c[8U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb););
  memcpy(res, c + 8U, 8U * sizeof (uint32_t));
  uint32_t c00 = c0;
  uint32_t tmp[8U] = { 0U };
  uint32_t c1 = Hacl_Bignum256_32_sub(res, n, tmp);
  KRML_MAYBE_UNUSED_VAR(c1);
  uint32_t m = 0U - c00;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t *os = res;
    uint32_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;);
}

static inline void
amont_mul(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *bM, uint32_t *resM)
{
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_mul(aM, bM, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void amont_sqr(uint32_t *n, uint32_t nInv_u64, uint32_t *aM, uint32_t *resM)
{
  uint32_t c[16U] = { 0U };
  Hacl_Bignum256_32_sqr(aM, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void
bn_slow_precomp(uint32_t *n, uint32_t mu, uint32_t *r2, uint32_t *a, uint32_t *res)
{
  uint32_t a_mod[8U] = { 0U };
  uint32_t a1[16U] = { 0U };
  memcpy(a1, a, 16U * sizeof (uint32_t));
  areduction(n, mu, a1, a_mod);
  to(n, mu, r2, a_mod, res);
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
  memset(one, 0U, 8U * sizeof (uint32_t));
  one[0U] = 1U;
  uint32_t bit0 = n[0U] & 1U;
  uint32_t m0 = 0U - bit0;
  uint32_t acc = 0U;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U))););
  uint32_t m1 = acc;
  uint32_t is_valid_m = m0 & m1;
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(8U, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    uint32_t r2[8U] = { 0U };
    precompr2(nBits, n, r2);
    uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
    bn_slow_precomp(n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, 8U * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
}

static uint32_t exp_check(uint32_t *n, uint32_t *a, uint32_t bBits, uint32_t *b)
{
  uint32_t one[8U] = { 0U };
  memset(one, 0U, 8U * sizeof (uint32_t));
  one[0U] = 1U;
  uint32_t bit0 = n[0U] & 1U;
  uint32_t m0 = 0U - bit0;
  uint32_t acc0 = 0U;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U))););
  uint32_t m10 = acc0;
  uint32_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 32U + 1U;
  }
  uint32_t m1;
  if (bBits < 32U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), bLen);
    uint32_t *b2 = (uint32_t *)alloca(bLen * sizeof (uint32_t));
    memset(b2, 0U, bLen * sizeof (uint32_t));
    uint32_t i0 = bBits / 32U;
    uint32_t j = bBits % 32U;
    b2[i0] = b2[i0] | 1U << j;
    uint32_t acc = 0U;
    for (uint32_t i = 0U; i < bLen; i++)
    {
      uint32_t beq = FStar_UInt32_eq_mask(b[i], b2[i]);
      uint32_t blt = ~FStar_UInt32_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U)));
    }
    uint32_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = 0xFFFFFFFFU;
  }
  uint32_t acc = 0U;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U))););
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
  if (bBits < 200U)
  {
    uint32_t aM[8U] = { 0U };
    to(n, mu, r2, a, aM);
    uint32_t resM[8U] = { 0U };
    uint32_t ctx[16U] = { 0U };
    memcpy(ctx, n, 8U * sizeof (uint32_t));
    memcpy(ctx + 8U, r2, 8U * sizeof (uint32_t));
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + 8U;
    from(ctx_n, mu, ctx_r2, resM);
    for (uint32_t i = 0U; i < bBits; i++)
    {
      uint32_t i1 = i / 32U;
      uint32_t j = i % 32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & 1U;
      if (!(bit == 0U))
      {
        uint32_t *ctx_n0 = ctx;
        amont_mul(ctx_n0, mu, resM, aM, resM);
      }
      uint32_t *ctx_n0 = ctx;
      amont_sqr(ctx_n0, mu, aM, aM);
    }
    from(n, mu, resM, res);
    return;
  }
  uint32_t aM[8U] = { 0U };
  to(n, mu, r2, a, aM);
  uint32_t resM[8U] = { 0U };
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 32U + 1U;
  }
  uint32_t ctx[16U] = { 0U };
  memcpy(ctx, n, 8U * sizeof (uint32_t));
  memcpy(ctx + 8U, r2, 8U * sizeof (uint32_t));
  uint32_t table[128U] = { 0U };
  uint32_t tmp[8U] = { 0U };
  uint32_t *t0 = table;
  uint32_t *t1 = table + 8U;
  uint32_t *ctx_n0 = ctx;
  uint32_t *ctx_r20 = ctx + 8U;
  from(ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, 8U * sizeof (uint32_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint32_t *t11 = table + (i + 1U) * 8U;
    uint32_t *ctx_n1 = ctx;
    amont_sqr(ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * 8U, tmp, 8U * sizeof (uint32_t));
    uint32_t *t2 = table + (2U * i + 2U) * 8U;
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * 8U, tmp, 8U * sizeof (uint32_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i = bBits / 4U * 4U;
    uint32_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, i, 4U);
    uint32_t bits_l32 = bits_c;
    const uint32_t *a_bits_l = table + bits_l32 * 8U;
    memcpy(resM, (uint32_t *)a_bits_l, 8U * sizeof (uint32_t));
  }
  else
  {
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + 8U;
    from(ctx_n, mu, ctx_r2, resM);
  }
  uint32_t tmp0[8U] = { 0U };
  for (uint32_t i = 0U; i < bBits / 4U; i++)
  {
    KRML_MAYBE_FOR4(i0,
      0U,
      4U,
      1U,
      uint32_t *ctx_n = ctx;
      amont_sqr(ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i - 4U;
    uint32_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, k, 4U);
    uint32_t bits_l32 = bits_l;
    const uint32_t *a_bits_l = table + bits_l32 * 8U;
    memcpy(tmp0, (uint32_t *)a_bits_l, 8U * sizeof (uint32_t));
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, resM, tmp0, resM);
  }
  from(n, mu, resM, res);
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
  if (bBits < 200U)
  {
    uint32_t aM[8U] = { 0U };
    to(n, mu, r2, a, aM);
    uint32_t resM[8U] = { 0U };
    uint32_t ctx[16U] = { 0U };
    memcpy(ctx, n, 8U * sizeof (uint32_t));
    memcpy(ctx + 8U, r2, 8U * sizeof (uint32_t));
    uint32_t sw = 0U;
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + 8U;
    from(ctx_n, mu, ctx_r2, resM);
    for (uint32_t i0 = 0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - 1U) / 32U;
      uint32_t j = (bBits - i0 - 1U) % 32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & 1U;
      uint32_t sw1 = bit ^ sw;
      KRML_MAYBE_FOR8(i,
        0U,
        8U,
        1U,
        uint32_t dummy = (0U - sw1) & (resM[i] ^ aM[i]);
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
      0U,
      8U,
      1U,
      uint32_t dummy = (0U - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;);
    from(n, mu, resM, res);
    return;
  }
  uint32_t aM[8U] = { 0U };
  to(n, mu, r2, a, aM);
  uint32_t resM[8U] = { 0U };
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 32U + 1U;
  }
  uint32_t ctx[16U] = { 0U };
  memcpy(ctx, n, 8U * sizeof (uint32_t));
  memcpy(ctx + 8U, r2, 8U * sizeof (uint32_t));
  uint32_t table[128U] = { 0U };
  uint32_t tmp[8U] = { 0U };
  uint32_t *t0 = table;
  uint32_t *t1 = table + 8U;
  uint32_t *ctx_n0 = ctx;
  uint32_t *ctx_r20 = ctx + 8U;
  from(ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, 8U * sizeof (uint32_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint32_t *t11 = table + (i + 1U) * 8U;
    uint32_t *ctx_n1 = ctx;
    amont_sqr(ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * 8U, tmp, 8U * sizeof (uint32_t));
    uint32_t *t2 = table + (2U * i + 2U) * 8U;
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * 8U, tmp, 8U * sizeof (uint32_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i0 = bBits / 4U * 4U;
    uint32_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, i0, 4U);
    memcpy(resM, (uint32_t *)table, 8U * sizeof (uint32_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint32_t c = FStar_UInt32_eq_mask(bits_c, i1 + 1U);
      const uint32_t *res_j = table + (i1 + 1U) * 8U;
      KRML_MAYBE_FOR8(i,
        0U,
        8U,
        1U,
        uint32_t *os = resM;
        uint32_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;););
  }
  else
  {
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + 8U;
    from(ctx_n, mu, ctx_r2, resM);
  }
  uint32_t tmp0[8U] = { 0U };
  for (uint32_t i0 = 0U; i0 < bBits / 4U; i0++)
  {
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *ctx_n = ctx;
      amont_sqr(ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i0 - 4U;
    uint32_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, k, 4U);
    memcpy(tmp0, (uint32_t *)table, 8U * sizeof (uint32_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint32_t c = FStar_UInt32_eq_mask(bits_l, i1 + 1U);
      const uint32_t *res_j = table + (i1 + 1U) * 8U;
      KRML_MAYBE_FOR8(i,
        0U,
        8U,
        1U,
        uint32_t *os = tmp0;
        uint32_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;););
    uint32_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, resM, tmp0, resM);
  }
  from(n, mu, resM, res);
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
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(8U, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    exp_vartime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, 8U * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
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
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(8U, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    exp_consttime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, 8U * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
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
  memset(one, 0U, 8U * sizeof (uint32_t));
  one[0U] = 1U;
  uint32_t bit0 = n[0U] & 1U;
  uint32_t m0 = 0U - bit0;
  uint32_t acc0 = 0U;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U))););
  uint32_t m1 = acc0;
  uint32_t m00 = m0 & m1;
  uint32_t bn_zero[8U] = { 0U };
  uint32_t mask = 0xFFFFFFFFU;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;);
  uint32_t mask1 = mask;
  uint32_t res10 = mask1;
  uint32_t m10 = res10;
  uint32_t acc = 0U;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U))););
  uint32_t m2 = acc;
  uint32_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(8U, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    uint32_t n2[8U] = { 0U };
    uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(0U, n[0U], 2U, n2);
    uint32_t *a1 = n + 1U;
    uint32_t *res1 = n2 + 1U;
    uint32_t c = c0;
    {
      uint32_t t1 = a1[4U * 0U];
      uint32_t *res_i0 = res1 + 4U * 0U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i0);
      uint32_t t10 = a1[4U * 0U + 1U];
      uint32_t *res_i1 = res1 + 4U * 0U + 1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, 0U, res_i1);
      uint32_t t11 = a1[4U * 0U + 2U];
      uint32_t *res_i2 = res1 + 4U * 0U + 2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, 0U, res_i2);
      uint32_t t12 = a1[4U * 0U + 3U];
      uint32_t *res_i = res1 + 4U * 0U + 3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, 0U, res_i);
    }
    KRML_MAYBE_FOR3(i,
      4U,
      7U,
      1U,
      uint32_t t1 = a1[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i););
    uint32_t c1 = c;
    uint32_t c2 = c1;
    KRML_MAYBE_UNUSED_VAR(c2);
    exp_vartime(nBits, n, a, 256U, n2, res);
  }
  else
  {
    memset(res, 0U, 8U * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
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
  uint32_t *r2 = (uint32_t *)KRML_HOST_CALLOC(8U, sizeof (uint32_t));
  uint32_t *n1 = (uint32_t *)KRML_HOST_CALLOC(8U, sizeof (uint32_t));
  uint32_t *r21 = r2;
  uint32_t *n11 = n1;
  memcpy(n11, n, 8U * sizeof (uint32_t));
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(8U, n);
  precompr2(nBits, n, r21);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 res = { .len = 8U, .n = n11, .mu = mu, .r2 = r21 };
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
  uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(0U, k1.n[0U], 2U, n2);
  uint32_t *a1 = k1.n + 1U;
  uint32_t *res1 = n2 + 1U;
  uint32_t c = c0;
  {
    uint32_t t1 = a1[4U * 0U];
    uint32_t *res_i0 = res1 + 4U * 0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i0);
    uint32_t t10 = a1[4U * 0U + 1U];
    uint32_t *res_i1 = res1 + 4U * 0U + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, 0U, res_i1);
    uint32_t t11 = a1[4U * 0U + 2U];
    uint32_t *res_i2 = res1 + 4U * 0U + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, 0U, res_i2);
    uint32_t t12 = a1[4U * 0U + 3U];
    uint32_t *res_i = res1 + 4U * 0U + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, 0U, res_i);
  }
  KRML_MAYBE_FOR3(i,
    4U,
    7U,
    1U,
    uint32_t t1 = a1[i];
    uint32_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i););
  uint32_t c1 = c;
  uint32_t c2 = c1;
  KRML_MAYBE_UNUSED_VAR(c2);
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, 256U, n2, res);
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
  if (len == 0U || !((len - 1U) / 4U + 1U <= 1073741823U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - 1U) / 4U + 1U);
  uint32_t *res = (uint32_t *)KRML_HOST_CALLOC((len - 1U) / 4U + 1U, sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 4U + 1U;
  uint32_t tmpLen = 4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    uint32_t *os = res2;
    uint32_t u = load32_be(tmp + (bnLen - i - 1U) * 4U);
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
  if (len == 0U || !((len - 1U) / 4U + 1U <= 1073741823U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - 1U) / 4U + 1U);
  uint32_t *res = (uint32_t *)KRML_HOST_CALLOC((len - 1U) / 4U + 1U, sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 4U + 1U;
  uint32_t tmpLen = 4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < (len - 1U) / 4U + 1U; i++)
  {
    uint32_t *os = res2;
    uint8_t *bj = tmp + i * 4U;
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
  KRML_MAYBE_UNUSED_VAR(tmp);
  KRML_MAYBE_FOR8(i, 0U, 8U, 1U, store32_be(res + i * 4U, b[8U - i - 1U]););
}

/**
Serialize a bignum into little-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_32_bn_to_bytes_le(uint32_t *b, uint8_t *res)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(tmp);
  KRML_MAYBE_FOR8(i, 0U, 8U, 1U, store32_le(res + i * 4U, b[i]););
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
  uint32_t acc = 0U;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t beq = FStar_UInt32_eq_mask(a[i], b[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U))););
  return acc;
}

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be 256-bit bignums, i.e. uint32_t[8].
*/
uint32_t Hacl_Bignum256_32_eq_mask(uint32_t *a, uint32_t *b)
{
  uint32_t mask = 0xFFFFFFFFU;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], b[i]);
    mask = uu____0 & mask;);
  uint32_t mask1 = mask;
  return mask1;
}

