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


#include "Hacl_Bignum4096.h"

#include "internal/Hacl_Bignum_Base.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************

A verified 4096-bit bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of sixty four unsigned 64-bit integers, i.e. uint64_t[64]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint64_t sixteen[64] = { 0x10 }

  (relying on the fact that when an initializer-list is provided, the remainder
  of the object gets initialized as if it had static storage duration, i.e. with
  zeroes)

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 32-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/**
Write `a + b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum4096_add(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = a[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res + 4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i););
  return c;
}

/**
Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum4096_sub(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = a[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i););
  return c;
}

/**
Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum4096_add_mod(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = a[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i););
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = res[4U * i];
    uint64_t t20 = n[4U * i];
    uint64_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * i + 1U];
    uint64_t t21 = n[4U * i + 1U];
    uint64_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * i + 2U];
    uint64_t t22 = n[4U * i + 2U];
    uint64_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * i + 3U];
    uint64_t t2 = n[4U * i + 3U];
    uint64_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i););
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

/**
Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum4096_sub_mod(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = a[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i););
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = res[4U * i];
    uint64_t t20 = n[4U * i];
    uint64_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * i + 1U];
    uint64_t t21 = n[4U * i + 1U];
    uint64_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * i + 2U];
    uint64_t t22 = n[4U * i + 2U];
    uint64_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * i + 3U];
    uint64_t t2 = n[4U * i + 3U];
    uint64_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i););
  uint64_t c1 = c;
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t c2 = 0ULL - c00;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x;
  }
}

/**
Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128].
*/
void Hacl_Bignum4096_mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t tmp[256U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(64U, a, b, tmp, res);
}

/**
Write `a * a` in `res`.

  The argument a is meant to be a 4096-bit bignum, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128].
*/
void Hacl_Bignum4096_sqr(uint64_t *a, uint64_t *res)
{
  uint64_t tmp[256U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(64U, a, tmp, res);
}

static inline void precompr2(uint32_t nBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, 64U * sizeof (uint64_t));
  uint32_t i = nBits / 64U;
  uint32_t j = nBits % 64U;
  res[i] = res[i] | 1ULL << j;
  for (uint32_t i0 = 0U; i0 < 8192U - nBits; i0++)
  {
    Hacl_Bignum4096_add_mod(n, res, res, res);
  }
}

static inline void reduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  for (uint32_t i0 = 0U; i0 < 64U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = 0ULL;
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint64_t a_i = n[4U * i];
      uint64_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[4U * i + 1U];
      uint64_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[4U * i + 2U];
      uint64_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[4U * i + 3U];
      uint64_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i););
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + 64U + i0;
    uint64_t res_j = c[64U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + 64U, 64U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c1 = 0ULL;
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t t1 = res[4U * i];
    uint64_t t20 = n[4U * i];
    uint64_t *res_i0 = tmp + 4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = res[4U * i + 1U];
    uint64_t t21 = n[4U * i + 1U];
    uint64_t *res_i1 = tmp + 4U * i + 1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = res[4U * i + 2U];
    uint64_t t22 = n[4U * i + 2U];
    uint64_t *res_i2 = tmp + 4U * i + 2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = res[4U * i + 3U];
    uint64_t t2 = n[4U * i + 3U];
    uint64_t *res_i = tmp + 4U * i + 3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i););
  uint64_t c10 = c1;
  uint64_t c2 = c00 - c10;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static inline void to(uint64_t *n, uint64_t nInv, uint64_t *r2, uint64_t *a, uint64_t *aM)
{
  uint64_t c[128U] = { 0U };
  Hacl_Bignum4096_mul(a, r2, c);
  reduction(n, nInv, c, aM);
}

static inline void from(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *a)
{
  uint64_t tmp[128U] = { 0U };
  memcpy(tmp, aM, 64U * sizeof (uint64_t));
  reduction(n, nInv_u64, tmp, a);
}

static inline void areduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  for (uint32_t i0 = 0U; i0 < 64U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = 0ULL;
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint64_t a_i = n[4U * i];
      uint64_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[4U * i + 1U];
      uint64_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[4U * i + 2U];
      uint64_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[4U * i + 3U];
      uint64_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i););
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + 64U + i0;
    uint64_t res_j = c[64U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + 64U, 64U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c1 = Hacl_Bignum4096_sub(res, n, tmp);
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t m = 0ULL - c00;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;
  }
}

static inline void
amont_mul(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  uint64_t c[128U] = { 0U };
  Hacl_Bignum4096_mul(aM, bM, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void amont_sqr(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  uint64_t c[128U] = { 0U };
  Hacl_Bignum4096_sqr(aM, c);
  areduction(n, nInv_u64, c, resM);
}

static inline void
bn_slow_precomp(uint64_t *n, uint64_t mu, uint64_t *r2, uint64_t *a, uint64_t *res)
{
  uint64_t a_mod[64U] = { 0U };
  uint64_t a1[128U] = { 0U };
  memcpy(a1, a, 128U * sizeof (uint64_t));
  areduction(n, mu, a1, a_mod);
  to(n, mu, r2, a_mod, res);
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be a 8192-bit bignum, i.e. uint64_t[128].
  The argument n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1 
*/
bool Hacl_Bignum4096_mod(uint64_t *n, uint64_t *a, uint64_t *res)
{
  uint64_t one[64U] = { 0U };
  memset(one, 0U, 64U * sizeof (uint64_t));
  one[0U] = 1ULL;
  uint64_t bit0 = n[0U] & 1ULL;
  uint64_t m0 = 0ULL - bit0;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m1 = acc;
  uint64_t is_valid_m = m0 & m1;
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(64U, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    uint64_t r2[64U] = { 0U };
    precompr2(nBits, n, r2);
    uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
    bn_slow_precomp(n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, 64U * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}

static uint64_t exp_check(uint64_t *n, uint64_t *a, uint32_t bBits, uint64_t *b)
{
  uint64_t one[64U] = { 0U };
  memset(one, 0U, 64U * sizeof (uint64_t));
  one[0U] = 1ULL;
  uint64_t bit0 = n[0U] & 1ULL;
  uint64_t m0 = 0ULL - bit0;
  uint64_t acc0 = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m10 = acc0;
  uint64_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 64U + 1U;
  }
  uint64_t m1;
  if (bBits < 64U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
    uint64_t *b2 = (uint64_t *)alloca(bLen * sizeof (uint64_t));
    memset(b2, 0U, bLen * sizeof (uint64_t));
    uint32_t i0 = bBits / 64U;
    uint32_t j = bBits % 64U;
    b2[i0] = b2[i0] | 1ULL << j;
    uint64_t acc = 0ULL;
    for (uint32_t i = 0U; i < bLen; i++)
    {
      uint64_t beq = FStar_UInt64_eq_mask(b[i], b2[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
    }
    uint64_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = 0xFFFFFFFFFFFFFFFFULL;
  }
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m2 = acc;
  uint64_t m = m1 & m2;
  return m00 & m;
}

static inline void
exp_vartime_precomp(
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  if (bBits < 200U)
  {
    uint64_t aM[64U] = { 0U };
    to(n, mu, r2, a, aM);
    uint64_t resM[64U] = { 0U };
    uint64_t ctx[128U] = { 0U };
    memcpy(ctx, n, 64U * sizeof (uint64_t));
    memcpy(ctx + 64U, r2, 64U * sizeof (uint64_t));
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + 64U;
    from(ctx_n, mu, ctx_r2, resM);
    for (uint32_t i = 0U; i < bBits; i++)
    {
      uint32_t i1 = i / 64U;
      uint32_t j = i % 64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & 1ULL;
      if (!(bit == 0ULL))
      {
        uint64_t *ctx_n0 = ctx;
        amont_mul(ctx_n0, mu, resM, aM, resM);
      }
      uint64_t *ctx_n0 = ctx;
      amont_sqr(ctx_n0, mu, aM, aM);
    }
    from(n, mu, resM, res);
    return;
  }
  uint64_t aM[64U] = { 0U };
  to(n, mu, r2, a, aM);
  uint64_t resM[64U] = { 0U };
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 64U + 1U;
  }
  uint64_t ctx[128U] = { 0U };
  memcpy(ctx, n, 64U * sizeof (uint64_t));
  memcpy(ctx + 64U, r2, 64U * sizeof (uint64_t));
  uint64_t table[1024U] = { 0U };
  uint64_t tmp[64U] = { 0U };
  uint64_t *t0 = table;
  uint64_t *t1 = table + 64U;
  uint64_t *ctx_n0 = ctx;
  uint64_t *ctx_r20 = ctx + 64U;
  from(ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, 64U * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint64_t *t11 = table + (i + 1U) * 64U;
    uint64_t *ctx_n1 = ctx;
    amont_sqr(ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * 64U, tmp, 64U * sizeof (uint64_t));
    uint64_t *t2 = table + (2U * i + 2U) * 64U;
    uint64_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * 64U, tmp, 64U * sizeof (uint64_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i = bBits / 4U * 4U;
    uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, i, 4U);
    uint32_t bits_l32 = (uint32_t)bits_c;
    const uint64_t *a_bits_l = table + bits_l32 * 64U;
    memcpy(resM, (uint64_t *)a_bits_l, 64U * sizeof (uint64_t));
  }
  else
  {
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + 64U;
    from(ctx_n, mu, ctx_r2, resM);
  }
  uint64_t tmp0[64U] = { 0U };
  for (uint32_t i = 0U; i < bBits / 4U; i++)
  {
    KRML_MAYBE_FOR4(i0,
      0U,
      4U,
      1U,
      uint64_t *ctx_n = ctx;
      amont_sqr(ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, k, 4U);
    uint32_t bits_l32 = (uint32_t)bits_l;
    const uint64_t *a_bits_l = table + bits_l32 * 64U;
    memcpy(tmp0, (uint64_t *)a_bits_l, 64U * sizeof (uint64_t));
    uint64_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, resM, tmp0, resM);
  }
  from(n, mu, resM, res);
}

static inline void
exp_consttime_precomp(
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  if (bBits < 200U)
  {
    uint64_t aM[64U] = { 0U };
    to(n, mu, r2, a, aM);
    uint64_t resM[64U] = { 0U };
    uint64_t ctx[128U] = { 0U };
    memcpy(ctx, n, 64U * sizeof (uint64_t));
    memcpy(ctx + 64U, r2, 64U * sizeof (uint64_t));
    uint64_t sw = 0ULL;
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + 64U;
    from(ctx_n, mu, ctx_r2, resM);
    for (uint32_t i0 = 0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - 1U) / 64U;
      uint32_t j = (bBits - i0 - 1U) % 64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & 1ULL;
      uint64_t sw1 = bit ^ sw;
      for (uint32_t i = 0U; i < 64U; i++)
      {
        uint64_t dummy = (0ULL - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;
      }
      uint64_t *ctx_n0 = ctx;
      amont_mul(ctx_n0, mu, aM, resM, aM);
      uint64_t *ctx_n1 = ctx;
      amont_sqr(ctx_n1, mu, resM, resM);
      sw = bit;
    }
    uint64_t sw0 = sw;
    for (uint32_t i = 0U; i < 64U; i++)
    {
      uint64_t dummy = (0ULL - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    from(n, mu, resM, res);
    return;
  }
  uint64_t aM[64U] = { 0U };
  to(n, mu, r2, a, aM);
  uint64_t resM[64U] = { 0U };
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 64U + 1U;
  }
  uint64_t ctx[128U] = { 0U };
  memcpy(ctx, n, 64U * sizeof (uint64_t));
  memcpy(ctx + 64U, r2, 64U * sizeof (uint64_t));
  uint64_t table[1024U] = { 0U };
  uint64_t tmp[64U] = { 0U };
  uint64_t *t0 = table;
  uint64_t *t1 = table + 64U;
  uint64_t *ctx_n0 = ctx;
  uint64_t *ctx_r20 = ctx + 64U;
  from(ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, 64U * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint64_t *t11 = table + (i + 1U) * 64U;
    uint64_t *ctx_n1 = ctx;
    amont_sqr(ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * 64U, tmp, 64U * sizeof (uint64_t));
    uint64_t *t2 = table + (2U * i + 2U) * 64U;
    uint64_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * 64U, tmp, 64U * sizeof (uint64_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i0 = bBits / 4U * 4U;
    uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, i0, 4U);
    memcpy(resM, (uint64_t *)table, 64U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_c, (uint64_t)(i1 + 1U));
      const uint64_t *res_j = table + (i1 + 1U) * 64U;
      for (uint32_t i = 0U; i < 64U; i++)
      {
        uint64_t *os = resM;
        uint64_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;
      });
  }
  else
  {
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + 64U;
    from(ctx_n, mu, ctx_r2, resM);
  }
  uint64_t tmp0[64U] = { 0U };
  for (uint32_t i0 = 0U; i0 < bBits / 4U; i0++)
  {
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint64_t *ctx_n = ctx;
      amont_sqr(ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i0 - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, k, 4U);
    memcpy(tmp0, (uint64_t *)table, 64U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i1 + 1U));
      const uint64_t *res_j = table + (i1 + 1U) * 64U;
      for (uint32_t i = 0U; i < 64U; i++)
      {
        uint64_t *os = tmp0;
        uint64_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;
      });
    uint64_t *ctx_n = ctx;
    amont_mul(ctx_n, mu, resM, tmp0, resM);
  }
  from(n, mu, resM, res);
}

static inline void
exp_vartime(
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t r2[64U] = { 0U };
  precompr2(nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  exp_vartime_precomp(n, mu, r2, a, bBits, b, res);
}

static inline void
exp_consttime(
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t r2[64U] = { 0U };
  precompr2(nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  exp_consttime_precomp(n, mu, r2, a, bBits, b, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

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
Hacl_Bignum4096_mod_exp_vartime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(64U, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    exp_vartime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, 64U * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

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
Hacl_Bignum4096_mod_exp_consttime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = exp_check(n, a, bBits, b);
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(64U, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    exp_consttime(nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, 64U * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n
*/
bool Hacl_Bignum4096_mod_inv_prime_vartime(uint64_t *n, uint64_t *a, uint64_t *res)
{
  uint64_t one[64U] = { 0U };
  memset(one, 0U, 64U * sizeof (uint64_t));
  one[0U] = 1ULL;
  uint64_t bit0 = n[0U] & 1ULL;
  uint64_t m0 = 0ULL - bit0;
  uint64_t acc0 = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m1 = acc0;
  uint64_t m00 = m0 & m1;
  uint64_t bn_zero[64U] = { 0U };
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  uint64_t res10 = mask1;
  uint64_t m10 = res10;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m2 = acc;
  uint64_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(64U, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    uint64_t n2[64U] = { 0U };
    uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(0ULL, n[0U], 2ULL, n2);
    uint64_t *a1 = n + 1U;
    uint64_t *res1 = n2 + 1U;
    uint64_t c = c0;
    KRML_MAYBE_FOR15(i,
      0U,
      15U,
      1U,
      uint64_t t1 = a1[4U * i];
      uint64_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i0);
      uint64_t t10 = a1[4U * i + 1U];
      uint64_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, 0ULL, res_i1);
      uint64_t t11 = a1[4U * i + 2U];
      uint64_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, 0ULL, res_i2);
      uint64_t t12 = a1[4U * i + 3U];
      uint64_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, 0ULL, res_i););
    KRML_MAYBE_FOR3(i,
      60U,
      63U,
      1U,
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i););
    uint64_t c1 = c;
    uint64_t c2 = c1;
    KRML_MAYBE_UNUSED_VAR(c2);
    exp_vartime(nBits, n, a, 4096U, n2, res);
  }
  else
  {
    memset(res, 0U, 64U * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be a 4096-bit bignum, i.e. uint64_t[64].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum4096_mont_ctx_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *Hacl_Bignum4096_mont_ctx_init(uint64_t *n)
{
  uint64_t *r2 = (uint64_t *)KRML_HOST_CALLOC(64U, sizeof (uint64_t));
  uint64_t *n1 = (uint64_t *)KRML_HOST_CALLOC(64U, sizeof (uint64_t));
  uint64_t *r21 = r2;
  uint64_t *n11 = n1;
  memcpy(n11, n, 64U * sizeof (uint64_t));
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(64U, n);
  precompr2(nBits, n, r21);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 res = { .len = 64U, .n = n11, .mu = mu, .r2 = r21 };
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
  *buf =
    (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *)KRML_HOST_MALLOC(sizeof (
        Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
      ));
  buf[0U] = res;
  return buf;
}

/**
Deallocate the memory previously allocated by Hacl_Bignum4096_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.
*/
void Hacl_Bignum4096_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint64_t *n = k1.n;
  uint64_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be a 8192-bit bignum, i.e. uint64_t[128].
  The outparam res is meant to be a 4096-bit bignum, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.
*/
void
Hacl_Bignum4096_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  bn_slow_precomp(k1.n, k1.mu, k1.r2, a, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum4096_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum4096_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  exp_consttime_precomp(k1.n, k1.mu, k1.r2, a, bBits, b, res);
}

/**
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The argument k is a montgomery context obtained through Hacl_Bignum4096_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n
*/
void
Hacl_Bignum4096_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint64_t n2[64U] = { 0U };
  uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(0ULL, k1.n[0U], 2ULL, n2);
  uint64_t *a1 = k1.n + 1U;
  uint64_t *res1 = n2 + 1U;
  uint64_t c = c0;
  KRML_MAYBE_FOR15(i,
    0U,
    15U,
    1U,
    uint64_t t1 = a1[4U * i];
    uint64_t *res_i0 = res1 + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i0);
    uint64_t t10 = a1[4U * i + 1U];
    uint64_t *res_i1 = res1 + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, 0ULL, res_i1);
    uint64_t t11 = a1[4U * i + 2U];
    uint64_t *res_i2 = res1 + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, 0ULL, res_i2);
    uint64_t t12 = a1[4U * i + 3U];
    uint64_t *res_i = res1 + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, 0ULL, res_i););
  KRML_MAYBE_FOR3(i,
    60U,
    63U,
    1U,
    uint64_t t1 = a1[i];
    uint64_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i););
  uint64_t c1 = c;
  uint64_t c2 = c1;
  KRML_MAYBE_UNUSED_VAR(c2);
  exp_vartime_precomp(k1.n, k1.mu, k1.r2, a, 4096U, n2, res);
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
uint64_t *Hacl_Bignum4096_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if (len == 0U || !((len - 1U) / 8U + 1U <= 536870911U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - 1U) / 8U + 1U);
  uint64_t *res = (uint64_t *)KRML_HOST_CALLOC((len - 1U) / 8U + 1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 8U + 1U;
  uint32_t tmpLen = 8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    uint64_t *os = res2;
    uint64_t u = load64_be(tmp + (bnLen - i - 1U) * 8U);
    uint64_t x = u;
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
uint64_t *Hacl_Bignum4096_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if (len == 0U || !((len - 1U) / 8U + 1U <= 536870911U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - 1U) / 8U + 1U);
  uint64_t *res = (uint64_t *)KRML_HOST_CALLOC((len - 1U) / 8U + 1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 8U + 1U;
  uint32_t tmpLen = 8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < (len - 1U) / 8U + 1U; i++)
  {
    uint64_t *os = res2;
    uint8_t *bj = tmp + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  return res2;
}

/**
Serialize a bignum into big-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory.
*/
void Hacl_Bignum4096_bn_to_bytes_be(uint64_t *b, uint8_t *res)
{
  uint8_t tmp[512U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(tmp);
  for (uint32_t i = 0U; i < 64U; i++)
  {
    store64_be(res + i * 8U, b[64U - i - 1U]);
  }
}

/**
Serialize a bignum into little-endian memory.

  The argument b points to a 4096-bit bignum.
  The outparam res points to 512 bytes of valid memory.
*/
void Hacl_Bignum4096_bn_to_bytes_le(uint64_t *b, uint8_t *res)
{
  uint8_t tmp[512U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(tmp);
  for (uint32_t i = 0U; i < 64U; i++)
  {
    store64_le(res + i * 8U, b[i]);
  }
}


/***************/
/* Comparisons */
/***************/


/**
Returns 2^64 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
*/
uint64_t Hacl_Bignum4096_lt_mask(uint64_t *a, uint64_t *b)
{
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], b[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  return acc;
}

/**
Returns 2^64 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
*/
uint64_t Hacl_Bignum4096_eq_mask(uint64_t *a, uint64_t *b)
{
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], b[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  return mask1;
}

