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


#include "internal/Hacl_K256_ECDSA.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_K256_PrecompTable.h"
#include "internal/Hacl_Bignum_K256.h"
#include "internal/Hacl_Bignum_Base.h"

static inline uint64_t
bn_add(uint32_t aLen, uint64_t *a, uint32_t bLen, uint64_t *b, uint64_t *res)
{
  uint64_t *a0 = a;
  uint64_t *res0 = res;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < bLen / (uint32_t)4U; i++)
  {
    uint64_t t1 = a0[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res0 + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res0 + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res0 + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res0 + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = bLen / (uint32_t)4U * (uint32_t)4U; i < bLen; i++)
  {
    uint64_t t1 = a0[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res0 + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  if (bLen < aLen)
  {
    uint64_t *a1 = a + bLen;
    uint64_t *res1 = res + bLen;
    uint64_t c = c00;
    for (uint32_t i = (uint32_t)0U; i < (aLen - bLen) / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = (aLen - bLen) / (uint32_t)4U * (uint32_t)4U; i < aLen - bLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c1 = c;
    return c1;
  }
  return c00;
}

static uint64_t add4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  {
    uint64_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  return c;
}

static void add_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = (uint64_t)0U;
  {
    uint64_t t1 = res[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = n[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;);
}

static void sub_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = (uint64_t)0U;
  {
    uint64_t t1 = res[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = n[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = (uint64_t)0U - c00;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = res;
    uint64_t x = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x;);
}

static void mul4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    {
      uint64_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    uint64_t r = c;
    res[(uint32_t)4U + i0] = r;);
}

static void sqr4(uint64_t *a, uint64_t *res)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    res[i0 + i0] = r;);
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, res, res);
  uint64_t tmp[8U] = { 0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;);
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, tmp, res);
}

static inline uint64_t is_qelem_zero(uint64_t *f)
{
  uint64_t bn_zero[4U] = { 0U };
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t uu____0 = FStar_UInt64_eq_mask(f[i], bn_zero[i]);
    mask = uu____0 & mask;);
  uint64_t mask1 = mask;
  uint64_t res = mask1;
  return res;
}

static inline bool is_qelem_zero_vartime(uint64_t *f)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  return f0 == (uint64_t)0U && f1 == (uint64_t)0U && f2 == (uint64_t)0U && f3 == (uint64_t)0U;
}

static inline uint64_t load_qelem_check(uint64_t *f, uint8_t *b)
{
  uint64_t n[4U] = { 0U };
  n[0U] = (uint64_t)0xbfd25e8cd0364141U;
  n[1U] = (uint64_t)0xbaaedce6af48a03bU;
  n[2U] = (uint64_t)0xfffffffffffffffeU;
  n[3U] = (uint64_t)0xffffffffffffffffU;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = f;
    uint64_t u = load64_be(b + ((uint32_t)4U - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;);
  uint64_t is_zero = is_qelem_zero(f);
  uint64_t acc = (uint64_t)0U;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t beq = FStar_UInt64_eq_mask(f[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(f[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U))););
  uint64_t is_lt_q = acc;
  return ~is_zero & is_lt_q;
}

static inline bool load_qelem_vartime(uint64_t *f, uint8_t *b)
{
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = f;
    uint64_t u = load64_be(b + ((uint32_t)4U - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;);
  bool is_zero = is_qelem_zero_vartime(f);
  uint64_t a0 = f[0U];
  uint64_t a1 = f[1U];
  uint64_t a2 = f[2U];
  uint64_t a3 = f[3U];
  bool is_lt_q_b;
  if (a3 < (uint64_t)0xffffffffffffffffU)
  {
    is_lt_q_b = true;
  }
  else if (a2 < (uint64_t)0xfffffffffffffffeU)
  {
    is_lt_q_b = true;
  }
  else if (a2 > (uint64_t)0xfffffffffffffffeU)
  {
    is_lt_q_b = false;
  }
  else if (a1 < (uint64_t)0xbaaedce6af48a03bU)
  {
    is_lt_q_b = true;
  }
  else if (a1 > (uint64_t)0xbaaedce6af48a03bU)
  {
    is_lt_q_b = false;
  }
  else
  {
    is_lt_q_b = a0 < (uint64_t)0xbfd25e8cd0364141U;
  }
  return !is_zero && is_lt_q_b;
}

static inline void modq_short(uint64_t *out, uint64_t *a)
{
  uint64_t tmp[4U] = { 0U };
  tmp[0U] = (uint64_t)0x402da1732fc9bebfU;
  tmp[1U] = (uint64_t)0x4551231950b75fc4U;
  tmp[2U] = (uint64_t)0x1U;
  tmp[3U] = (uint64_t)0x0U;
  uint64_t c = add4(a, tmp, out);
  uint64_t mask = (uint64_t)0U - c;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = out;
    uint64_t x = (mask & out[i]) | (~mask & a[i]);
    os[i] = x;);
}

static inline void load_qelem_modq(uint64_t *f, uint8_t *b)
{
  uint64_t tmp[4U] = { 0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = f;
    uint64_t u = load64_be(b + ((uint32_t)4U - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;);
  memcpy(tmp, f, (uint32_t)4U * sizeof (uint64_t));
  modq_short(f, tmp);
}

static inline void store_qelem(uint8_t *b, uint64_t *f)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    store64_be(b + i * (uint32_t)8U, f[(uint32_t)4U - i - (uint32_t)1U]););
}

static inline void qadd(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t n[4U] = { 0U };
  n[0U] = (uint64_t)0xbfd25e8cd0364141U;
  n[1U] = (uint64_t)0xbaaedce6af48a03bU;
  n[2U] = (uint64_t)0xfffffffffffffffeU;
  n[3U] = (uint64_t)0xffffffffffffffffU;
  add_mod4(n, f1, f2, out);
}

static inline uint64_t
mul_pow2_256_minus_q_add(
  uint32_t len,
  uint32_t resLen,
  uint64_t *t01,
  uint64_t *a,
  uint64_t *e,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + (uint32_t)2U);
  uint64_t tmp[len + (uint32_t)2U];
  memset(tmp, 0U, (len + (uint32_t)2U) * sizeof (uint64_t));
  memset(tmp, 0U, (len + (uint32_t)2U) * sizeof (uint64_t));
  KRML_MAYBE_FOR2(i0,
    (uint32_t)0U,
    (uint32_t)2U,
    (uint32_t)1U,
    uint64_t bj = t01[i0];
    uint64_t *res_j = tmp + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U; i++)
    {
      uint64_t a_i = a[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    tmp[len + i0] = r;);
  memcpy(res + (uint32_t)2U, a, len * sizeof (uint64_t));
  uint64_t uu____0 = bn_add(resLen, res, len + (uint32_t)2U, tmp, res);
  uint64_t c = bn_add(resLen, res, (uint32_t)4U, e, res);
  return c;
}

static inline void modq(uint64_t *out, uint64_t *a)
{
  uint64_t r[4U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  tmp[0U] = (uint64_t)0x402da1732fc9bebfU;
  tmp[1U] = (uint64_t)0x4551231950b75fc4U;
  tmp[2U] = (uint64_t)0x1U;
  tmp[3U] = (uint64_t)0x0U;
  uint64_t *t01 = tmp;
  uint64_t m[7U] = { 0U };
  uint64_t p[5U] = { 0U };
  uint64_t
  c0 = mul_pow2_256_minus_q_add((uint32_t)4U, (uint32_t)7U, t01, a + (uint32_t)4U, a, m);
  uint64_t
  c10 = mul_pow2_256_minus_q_add((uint32_t)3U, (uint32_t)5U, t01, m + (uint32_t)4U, m, p);
  uint64_t
  c2 = mul_pow2_256_minus_q_add((uint32_t)1U, (uint32_t)4U, t01, p + (uint32_t)4U, p, r);
  uint64_t c00 = c2;
  uint64_t c1 = add4(r, tmp, out);
  uint64_t mask = (uint64_t)0U - (c00 + c1);
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = out;
    uint64_t x = (mask & out[i]) | (~mask & r[i]);
    os[i] = x;);
}

static inline void qmul(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t tmp[8U] = { 0U };
  mul4(f1, f2, tmp);
  modq(out, tmp);
}

static inline void qsqr(uint64_t *out, uint64_t *f)
{
  uint64_t tmp[8U] = { 0U };
  sqr4(f, tmp);
  modq(out, tmp);
}

static inline void qnegate_conditional_vartime(uint64_t *f, bool is_negate)
{
  uint64_t n[4U] = { 0U };
  n[0U] = (uint64_t)0xbfd25e8cd0364141U;
  n[1U] = (uint64_t)0xbaaedce6af48a03bU;
  n[2U] = (uint64_t)0xfffffffffffffffeU;
  n[3U] = (uint64_t)0xffffffffffffffffU;
  uint64_t zero[4U] = { 0U };
  if (is_negate)
  {
    sub_mod4(n, zero, f, f);
  }
}

static inline bool is_qelem_le_q_halved_vartime(uint64_t *f)
{
  uint64_t a0 = f[0U];
  uint64_t a1 = f[1U];
  uint64_t a2 = f[2U];
  uint64_t a3 = f[3U];
  if (a3 < (uint64_t)0x7fffffffffffffffU)
  {
    return true;
  }
  if (a3 > (uint64_t)0x7fffffffffffffffU)
  {
    return false;
  }
  if (a2 < (uint64_t)0xffffffffffffffffU)
  {
    return true;
  }
  if (a2 > (uint64_t)0xffffffffffffffffU)
  {
    return false;
  }
  if (a1 < (uint64_t)0x5d576e7357a4501dU)
  {
    return true;
  }
  if (a1 > (uint64_t)0x5d576e7357a4501dU)
  {
    return false;
  }
  return a0 <= (uint64_t)0xdfe92f46681b20a0U;
}

static inline void qmul_shift_384(uint64_t *res, uint64_t *a, uint64_t *b)
{
  uint64_t l[8U] = { 0U };
  mul4(a, b, l);
  uint64_t res_b_padded[4U] = { 0U };
  memcpy(res_b_padded, l + (uint32_t)6U, (uint32_t)2U * sizeof (uint64_t));
  uint64_t
  c0 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, res_b_padded[0U], (uint64_t)1U, res);
  uint64_t *a1 = res_b_padded + (uint32_t)1U;
  uint64_t *res1 = res + (uint32_t)1U;
  uint64_t c = c0;
  KRML_MAYBE_FOR3(i,
    (uint32_t)0U,
    (uint32_t)3U,
    (uint32_t)1U,
    uint64_t t1 = a1[i];
    uint64_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i););
  uint64_t c1 = c;
  uint64_t uu____0 = c1;
  uint64_t flag = l[5U] >> (uint32_t)63U;
  uint64_t mask = (uint64_t)0U - flag;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = res;
    uint64_t x = (mask & res[i]) | (~mask & res_b_padded[i]);
    os[i] = x;);
}

static inline void qsquare_times_in_place(uint64_t *out, uint32_t b)
{
  for (uint32_t i = (uint32_t)0U; i < b; i++)
  {
    qsqr(out, out);
  }
}

static inline void qsquare_times(uint64_t *out, uint64_t *a, uint32_t b)
{
  memcpy(out, a, (uint32_t)4U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < b; i++)
  {
    qsqr(out, out);
  }
}

static inline void qinv(uint64_t *out, uint64_t *f)
{
  uint64_t x_10[4U] = { 0U };
  uint64_t x_11[4U] = { 0U };
  uint64_t x_101[4U] = { 0U };
  uint64_t x_111[4U] = { 0U };
  uint64_t x_1001[4U] = { 0U };
  uint64_t x_1011[4U] = { 0U };
  uint64_t x_1101[4U] = { 0U };
  qsquare_times(x_10, f, (uint32_t)1U);
  qmul(x_11, x_10, f);
  qmul(x_101, x_10, x_11);
  qmul(x_111, x_10, x_101);
  qmul(x_1001, x_10, x_111);
  qmul(x_1011, x_10, x_1001);
  qmul(x_1101, x_10, x_1011);
  uint64_t x6[4U] = { 0U };
  uint64_t x8[4U] = { 0U };
  uint64_t x14[4U] = { 0U };
  qsquare_times(x6, x_1101, (uint32_t)2U);
  qmul(x6, x6, x_1011);
  qsquare_times(x8, x6, (uint32_t)2U);
  qmul(x8, x8, x_11);
  qsquare_times(x14, x8, (uint32_t)6U);
  qmul(x14, x14, x6);
  uint64_t x56[4U] = { 0U };
  qsquare_times(out, x14, (uint32_t)14U);
  qmul(out, out, x14);
  qsquare_times(x56, out, (uint32_t)28U);
  qmul(x56, x56, out);
  qsquare_times(out, x56, (uint32_t)56U);
  qmul(out, out, x56);
  qsquare_times_in_place(out, (uint32_t)14U);
  qmul(out, out, x14);
  qsquare_times_in_place(out, (uint32_t)3U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, (uint32_t)5U);
  qmul(out, out, x_1011);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_1011);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, (uint32_t)5U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, (uint32_t)6U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, (uint32_t)3U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, (uint32_t)5U);
  qmul(out, out, x_1001);
  qsquare_times_in_place(out, (uint32_t)6U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, (uint32_t)10U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, (uint32_t)9U);
  qmul(out, out, x8);
  qsquare_times_in_place(out, (uint32_t)5U);
  qmul(out, out, x_1001);
  qsquare_times_in_place(out, (uint32_t)6U);
  qmul(out, out, x_1011);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, (uint32_t)5U);
  qmul(out, out, x_11);
  qsquare_times_in_place(out, (uint32_t)6U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, (uint32_t)10U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, (uint32_t)4U);
  qmul(out, out, x_1001);
  qsquare_times_in_place(out, (uint32_t)6U);
  qmul(out, out, f);
  qsquare_times_in_place(out, (uint32_t)8U);
  qmul(out, out, x6);
}

void Hacl_Impl_K256_Point_make_point_at_inf(uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  memset(px, 0U, (uint32_t)5U * sizeof (uint64_t));
  memset(py, 0U, (uint32_t)5U * sizeof (uint64_t));
  py[0U] = (uint64_t)1U;
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
}

void Hacl_Impl_K256_Point_point_negate(uint64_t *out, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  uint64_t *ox = out;
  uint64_t *oy = out + (uint32_t)5U;
  uint64_t *oz = out + (uint32_t)10U;
  ox[0U] = px[0U];
  ox[1U] = px[1U];
  ox[2U] = px[2U];
  ox[3U] = px[3U];
  ox[4U] = px[4U];
  oz[0U] = pz[0U];
  oz[1U] = pz[1U];
  oz[2U] = pz[2U];
  oz[3U] = pz[3U];
  oz[4U] = pz[4U];
  uint64_t a0 = py[0U];
  uint64_t a1 = py[1U];
  uint64_t a2 = py[2U];
  uint64_t a3 = py[3U];
  uint64_t a4 = py[4U];
  uint64_t r0 = (uint64_t)18014381329608892U - a0;
  uint64_t r1 = (uint64_t)18014398509481980U - a1;
  uint64_t r2 = (uint64_t)18014398509481980U - a2;
  uint64_t r3 = (uint64_t)18014398509481980U - a3;
  uint64_t r4 = (uint64_t)1125899906842620U - a4;
  uint64_t f0 = r0;
  uint64_t f1 = r1;
  uint64_t f2 = r2;
  uint64_t f3 = r3;
  uint64_t f4 = r4;
  oy[0U] = f0;
  oy[1U] = f1;
  oy[2U] = f2;
  oy[3U] = f3;
  oy[4U] = f4;
  Hacl_K256_Field_fnormalize_weak(oy, oy);
}

static inline void point_negate_conditional_vartime(uint64_t *p, bool is_negate)
{
  if (is_negate)
  {
    Hacl_Impl_K256_Point_point_negate(p, p);
    return;
  }
}

static inline bool fmul_fmul_eq_vartime(uint64_t *a, uint64_t *bz, uint64_t *c, uint64_t *dz)
{
  uint64_t a_bz[5U] = { 0U };
  uint64_t c_dz[5U] = { 0U };
  Hacl_K256_Field_fmul(a_bz, a, bz);
  Hacl_K256_Field_fmul(c_dz, c, dz);
  Hacl_K256_Field_fnormalize(a_bz, a_bz);
  Hacl_K256_Field_fnormalize(c_dz, c_dz);
  bool z = Hacl_K256_Field_is_felem_eq_vartime(a_bz, c_dz);
  return z;
}

bool Hacl_Impl_K256_Point_point_eq_vartime(uint64_t *p, uint64_t *q)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  uint64_t *qx = q;
  uint64_t *qy = q + (uint32_t)5U;
  uint64_t *qz = q + (uint32_t)10U;
  bool z0 = fmul_fmul_eq_vartime(px, qz, qx, pz);
  if (!z0)
  {
    return false;
  }
  return fmul_fmul_eq_vartime(py, qz, qy, pz);
}

bool Hacl_Impl_K256_Point_aff_point_decompress_vartime(uint64_t *x, uint64_t *y, uint8_t *s)
{
  uint8_t s0 = s[0U];
  if (!(s0 == (uint8_t)0x02U || s0 == (uint8_t)0x03U))
  {
    return false;
  }
  uint8_t *xb = s + (uint32_t)1U;
  bool is_x_valid = Hacl_K256_Field_load_felem_vartime(x, xb);
  bool is_y_odd = s0 == (uint8_t)0x03U;
  if (!is_x_valid)
  {
    return false;
  }
  uint64_t y2[5U] = { 0U };
  uint64_t b[5U] = { 0U };
  b[0U] = (uint64_t)0x7U;
  b[1U] = (uint64_t)0U;
  b[2U] = (uint64_t)0U;
  b[3U] = (uint64_t)0U;
  b[4U] = (uint64_t)0U;
  Hacl_K256_Field_fsqr(y2, x);
  Hacl_K256_Field_fmul(y2, y2, x);
  Hacl_K256_Field_fadd(y2, y2, b);
  Hacl_K256_Field_fnormalize(y2, y2);
  Hacl_Impl_K256_Finv_fsqrt(y, y2);
  Hacl_K256_Field_fnormalize(y, y);
  uint64_t y2_comp[5U] = { 0U };
  Hacl_K256_Field_fsqr(y2_comp, y);
  Hacl_K256_Field_fnormalize(y2_comp, y2_comp);
  bool res = Hacl_K256_Field_is_felem_eq_vartime(y2, y2_comp);
  bool is_y_valid = res;
  if (!is_y_valid)
  {
    return false;
  }
  uint64_t x0 = y[0U];
  bool is_y_odd1 = (x0 & (uint64_t)1U) == (uint64_t)1U;
  Hacl_K256_Field_fnegate_conditional_vartime(y, is_y_odd1 != is_y_odd);
  return true;
}

void Hacl_Impl_K256_Point_aff_point_compress_vartime(uint8_t *s, uint64_t *x, uint64_t *y)
{
  Hacl_K256_Field_fnormalize(y, y);
  Hacl_K256_Field_fnormalize(x, x);
  uint64_t x0 = y[0U];
  bool is_y_odd = (x0 & (uint64_t)1U) == (uint64_t)1U;
  uint8_t ite;
  if (is_y_odd)
  {
    ite = (uint8_t)0x03U;
  }
  else
  {
    ite = (uint8_t)0x02U;
  }
  s[0U] = ite;
  Hacl_K256_Field_store_felem(s + (uint32_t)1U, x);
}

void Hacl_Impl_K256_PointDouble_point_double(uint64_t *out, uint64_t *p)
{
  uint64_t tmp[25U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *yy = tmp;
  uint64_t *zz = tmp + (uint32_t)5U;
  uint64_t *bzz3 = tmp + (uint32_t)10U;
  uint64_t *bzz9 = tmp + (uint32_t)15U;
  uint64_t *tmp1 = tmp + (uint32_t)20U;
  Hacl_K256_Field_fsqr(yy, y1);
  Hacl_K256_Field_fsqr(zz, z1);
  Hacl_K256_Field_fmul_small_num(x3, x1, (uint64_t)2U);
  Hacl_K256_Field_fmul(x3, x3, y1);
  Hacl_K256_Field_fmul(tmp1, yy, y1);
  Hacl_K256_Field_fmul(z3, tmp1, z1);
  Hacl_K256_Field_fmul_small_num(z3, z3, (uint64_t)8U);
  Hacl_K256_Field_fnormalize_weak(z3, z3);
  Hacl_K256_Field_fmul_small_num(bzz3, zz, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(bzz3, bzz3);
  Hacl_K256_Field_fmul_small_num(bzz9, bzz3, (uint64_t)3U);
  Hacl_K256_Field_fsub(bzz9, yy, bzz9, (uint64_t)6U);
  Hacl_K256_Field_fadd(tmp1, yy, bzz3);
  Hacl_K256_Field_fmul(tmp1, bzz9, tmp1);
  Hacl_K256_Field_fmul(y3, yy, zz);
  Hacl_K256_Field_fmul(x3, x3, bzz9);
  Hacl_K256_Field_fmul_small_num(y3, y3, (uint64_t)168U);
  Hacl_K256_Field_fadd(y3, tmp1, y3);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
}

void Hacl_Impl_K256_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q)
{
  uint64_t tmp[45U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t *x2 = q;
  uint64_t *y2 = q + (uint32_t)5U;
  uint64_t *z2 = q + (uint32_t)10U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *xx = tmp;
  uint64_t *yy = tmp + (uint32_t)5U;
  uint64_t *zz = tmp + (uint32_t)10U;
  uint64_t *xy_pairs = tmp + (uint32_t)15U;
  uint64_t *yz_pairs = tmp + (uint32_t)20U;
  uint64_t *xz_pairs = tmp + (uint32_t)25U;
  uint64_t *yy_m_bzz3 = tmp + (uint32_t)30U;
  uint64_t *yy_p_bzz3 = tmp + (uint32_t)35U;
  uint64_t *tmp1 = tmp + (uint32_t)40U;
  Hacl_K256_Field_fmul(xx, x1, x2);
  Hacl_K256_Field_fmul(yy, y1, y2);
  Hacl_K256_Field_fmul(zz, z1, z2);
  Hacl_K256_Field_fadd(xy_pairs, x1, y1);
  Hacl_K256_Field_fadd(tmp1, x2, y2);
  Hacl_K256_Field_fmul(xy_pairs, xy_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, xx, yy);
  Hacl_K256_Field_fsub(xy_pairs, xy_pairs, tmp1, (uint64_t)4U);
  Hacl_K256_Field_fadd(yz_pairs, y1, z1);
  Hacl_K256_Field_fadd(tmp1, y2, z2);
  Hacl_K256_Field_fmul(yz_pairs, yz_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, yy, zz);
  Hacl_K256_Field_fsub(yz_pairs, yz_pairs, tmp1, (uint64_t)4U);
  Hacl_K256_Field_fadd(xz_pairs, x1, z1);
  Hacl_K256_Field_fadd(tmp1, x2, z2);
  Hacl_K256_Field_fmul(xz_pairs, xz_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, xx, zz);
  Hacl_K256_Field_fsub(xz_pairs, xz_pairs, tmp1, (uint64_t)4U);
  Hacl_K256_Field_fmul_small_num(tmp1, zz, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(tmp1, tmp1);
  Hacl_K256_Field_fsub(yy_m_bzz3, yy, tmp1, (uint64_t)2U);
  Hacl_K256_Field_fadd(yy_p_bzz3, yy, tmp1);
  Hacl_K256_Field_fmul_small_num(x3, yz_pairs, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(x3, x3);
  Hacl_K256_Field_fmul_small_num(z3, xx, (uint64_t)3U);
  Hacl_K256_Field_fmul_small_num(y3, z3, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
  Hacl_K256_Field_fmul(tmp1, xy_pairs, yy_m_bzz3);
  Hacl_K256_Field_fmul(x3, x3, xz_pairs);
  Hacl_K256_Field_fsub(x3, tmp1, x3, (uint64_t)2U);
  Hacl_K256_Field_fnormalize_weak(x3, x3);
  Hacl_K256_Field_fmul(tmp1, yy_p_bzz3, yy_m_bzz3);
  Hacl_K256_Field_fmul(y3, y3, xz_pairs);
  Hacl_K256_Field_fadd(y3, tmp1, y3);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
  Hacl_K256_Field_fmul(tmp1, yz_pairs, yy_p_bzz3);
  Hacl_K256_Field_fmul(z3, z3, xy_pairs);
  Hacl_K256_Field_fadd(z3, tmp1, z3);
  Hacl_K256_Field_fnormalize_weak(z3, z3);
}

static inline void scalar_split_lambda(uint64_t *r1, uint64_t *r2, uint64_t *k)
{
  uint64_t tmp1[4U] = { 0U };
  uint64_t tmp2[4U] = { 0U };
  tmp1[0U] = (uint64_t)0xe893209a45dbb031U;
  tmp1[1U] = (uint64_t)0x3daa8a1471e8ca7fU;
  tmp1[2U] = (uint64_t)0xe86c90e49284eb15U;
  tmp1[3U] = (uint64_t)0x3086d221a7d46bcdU;
  tmp2[0U] = (uint64_t)0x1571b4ae8ac47f71U;
  tmp2[1U] = (uint64_t)0x221208ac9df506c6U;
  tmp2[2U] = (uint64_t)0x6f547fa90abfe4c4U;
  tmp2[3U] = (uint64_t)0xe4437ed6010e8828U;
  qmul_shift_384(r1, k, tmp1);
  qmul_shift_384(r2, k, tmp2);
  tmp1[0U] = (uint64_t)0x6f547fa90abfe4c3U;
  tmp1[1U] = (uint64_t)0xe4437ed6010e8828U;
  tmp1[2U] = (uint64_t)0x0U;
  tmp1[3U] = (uint64_t)0x0U;
  tmp2[0U] = (uint64_t)0xd765cda83db1562cU;
  tmp2[1U] = (uint64_t)0x8a280ac50774346dU;
  tmp2[2U] = (uint64_t)0xfffffffffffffffeU;
  tmp2[3U] = (uint64_t)0xffffffffffffffffU;
  qmul(r1, r1, tmp1);
  qmul(r2, r2, tmp2);
  tmp1[0U] = (uint64_t)0xe0cfc810b51283cfU;
  tmp1[1U] = (uint64_t)0xa880b9fc8ec739c2U;
  tmp1[2U] = (uint64_t)0x5ad9e3fd77ed9ba4U;
  tmp1[3U] = (uint64_t)0xac9c52b33fa3cf1fU;
  qadd(r2, r1, r2);
  qmul(tmp2, r2, tmp1);
  qadd(r1, k, tmp2);
}

static inline void point_mul_lambda(uint64_t *res, uint64_t *p)
{
  uint64_t *rx = res;
  uint64_t *ry = res + (uint32_t)5U;
  uint64_t *rz = res + (uint32_t)10U;
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  uint64_t beta[5U] = { 0U };
  beta[0U] = (uint64_t)0x96c28719501eeU;
  beta[1U] = (uint64_t)0x7512f58995c13U;
  beta[2U] = (uint64_t)0xc3434e99cf049U;
  beta[3U] = (uint64_t)0x7106e64479eaU;
  beta[4U] = (uint64_t)0x7ae96a2b657cU;
  Hacl_K256_Field_fmul(rx, beta, px);
  ry[0U] = py[0U];
  ry[1U] = py[1U];
  ry[2U] = py[2U];
  ry[3U] = py[3U];
  ry[4U] = py[4U];
  rz[0U] = pz[0U];
  rz[1U] = pz[1U];
  rz[2U] = pz[2U];
  rz[3U] = pz[3U];
  rz[4U] = pz[4U];
}

static inline void point_mul_lambda_inplace(uint64_t *res)
{
  uint64_t *rx = res;
  uint64_t beta[5U] = { 0U };
  beta[0U] = (uint64_t)0x96c28719501eeU;
  beta[1U] = (uint64_t)0x7512f58995c13U;
  beta[2U] = (uint64_t)0xc3434e99cf049U;
  beta[3U] = (uint64_t)0x7106e64479eaU;
  beta[4U] = (uint64_t)0x7ae96a2b657cU;
  Hacl_K256_Field_fmul(rx, beta, rx);
}

typedef struct __bool_bool_s
{
  bool fst;
  bool snd;
}
__bool_bool;

static inline __bool_bool
ecmult_endo_split(
  uint64_t *r1,
  uint64_t *r2,
  uint64_t *q1,
  uint64_t *q2,
  uint64_t *scalar,
  uint64_t *q
)
{
  scalar_split_lambda(r1, r2, scalar);
  point_mul_lambda(q2, q);
  memcpy(q1, q, (uint32_t)15U * sizeof (uint64_t));
  bool b0 = is_qelem_le_q_halved_vartime(r1);
  qnegate_conditional_vartime(r1, !b0);
  point_negate_conditional_vartime(q1, !b0);
  bool is_high1 = !b0;
  bool b = is_qelem_le_q_halved_vartime(r2);
  qnegate_conditional_vartime(r2, !b);
  point_negate_conditional_vartime(q2, !b);
  bool is_high2 = !b;
  return ((__bool_bool){ .fst = is_high1, .snd = is_high2 });
}

void Hacl_Impl_K256_PointMul_point_mul(uint64_t *out, uint64_t *scalar, uint64_t *q)
{
  uint64_t table[240U] = { 0U };
  uint64_t tmp[15U] = { 0U };
  uint64_t *t0 = table;
  uint64_t *t1 = table + (uint32_t)15U;
  Hacl_Impl_K256_Point_make_point_at_inf(t0);
  memcpy(t1, q, (uint32_t)15U * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    (uint32_t)0U,
    (uint32_t)7U,
    (uint32_t)1U,
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)15U;
    Hacl_Impl_K256_PointDouble_point_double(tmp, t11);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)15U,
      tmp,
      (uint32_t)15U * sizeof (uint64_t));
    uint64_t *t2 = table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)15U;
    Hacl_Impl_K256_PointAdd_point_add(tmp, q, t2);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)15U,
      tmp,
      (uint32_t)15U * sizeof (uint64_t)););
  Hacl_Impl_K256_Point_make_point_at_inf(out);
  uint64_t tmp0[15U] = { 0U };
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t bk = (uint32_t)256U;
    uint64_t mask_l = (uint64_t)15U;
    uint32_t i1 = (bk - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bk - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = scalar[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | scalar[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    memcpy(tmp0, (uint64_t *)table, (uint32_t)15U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i2,
      (uint32_t)0U,
      (uint32_t)15U,
      (uint32_t)1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      const uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)15U;
      KRML_MAYBE_FOR15(i,
        (uint32_t)0U,
        (uint32_t)15U,
        (uint32_t)1U,
        uint64_t *os = tmp0;
        uint64_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;););
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp0);
  }
}

static inline void precomp_get_consttime(const uint64_t *table, uint64_t bits_l, uint64_t *tmp)
{
  memcpy(tmp, (uint64_t *)table, (uint32_t)15U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i0,
    (uint32_t)0U,
    (uint32_t)15U,
    (uint32_t)1U,
    uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i0 + (uint32_t)1U));
    const uint64_t *res_j = table + (i0 + (uint32_t)1U) * (uint32_t)15U;
    KRML_MAYBE_FOR15(i,
      (uint32_t)0U,
      (uint32_t)15U,
      (uint32_t)1U,
      uint64_t *os = tmp;
      uint64_t x = (c & res_j[i]) | (~c & tmp[i]);
      os[i] = x;););
}

static inline void point_mul_g(uint64_t *out, uint64_t *scalar)
{
  uint64_t q1[15U] = { 0U };
  uint64_t *gx = q1;
  uint64_t *gy = q1 + (uint32_t)5U;
  uint64_t *gz = q1 + (uint32_t)10U;
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
  uint64_t
  q2[15U] =
    {
      (uint64_t)4496295042185355U, (uint64_t)3125448202219451U, (uint64_t)1239608518490046U,
      (uint64_t)2687445637493112U, (uint64_t)77979604880139U, (uint64_t)3360310474215011U,
      (uint64_t)1216410458165163U, (uint64_t)177901593587973U, (uint64_t)3209978938104985U,
      (uint64_t)118285133003718U, (uint64_t)434519962075150U, (uint64_t)1114612377498854U,
      (uint64_t)3488596944003813U, (uint64_t)450716531072892U, (uint64_t)66044973203836U
    };
  uint64_t
  q3[15U] =
    {
      (uint64_t)1277614565900951U, (uint64_t)378671684419493U, (uint64_t)3176260448102880U,
      (uint64_t)1575691435565077U, (uint64_t)167304528382180U, (uint64_t)2600787765776588U,
      (uint64_t)7497946149293U, (uint64_t)2184272641272202U, (uint64_t)2200235265236628U,
      (uint64_t)265969268774814U, (uint64_t)1913228635640715U, (uint64_t)2831959046949342U,
      (uint64_t)888030405442963U, (uint64_t)1817092932985033U, (uint64_t)101515844997121U
    };
  uint64_t
  q4[15U] =
    {
      (uint64_t)34056422761564U, (uint64_t)3315864838337811U, (uint64_t)3797032336888745U,
      (uint64_t)2580641850480806U, (uint64_t)208048944042500U, (uint64_t)1233795288689421U,
      (uint64_t)1048795233382631U, (uint64_t)646545158071530U, (uint64_t)1816025742137285U,
      (uint64_t)12245672982162U, (uint64_t)2119364213800870U, (uint64_t)2034960311715107U,
      (uint64_t)3172697815804487U, (uint64_t)4185144850224160U, (uint64_t)2792055915674U
    };
  uint64_t *r1 = scalar;
  uint64_t *r2 = scalar + (uint32_t)1U;
  uint64_t *r3 = scalar + (uint32_t)2U;
  uint64_t *r4 = scalar + (uint32_t)3U;
  Hacl_Impl_K256_Point_make_point_at_inf(out);
  uint64_t tmp[15U] = { 0U };
  KRML_MAYBE_FOR16(i,
    (uint32_t)0U,
    (uint32_t)16U,
    (uint32_t)1U,
    KRML_MAYBE_FOR4(i0,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t bk = (uint32_t)64U;
    uint64_t mask_l0 = (uint64_t)15U;
    uint32_t i10 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j0 = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p10 = r4[i10] >> j0;
    uint64_t ite0;
    if (i10 + (uint32_t)1U < (uint32_t)1U && (uint32_t)0U < j0)
    {
      ite0 = p10 | r4[i10 + (uint32_t)1U] << ((uint32_t)64U - j0);
    }
    else
    {
      ite0 = p10;
    }
    uint64_t bits_l = ite0 & mask_l0;
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4, bits_l, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp);
    uint32_t bk0 = (uint32_t)64U;
    uint64_t mask_l1 = (uint64_t)15U;
    uint32_t i11 = (bk0 - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j1 = (bk0 - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p11 = r3[i11] >> j1;
    uint64_t ite1;
    if (i11 + (uint32_t)1U < (uint32_t)1U && (uint32_t)0U < j1)
    {
      ite1 = p11 | r3[i11 + (uint32_t)1U] << ((uint32_t)64U - j1);
    }
    else
    {
      ite1 = p11;
    }
    uint64_t bits_l0 = ite1 & mask_l1;
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4, bits_l0, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp);
    uint32_t bk1 = (uint32_t)64U;
    uint64_t mask_l2 = (uint64_t)15U;
    uint32_t i12 = (bk1 - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j2 = (bk1 - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p12 = r2[i12] >> j2;
    uint64_t ite2;
    if (i12 + (uint32_t)1U < (uint32_t)1U && (uint32_t)0U < j2)
    {
      ite2 = p12 | r2[i12 + (uint32_t)1U] << ((uint32_t)64U - j2);
    }
    else
    {
      ite2 = p12;
    }
    uint64_t bits_l1 = ite2 & mask_l2;
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4, bits_l1, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp);
    uint32_t bk2 = (uint32_t)64U;
    uint64_t mask_l = (uint64_t)15U;
    uint32_t i1 = (bk2 - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bk2 - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = r1[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)1U && (uint32_t)0U < j)
    {
      ite = p1 | r1[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l2 = ite & mask_l;
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_basepoint_table_w4, bits_l2, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp););
}

static inline void
point_mul_g_double_vartime(uint64_t *out, uint64_t *scalar1, uint64_t *scalar2, uint64_t *q2)
{
  uint64_t q1[15U] = { 0U };
  uint64_t *gx = q1;
  uint64_t *gy = q1 + (uint32_t)5U;
  uint64_t *gz = q1 + (uint32_t)10U;
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
  uint64_t table2[480U] = { 0U };
  uint64_t tmp[15U] = { 0U };
  uint64_t *t0 = table2;
  uint64_t *t1 = table2 + (uint32_t)15U;
  Hacl_Impl_K256_Point_make_point_at_inf(t0);
  memcpy(t1, q2, (uint32_t)15U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    (uint32_t)0U,
    (uint32_t)15U,
    (uint32_t)1U,
    uint64_t *t11 = table2 + (i + (uint32_t)1U) * (uint32_t)15U;
    Hacl_Impl_K256_PointDouble_point_double(tmp, t11);
    memcpy(table2 + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)15U,
      tmp,
      (uint32_t)15U * sizeof (uint64_t));
    uint64_t *t2 = table2 + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)15U;
    Hacl_Impl_K256_PointAdd_point_add(tmp, q2, t2);
    memcpy(table2 + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)15U,
      tmp,
      (uint32_t)15U * sizeof (uint64_t)););
  uint64_t tmp0[15U] = { 0U };
  uint64_t mask_l0 = (uint64_t)31U;
  uint32_t i0 = (uint32_t)3U;
  uint32_t j0 = (uint32_t)63U;
  uint64_t p10 = scalar1[i0] >> j0;
  uint64_t ite0;
  if (i0 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
  {
    ite0 = p10 | scalar1[i0 + (uint32_t)1U] << ((uint32_t)64U - j0);
  }
  else
  {
    ite0 = p10;
  }
  uint64_t bits_c = ite0 & mask_l0;
  uint32_t bits_l32 = (uint32_t)bits_c;
  const
  uint64_t
  *a_bits_l = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l32 * (uint32_t)15U;
  memcpy(out, (uint64_t *)a_bits_l, (uint32_t)15U * sizeof (uint64_t));
  uint64_t mask_l1 = (uint64_t)31U;
  uint32_t i2 = (uint32_t)3U;
  uint32_t j1 = (uint32_t)63U;
  uint64_t p11 = scalar2[i2] >> j1;
  uint64_t ite1;
  if (i2 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j1)
  {
    ite1 = p11 | scalar2[i2 + (uint32_t)1U] << ((uint32_t)64U - j1);
  }
  else
  {
    ite1 = p11;
  }
  uint64_t bits_c0 = ite1 & mask_l1;
  uint32_t bits_l320 = (uint32_t)bits_c0;
  const uint64_t *a_bits_l0 = table2 + bits_l320 * (uint32_t)15U;
  memcpy(tmp0, (uint64_t *)a_bits_l0, (uint32_t)15U * sizeof (uint64_t));
  Hacl_Impl_K256_PointAdd_point_add(out, out, tmp0);
  uint64_t tmp1[15U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)51U; i++)
  {
    KRML_MAYBE_FOR5(i1,
      (uint32_t)0U,
      (uint32_t)5U,
      (uint32_t)1U,
      Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t bk = (uint32_t)255U;
    uint64_t mask_l2 = (uint64_t)31U;
    uint32_t i10 = (bk - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j2 = (bk - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p12 = scalar2[i10] >> j2;
    uint64_t ite2;
    if (i10 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j2)
    {
      ite2 = p12 | scalar2[i10 + (uint32_t)1U] << ((uint32_t)64U - j2);
    }
    else
    {
      ite2 = p12;
    }
    uint64_t bits_l = ite2 & mask_l2;
    uint32_t bits_l321 = (uint32_t)bits_l;
    const uint64_t *a_bits_l1 = table2 + bits_l321 * (uint32_t)15U;
    memcpy(tmp1, (uint64_t *)a_bits_l1, (uint32_t)15U * sizeof (uint64_t));
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp1);
    uint32_t bk0 = (uint32_t)255U;
    uint64_t mask_l = (uint64_t)31U;
    uint32_t i1 = (bk0 - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j = (bk0 - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p1 = scalar1[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | scalar1[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l0 = ite & mask_l;
    uint32_t bits_l322 = (uint32_t)bits_l0;
    const
    uint64_t
    *a_bits_l2 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l322 * (uint32_t)15U;
    memcpy(tmp1, (uint64_t *)a_bits_l2, (uint32_t)15U * sizeof (uint64_t));
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp1);
  }
}

static inline void
point_mul_g_double_split_lambda_table(
  uint64_t *out,
  uint64_t *r1,
  uint64_t *r2,
  uint64_t *r3,
  uint64_t *r4,
  uint64_t *p2,
  bool is_negate1,
  bool is_negate2,
  bool is_negate3,
  bool is_negate4
)
{
  uint64_t table2[480U] = { 0U };
  uint64_t tmp[15U] = { 0U };
  uint64_t *t0 = table2;
  uint64_t *t1 = table2 + (uint32_t)15U;
  Hacl_Impl_K256_Point_make_point_at_inf(t0);
  memcpy(t1, p2, (uint32_t)15U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    (uint32_t)0U,
    (uint32_t)15U,
    (uint32_t)1U,
    uint64_t *t11 = table2 + (i + (uint32_t)1U) * (uint32_t)15U;
    Hacl_Impl_K256_PointDouble_point_double(tmp, t11);
    memcpy(table2 + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)15U,
      tmp,
      (uint32_t)15U * sizeof (uint64_t));
    uint64_t *t2 = table2 + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)15U;
    Hacl_Impl_K256_PointAdd_point_add(tmp, p2, t2);
    memcpy(table2 + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)15U,
      tmp,
      (uint32_t)15U * sizeof (uint64_t)););
  uint64_t tmp0[15U] = { 0U };
  uint64_t tmp1[15U] = { 0U };
  uint64_t mask_l0 = (uint64_t)31U;
  uint32_t i0 = (uint32_t)1U;
  uint32_t j0 = (uint32_t)61U;
  uint64_t p110 = r1[i0] >> j0;
  uint64_t ite0;
  if (i0 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
  {
    ite0 = p110 | r1[i0 + (uint32_t)1U] << ((uint32_t)64U - j0);
  }
  else
  {
    ite0 = p110;
  }
  uint64_t bits_c = ite0 & mask_l0;
  uint32_t bits_l32 = (uint32_t)bits_c;
  const
  uint64_t
  *a_bits_l = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l32 * (uint32_t)15U;
  memcpy(out, (uint64_t *)a_bits_l, (uint32_t)15U * sizeof (uint64_t));
  point_negate_conditional_vartime(out, is_negate1);
  uint64_t mask_l1 = (uint64_t)31U;
  uint32_t i2 = (uint32_t)1U;
  uint32_t j1 = (uint32_t)61U;
  uint64_t p111 = r2[i2] >> j1;
  uint64_t ite1;
  if (i2 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j1)
  {
    ite1 = p111 | r2[i2 + (uint32_t)1U] << ((uint32_t)64U - j1);
  }
  else
  {
    ite1 = p111;
  }
  uint64_t bits_c0 = ite1 & mask_l1;
  uint32_t bits_l320 = (uint32_t)bits_c0;
  const
  uint64_t
  *a_bits_l0 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l320 * (uint32_t)15U;
  memcpy(tmp1, (uint64_t *)a_bits_l0, (uint32_t)15U * sizeof (uint64_t));
  point_negate_conditional_vartime(tmp1, is_negate2);
  point_mul_lambda_inplace(tmp1);
  Hacl_Impl_K256_PointAdd_point_add(out, out, tmp1);
  uint64_t tmp10[15U] = { 0U };
  uint64_t mask_l2 = (uint64_t)31U;
  uint32_t i3 = (uint32_t)1U;
  uint32_t j2 = (uint32_t)61U;
  uint64_t p112 = r3[i3] >> j2;
  uint64_t ite2;
  if (i3 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j2)
  {
    ite2 = p112 | r3[i3 + (uint32_t)1U] << ((uint32_t)64U - j2);
  }
  else
  {
    ite2 = p112;
  }
  uint64_t bits_c1 = ite2 & mask_l2;
  uint32_t bits_l321 = (uint32_t)bits_c1;
  const uint64_t *a_bits_l1 = table2 + bits_l321 * (uint32_t)15U;
  memcpy(tmp0, (uint64_t *)a_bits_l1, (uint32_t)15U * sizeof (uint64_t));
  point_negate_conditional_vartime(tmp0, is_negate3);
  uint64_t mask_l3 = (uint64_t)31U;
  uint32_t i4 = (uint32_t)1U;
  uint32_t j3 = (uint32_t)61U;
  uint64_t p113 = r4[i4] >> j3;
  uint64_t ite3;
  if (i4 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j3)
  {
    ite3 = p113 | r4[i4 + (uint32_t)1U] << ((uint32_t)64U - j3);
  }
  else
  {
    ite3 = p113;
  }
  uint64_t bits_c2 = ite3 & mask_l3;
  uint32_t bits_l322 = (uint32_t)bits_c2;
  const uint64_t *a_bits_l2 = table2 + bits_l322 * (uint32_t)15U;
  memcpy(tmp10, (uint64_t *)a_bits_l2, (uint32_t)15U * sizeof (uint64_t));
  point_negate_conditional_vartime(tmp10, is_negate4);
  point_mul_lambda_inplace(tmp10);
  Hacl_Impl_K256_PointAdd_point_add(tmp0, tmp0, tmp10);
  Hacl_Impl_K256_PointAdd_point_add(out, out, tmp0);
  uint64_t tmp2[15U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)25U; i++)
  {
    KRML_MAYBE_FOR5(i1,
      (uint32_t)0U,
      (uint32_t)5U,
      (uint32_t)1U,
      Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t bk = (uint32_t)125U;
    uint64_t mask_l4 = (uint64_t)31U;
    uint32_t i10 = (bk - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j4 = (bk - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p114 = r4[i10] >> j4;
    uint64_t ite4;
    if (i10 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j4)
    {
      ite4 = p114 | r4[i10 + (uint32_t)1U] << ((uint32_t)64U - j4);
    }
    else
    {
      ite4 = p114;
    }
    uint64_t bits_l = ite4 & mask_l4;
    uint32_t bits_l323 = (uint32_t)bits_l;
    const uint64_t *a_bits_l3 = table2 + bits_l323 * (uint32_t)15U;
    memcpy(tmp2, (uint64_t *)a_bits_l3, (uint32_t)15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate4);
    point_mul_lambda_inplace(tmp2);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
    uint32_t bk0 = (uint32_t)125U;
    uint64_t mask_l5 = (uint64_t)31U;
    uint32_t i11 = (bk0 - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j5 = (bk0 - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p115 = r3[i11] >> j5;
    uint64_t ite5;
    if (i11 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j5)
    {
      ite5 = p115 | r3[i11 + (uint32_t)1U] << ((uint32_t)64U - j5);
    }
    else
    {
      ite5 = p115;
    }
    uint64_t bits_l0 = ite5 & mask_l5;
    uint32_t bits_l324 = (uint32_t)bits_l0;
    const uint64_t *a_bits_l4 = table2 + bits_l324 * (uint32_t)15U;
    memcpy(tmp2, (uint64_t *)a_bits_l4, (uint32_t)15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate3);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
    uint32_t bk1 = (uint32_t)125U;
    uint64_t mask_l6 = (uint64_t)31U;
    uint32_t i12 = (bk1 - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j6 = (bk1 - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p116 = r2[i12] >> j6;
    uint64_t ite6;
    if (i12 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j6)
    {
      ite6 = p116 | r2[i12 + (uint32_t)1U] << ((uint32_t)64U - j6);
    }
    else
    {
      ite6 = p116;
    }
    uint64_t bits_l1 = ite6 & mask_l6;
    uint32_t bits_l325 = (uint32_t)bits_l1;
    const
    uint64_t
    *a_bits_l5 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l325 * (uint32_t)15U;
    memcpy(tmp2, (uint64_t *)a_bits_l5, (uint32_t)15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate2);
    point_mul_lambda_inplace(tmp2);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
    uint32_t bk2 = (uint32_t)125U;
    uint64_t mask_l = (uint64_t)31U;
    uint32_t i1 = (bk2 - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j = (bk2 - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p11 = r1[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p11 | r1[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p11;
    }
    uint64_t bits_l2 = ite & mask_l;
    uint32_t bits_l326 = (uint32_t)bits_l2;
    const
    uint64_t
    *a_bits_l6 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l326 * (uint32_t)15U;
    memcpy(tmp2, (uint64_t *)a_bits_l6, (uint32_t)15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate1);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
  }
}

static inline bool
check_ecmult_endo_split(uint64_t *r1, uint64_t *r2, uint64_t *r3, uint64_t *r4)
{
  uint64_t f20 = r1[2U];
  uint64_t f30 = r1[3U];
  bool b1 = f20 == (uint64_t)0U && f30 == (uint64_t)0U;
  uint64_t f21 = r2[2U];
  uint64_t f31 = r2[3U];
  bool b2 = f21 == (uint64_t)0U && f31 == (uint64_t)0U;
  uint64_t f22 = r3[2U];
  uint64_t f32 = r3[3U];
  bool b3 = f22 == (uint64_t)0U && f32 == (uint64_t)0U;
  uint64_t f2 = r4[2U];
  uint64_t f3 = r4[3U];
  bool b4 = f2 == (uint64_t)0U && f3 == (uint64_t)0U;
  return b1 && b2 && b3 && b4;
}

typedef struct __bool_bool_bool_bool_s
{
  bool fst;
  bool snd;
  bool thd;
  bool f3;
}
__bool_bool_bool_bool;

static inline void
point_mul_g_double_split_lambda_vartime(
  uint64_t *out,
  uint64_t *scalar1,
  uint64_t *scalar2,
  uint64_t *p2
)
{
  uint64_t g[15U] = { 0U };
  uint64_t *gx = g;
  uint64_t *gy = g + (uint32_t)5U;
  uint64_t *gz = g + (uint32_t)10U;
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
  uint64_t r1234[16U] = { 0U };
  uint64_t q1234[60U] = { 0U };
  uint64_t *r1 = r1234;
  uint64_t *r2 = r1234 + (uint32_t)4U;
  uint64_t *r3 = r1234 + (uint32_t)8U;
  uint64_t *r4 = r1234 + (uint32_t)12U;
  uint64_t *q1 = q1234;
  uint64_t *q2 = q1234 + (uint32_t)15U;
  uint64_t *q3 = q1234 + (uint32_t)30U;
  uint64_t *q4 = q1234 + (uint32_t)45U;
  __bool_bool scrut0 = ecmult_endo_split(r1, r2, q1, q2, scalar1, g);
  bool is_high10 = scrut0.fst;
  bool is_high20 = scrut0.snd;
  __bool_bool scrut = ecmult_endo_split(r3, r4, q3, q4, scalar2, p2);
  bool is_high30 = scrut.fst;
  bool is_high40 = scrut.snd;
  __bool_bool_bool_bool
  scrut1 = { .fst = is_high10, .snd = is_high20, .thd = is_high30, .f3 = is_high40 };
  bool is_high1 = scrut1.fst;
  bool is_high2 = scrut1.snd;
  bool is_high3 = scrut1.thd;
  bool is_high4 = scrut1.f3;
  bool is_r1234_valid = check_ecmult_endo_split(r1, r2, r3, r4);
  if (is_r1234_valid)
  {
    point_mul_g_double_split_lambda_table(out,
      r1,
      r2,
      r3,
      r4,
      p2,
      is_high1,
      is_high2,
      is_high3,
      is_high4);
  }
  else
  {
    point_mul_g_double_vartime(out, scalar1, scalar2, p2);
  }
}

static inline bool load_public_key(uint8_t *pk, uint64_t *fpk_x, uint64_t *fpk_y)
{
  uint8_t *pk_x = pk;
  uint8_t *pk_y = pk + (uint32_t)32U;
  bool is_x_valid = Hacl_K256_Field_load_felem_vartime(fpk_x, pk_x);
  bool is_y_valid = Hacl_K256_Field_load_felem_vartime(fpk_y, pk_y);
  if (is_x_valid && is_y_valid)
  {
    uint64_t y2_exp[5U] = { 0U };
    uint64_t b[5U] = { 0U };
    b[0U] = (uint64_t)0x7U;
    b[1U] = (uint64_t)0U;
    b[2U] = (uint64_t)0U;
    b[3U] = (uint64_t)0U;
    b[4U] = (uint64_t)0U;
    Hacl_K256_Field_fsqr(y2_exp, fpk_x);
    Hacl_K256_Field_fmul(y2_exp, y2_exp, fpk_x);
    Hacl_K256_Field_fadd(y2_exp, y2_exp, b);
    Hacl_K256_Field_fnormalize(y2_exp, y2_exp);
    uint64_t y2_comp[5U] = { 0U };
    Hacl_K256_Field_fsqr(y2_comp, fpk_y);
    Hacl_K256_Field_fnormalize(y2_comp, y2_comp);
    bool res = Hacl_K256_Field_is_felem_eq_vartime(y2_exp, y2_comp);
    bool res0 = res;
    return res0;
  }
  return false;
}

static inline bool fmul_eq_vartime(uint64_t *r, uint64_t *z, uint64_t *x)
{
  uint64_t tmp[5U] = { 0U };
  Hacl_K256_Field_fmul(tmp, r, z);
  Hacl_K256_Field_fnormalize(tmp, tmp);
  bool b = Hacl_K256_Field_is_felem_eq_vartime(tmp, x);
  return b;
}

/*******************************************************************************
  Verified C library for ECDSA signing and verification on the secp256k1 curve.

  For the comments on low-S normalization (or canonical lowest S value), see:
    • https://en.bitcoin.it/wiki/BIP_0062
    • https://yondon.blog/2019/01/01/how-not-to-use-ecdsa/
    • https://eklitzke.org/bitcoin-transaction-malleability

  For example, bitcoin-core/secp256k1 *always* performs low-S normalization.

*******************************************************************************/


/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` and `private_key` < the order of the curve
    • 0 < `nonce` and `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t oneq[4U] = { (uint64_t)0x1U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U };
  uint64_t rsdk_q[16U] = { 0U };
  uint64_t *r_q = rsdk_q;
  uint64_t *s_q = rsdk_q + (uint32_t)4U;
  uint64_t *d_a = rsdk_q + (uint32_t)8U;
  uint64_t *k_q = rsdk_q + (uint32_t)12U;
  uint64_t is_sk_valid = load_qelem_check(d_a, private_key);
  uint64_t is_nonce_valid = load_qelem_check(k_q, nonce);
  uint64_t are_sk_nonce_valid = is_sk_valid & is_nonce_valid;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = d_a;
    uint64_t uu____0 = oneq[i];
    uint64_t x = uu____0 ^ (are_sk_nonce_valid & (d_a[i] ^ uu____0));
    os[i] = x;);
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = k_q;
    uint64_t uu____1 = oneq[i];
    uint64_t x = uu____1 ^ (are_sk_nonce_valid & (k_q[i] ^ uu____1));
    os[i] = x;);
  uint64_t tmp[5U] = { 0U };
  uint8_t x_bytes[32U] = { 0U };
  uint64_t p[15U] = { 0U };
  point_mul_g(p, k_q);
  uint64_t *x = p;
  uint64_t *z = p + (uint32_t)10U;
  Hacl_Impl_K256_Finv_finv(tmp, z);
  Hacl_K256_Field_fmul(tmp, x, tmp);
  Hacl_K256_Field_fnormalize(tmp, tmp);
  Hacl_K256_Field_store_felem(x_bytes, tmp);
  load_qelem_modq(r_q, x_bytes);
  uint64_t z0[4U] = { 0U };
  uint64_t kinv[4U] = { 0U };
  load_qelem_modq(z0, msgHash);
  qinv(kinv, k_q);
  qmul(s_q, r_q, d_a);
  qadd(s_q, z0, s_q);
  qmul(s_q, kinv, s_q);
  store_qelem(signature, r_q);
  store_qelem(signature + (uint32_t)32U, s_q);
  uint64_t is_r_zero = is_qelem_zero(r_q);
  uint64_t is_s_zero = is_qelem_zero(s_q);
  uint64_t m = are_sk_nonce_valid & (~is_r_zero & ~is_s_zero);
  bool res = m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  return res;
}

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_sign_hashed_msg`.

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint8_t msgHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, msgHash);
  bool b = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  return b;
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether a public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(uint8_t *m, uint8_t *public_key, uint8_t *signature)
{
  uint64_t pk_x[5U] = { 0U };
  uint64_t pk_y[5U] = { 0U };
  uint64_t r_q[4U] = { 0U };
  uint64_t s_q[4U] = { 0U };
  uint64_t z[4U] = { 0U };
  bool is_xy_on_curve = load_public_key(public_key, pk_x, pk_y);
  bool is_r_valid = load_qelem_vartime(r_q, signature);
  bool is_s_valid = load_qelem_vartime(s_q, signature + (uint32_t)32U);
  load_qelem_modq(z, m);
  if (!(is_xy_on_curve && is_r_valid && is_s_valid))
  {
    return false;
  }
  uint64_t p[15U] = { 0U };
  uint64_t res[15U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z10 = p + (uint32_t)10U;
  memcpy(x1, pk_x, (uint32_t)5U * sizeof (uint64_t));
  memcpy(y1, pk_y, (uint32_t)5U * sizeof (uint64_t));
  memset(z10, 0U, (uint32_t)5U * sizeof (uint64_t));
  z10[0U] = (uint64_t)1U;
  uint64_t sinv1[4U] = { 0U };
  uint64_t u11[4U] = { 0U };
  uint64_t u21[4U] = { 0U };
  qinv(sinv1, s_q);
  qmul(u11, z, sinv1);
  qmul(u21, r_q, sinv1);
  point_mul_g_double_split_lambda_vartime(res, u11, u21, p);
  uint64_t tmp[5U] = { 0U };
  uint64_t *pz = res + (uint32_t)10U;
  Hacl_K256_Field_fnormalize(tmp, pz);
  bool b = Hacl_K256_Field_is_felem_zero_vartime(tmp);
  if (b)
  {
    return false;
  }
  uint64_t *x = res;
  uint64_t *z1 = res + (uint32_t)10U;
  uint8_t r_bytes[32U] = { 0U };
  uint64_t r_fe[5U] = { 0U };
  uint64_t tmp_q[5U] = { 0U };
  uint64_t tmp_x[5U] = { 0U };
  store_qelem(r_bytes, r_q);
  Hacl_K256_Field_load_felem(r_fe, r_bytes);
  Hacl_K256_Field_fnormalize(tmp_x, x);
  bool is_rz_x = fmul_eq_vartime(r_fe, z1, tmp_x);
  if (!is_rz_x)
  {
    bool is_r_lt_p_m_q = Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime(r_fe);
    if (is_r_lt_p_m_q)
    {
      tmp_q[0U] = (uint64_t)0x25e8cd0364141U;
      tmp_q[1U] = (uint64_t)0xe6af48a03bbfdU;
      tmp_q[2U] = (uint64_t)0xffffffebaaedcU;
      tmp_q[3U] = (uint64_t)0xfffffffffffffU;
      tmp_q[4U] = (uint64_t)0xffffffffffffU;
      Hacl_K256_Field_fadd(tmp_q, r_fe, tmp_q);
      return fmul_eq_vartime(tmp_q, z1, tmp_x);
    }
    return false;
  }
  return true;
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_verify_hashed_msg`.

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
)
{
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  bool b = Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(mHash, public_key, signature);
  return b;
}

/**
Compute canonical lowest S value for `signature` (R || S).

  The function returns `true` for successful normalization of S and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(uint8_t *signature)
{
  uint64_t s_q[4U] = { 0U };
  uint8_t *s = signature + (uint32_t)32U;
  bool is_sk_valid = load_qelem_vartime(s_q, s);
  if (!is_sk_valid)
  {
    return false;
  }
  bool is_sk_lt_q_halved = is_qelem_le_q_halved_vartime(s_q);
  qnegate_conditional_vartime(s_q, !is_sk_lt_q_halved);
  store_qelem(signature + (uint32_t)32U, s_q);
  return true;
}

/**
Check whether `signature` (R || S) is in canonical form.

  The function returns `true` if S is low-S normalized and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(uint8_t *signature)
{
  uint64_t s_q[4U] = { 0U };
  uint8_t *s = signature + (uint32_t)32U;
  bool is_s_valid = load_qelem_vartime(s_q, s);
  bool is_s_lt_q_halved = is_qelem_le_q_halved_vartime(s_q);
  return is_s_valid && is_s_lt_q_halved;
}

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` and `private_key` < the order of the curve
    • 0 < `nonce` and `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  bool b = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  if (b)
  {
    return Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(signature);
  }
  return false;
}

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_sign_hashed_msg`.

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint8_t msgHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, msgHash);
  bool
  b = Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  return b;
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_hashed_msg` if needed.

  The function also checks whether a public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
  uint8_t *msgHash,
  uint8_t *public_key,
  uint8_t *signature
)
{
  bool is_s_normalized = Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(signature);
  if (!is_s_normalized)
  {
    return false;
  }
  return Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(msgHash, public_key, signature);
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_verify_hashed_msg`.

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
)
{
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  bool b = Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(mHash, public_key, signature);
  return b;
}

/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the secp256k1 curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/


/**
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is valid point.
*/
bool Hacl_K256_ECDSA_public_key_uncompressed_to_raw(uint8_t *pk_raw, uint8_t *pk)
{
  uint8_t pk0 = pk[0U];
  if (pk0 != (uint8_t)0x04U)
  {
    return false;
  }
  memcpy(pk_raw, pk + (uint32_t)1U, (uint32_t)64U * sizeof (uint8_t));
  return true;
}

/**
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
void Hacl_K256_ECDSA_public_key_uncompressed_from_raw(uint8_t *pk, uint8_t *pk_raw)
{
  pk[0U] = (uint8_t)0x04U;
  memcpy(pk + (uint32_t)1U, pk_raw, (uint32_t)64U * sizeof (uint8_t));
}

/**
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is valid point.
*/
bool Hacl_K256_ECDSA_public_key_compressed_to_raw(uint8_t *pk_raw, uint8_t *pk)
{
  uint64_t xa[5U] = { 0U };
  uint64_t ya[5U] = { 0U };
  uint8_t *pk_xb = pk + (uint32_t)1U;
  bool b = Hacl_Impl_K256_Point_aff_point_decompress_vartime(xa, ya, pk);
  if (b)
  {
    memcpy(pk_raw, pk_xb, (uint32_t)32U * sizeof (uint8_t));
    Hacl_K256_Field_store_felem(pk_raw + (uint32_t)32U, ya);
  }
  return b;
}

/**
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
void Hacl_K256_ECDSA_public_key_compressed_from_raw(uint8_t *pk, uint8_t *pk_raw)
{
  uint8_t *pk_x = pk_raw;
  uint8_t *pk_y = pk_raw + (uint32_t)32U;
  uint8_t x0 = pk_y[31U];
  bool is_pk_y_odd = (x0 & (uint8_t)1U) == (uint8_t)1U;
  uint8_t ite;
  if (is_pk_y_odd)
  {
    ite = (uint8_t)0x03U;
  }
  else
  {
    ite = (uint8_t)0x02U;
  }
  pk[0U] = ite;
  memcpy(pk + (uint32_t)1U, pk_x, (uint32_t)32U * sizeof (uint8_t));
}

/**
Public key validation.

  The function returns `true` if a public key is valid and `false` otherwise.

  The argument `pk` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve. 
*/
bool Hacl_K256_ECDSA_is_public_key_valid(uint8_t *pk)
{
  uint64_t fpk_x[5U] = { 0U };
  uint64_t fpk_y[5U] = { 0U };
  bool is_pk_valid = load_public_key(pk, fpk_x, fpk_y);
  return is_pk_valid;
}

/**
Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` and `private_key` < the order of the curve.
*/
bool Hacl_K256_ECDSA_secret_to_public(uint8_t *public_key, uint8_t *private_key)
{
  uint64_t d_a[4U] = { 0U };
  uint64_t p[15U] = { 0U };
  uint64_t is_sk_valid = load_qelem_check(d_a, private_key);
  uint64_t oneq[4U] = { (uint64_t)0x1U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = d_a;
    uint64_t uu____0 = oneq[i];
    uint64_t x = uu____0 ^ (is_sk_valid & (d_a[i] ^ uu____0));
    os[i] = x;);
  point_mul_g(p, d_a);
  uint64_t px[5U] = { 0U };
  uint64_t py[5U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t zinv[5U] = { 0U };
  Hacl_Impl_K256_Finv_finv(zinv, z1);
  Hacl_K256_Field_fmul(px, x1, zinv);
  Hacl_K256_Field_fmul(py, y1, zinv);
  Hacl_K256_Field_fnormalize(px, px);
  Hacl_K256_Field_fnormalize(py, py);
  Hacl_K256_Field_store_felem(public_key, px);
  Hacl_K256_Field_store_felem(public_key + (uint32_t)32U, py);
  return is_sk_valid == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

