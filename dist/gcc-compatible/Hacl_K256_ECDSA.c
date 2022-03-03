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


#include "Hacl_K256_ECDSA.h"

#include "internal/Hacl_Kremlib.h"
#include "internal/Hacl_Bignum.h"

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
    uint32_t rLen = aLen - bLen;
    uint64_t *a1 = a + bLen;
    uint64_t *res1 = res + bLen;
    uint64_t c = c00;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
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
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  return c;
}

static void add_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = res + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    uint64_t *res_i0 = tmp + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tmp + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tmp + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tmp + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static void mul4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
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
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    res[(uint32_t)4U + i0] = r;
  }
}

static void sqr4(uint64_t *a, uint64_t *res)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
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
    res[i0 + i0] = r;
  }
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, res, res);
  uint64_t tmp[8U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, tmp, res);
}

static inline uint64_t is_qelem_zero(uint64_t *f)
{
  uint64_t bn_zero[4U] = { 0U };
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(f[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
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

static inline void load_qelem(uint64_t *f, uint8_t *b)
{
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)32U, b, f);
}

static inline bool load_qelem_vartime(uint64_t *f, uint8_t *b)
{
  load_qelem(f, b);
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = out;
    uint64_t x = (mask & out[i]) | (~mask & a[i]);
    os[i] = x;
  }
}

static inline void load_qelem_modq(uint64_t *f, uint8_t *b)
{
  uint64_t tmp[4U] = { 0U };
  load_qelem(f, b);
  memcpy(tmp, f, (uint32_t)4U * sizeof (uint64_t));
  modq_short(f, tmp);
}

static inline void store_qelem(uint8_t *b, uint64_t *f)
{
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64((uint32_t)32U, f, b);
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
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)2U; i0++)
  {
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
    tmp[len + i0] = r;
  }
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = out;
    uint64_t x = (mask & out[i]) | (~mask & r[i]);
    os[i] = x;
  }
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

static inline bool is_felem_zero_vartime(uint64_t *f)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t f4 = f[4U];
  return
    f0
    == (uint64_t)0U
    && f1 == (uint64_t)0U
    && f2 == (uint64_t)0U
    && f3 == (uint64_t)0U
    && f4 == (uint64_t)0U;
}

static inline bool is_felem_eq_vartime(uint64_t *f1, uint64_t *f2)
{
  uint64_t a0 = f1[0U];
  uint64_t a1 = f1[1U];
  uint64_t a2 = f1[2U];
  uint64_t a3 = f1[3U];
  uint64_t a4 = f1[4U];
  uint64_t b0 = f2[0U];
  uint64_t b1 = f2[1U];
  uint64_t b2 = f2[2U];
  uint64_t b3 = f2[3U];
  uint64_t b4 = f2[4U];
  return a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4;
}

static inline bool is_felem_lt_prime_minus_order_vartime(uint64_t *f)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t f4 = f[4U];
  if (f4 > (uint64_t)0U)
  {
    return false;
  }
  if (f3 > (uint64_t)0U)
  {
    return false;
  }
  if (f2 < (uint64_t)0x1455123U)
  {
    return true;
  }
  if (f2 > (uint64_t)0x1455123U)
  {
    return false;
  }
  if (f1 < (uint64_t)0x1950b75fc4402U)
  {
    return true;
  }
  if (f1 > (uint64_t)0x1950b75fc4402U)
  {
    return false;
  }
  return f0 < (uint64_t)0xda1722fc9baeeU;
}

static inline void load_felem(uint64_t *f, uint8_t *b)
{
  uint64_t tmp[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = tmp;
    uint8_t *bj = b + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t s0 = tmp[3U];
  uint64_t s1 = tmp[2U];
  uint64_t s2 = tmp[1U];
  uint64_t s3 = tmp[0U];
  uint64_t f00 = s0 & (uint64_t)0xfffffffffffffU;
  uint64_t f10 = s0 >> (uint32_t)52U | (s1 & (uint64_t)0xffffffffffU) << (uint32_t)12U;
  uint64_t f20 = s1 >> (uint32_t)40U | (s2 & (uint64_t)0xfffffffU) << (uint32_t)24U;
  uint64_t f30 = s2 >> (uint32_t)28U | (s3 & (uint64_t)0xffffU) << (uint32_t)36U;
  uint64_t f40 = s3 >> (uint32_t)16U;
  uint64_t f0 = f00;
  uint64_t f1 = f10;
  uint64_t f2 = f20;
  uint64_t f3 = f30;
  uint64_t f4 = f40;
  f[0U] = f0;
  f[1U] = f1;
  f[2U] = f2;
  f[3U] = f3;
  f[4U] = f4;
}

static inline bool load_felem_vartime(uint64_t *f, uint8_t *b)
{
  load_felem(f, b);
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t f4 = f[4U];
  bool
  is_ge_p =
    f0
    >= (uint64_t)0xffffefffffc2fU
    && f1 == (uint64_t)0xfffffffffffffU
    && f2 == (uint64_t)0xfffffffffffffU
    && f3 == (uint64_t)0xfffffffffffffU
    && f4 == (uint64_t)0xffffffffffffU;
  if (is_ge_p)
  {
    return false;
  }
  return !is_felem_zero_vartime(f);
}

static inline void store_felem(uint8_t *b, uint64_t *f)
{
  uint64_t tmp[4U] = { 0U };
  uint64_t f00 = f[0U];
  uint64_t f10 = f[1U];
  uint64_t f20 = f[2U];
  uint64_t f30 = f[3U];
  uint64_t f4 = f[4U];
  uint64_t o0 = f00 | f10 << (uint32_t)52U;
  uint64_t o1 = f10 >> (uint32_t)12U | f20 << (uint32_t)40U;
  uint64_t o2 = f20 >> (uint32_t)24U | f30 << (uint32_t)28U;
  uint64_t o3 = f30 >> (uint32_t)36U | f4 << (uint32_t)16U;
  uint64_t f0 = o0;
  uint64_t f1 = o1;
  uint64_t f2 = o2;
  uint64_t f3 = o3;
  tmp[0U] = f3;
  tmp[1U] = f2;
  tmp[2U] = f1;
  tmp[3U] = f0;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store64_be(b + i * (uint32_t)8U, tmp[i]);
  }
}

static inline void fmul_small_num(uint64_t *out, uint64_t *f, uint64_t num)
{
  uint64_t f00 = f[0U];
  uint64_t f10 = f[1U];
  uint64_t f20 = f[2U];
  uint64_t f30 = f[3U];
  uint64_t f40 = f[4U];
  uint64_t o0 = f00 * num;
  uint64_t o1 = f10 * num;
  uint64_t o2 = f20 * num;
  uint64_t o3 = f30 * num;
  uint64_t o4 = f40 * num;
  uint64_t f0 = o0;
  uint64_t f1 = o1;
  uint64_t f2 = o2;
  uint64_t f3 = o3;
  uint64_t f4 = o4;
  out[0U] = f0;
  out[1U] = f1;
  out[2U] = f2;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void fadd0(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t a0 = f1[0U];
  uint64_t a1 = f1[1U];
  uint64_t a2 = f1[2U];
  uint64_t a3 = f1[3U];
  uint64_t a4 = f1[4U];
  uint64_t b0 = f2[0U];
  uint64_t b1 = f2[1U];
  uint64_t b2 = f2[2U];
  uint64_t b3 = f2[3U];
  uint64_t b4 = f2[4U];
  uint64_t o0 = a0 + b0;
  uint64_t o1 = a1 + b1;
  uint64_t o2 = a2 + b2;
  uint64_t o3 = a3 + b3;
  uint64_t o4 = a4 + b4;
  uint64_t f0 = o0;
  uint64_t f11 = o1;
  uint64_t f21 = o2;
  uint64_t f3 = o3;
  uint64_t f4 = o4;
  out[0U] = f0;
  out[1U] = f11;
  out[2U] = f21;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void fsub0(uint64_t *out, uint64_t *f1, uint64_t *f2, uint64_t x)
{
  uint64_t a0 = f1[0U];
  uint64_t a1 = f1[1U];
  uint64_t a2 = f1[2U];
  uint64_t a3 = f1[3U];
  uint64_t a4 = f1[4U];
  uint64_t b0 = f2[0U];
  uint64_t b1 = f2[1U];
  uint64_t b2 = f2[2U];
  uint64_t b3 = f2[3U];
  uint64_t b4 = f2[4U];
  uint64_t r00 = (uint64_t)0xffffefffffc2fU * (uint64_t)2U * x - b0;
  uint64_t r10 = (uint64_t)0xfffffffffffffU * (uint64_t)2U * x - b1;
  uint64_t r20 = (uint64_t)0xfffffffffffffU * (uint64_t)2U * x - b2;
  uint64_t r30 = (uint64_t)0xfffffffffffffU * (uint64_t)2U * x - b3;
  uint64_t r40 = (uint64_t)0xffffffffffffU * (uint64_t)2U * x - b4;
  uint64_t r0 = r00;
  uint64_t r1 = r10;
  uint64_t r2 = r20;
  uint64_t r3 = r30;
  uint64_t r4 = r40;
  uint64_t o0 = a0 + r0;
  uint64_t o1 = a1 + r1;
  uint64_t o2 = a2 + r2;
  uint64_t o3 = a3 + r3;
  uint64_t o4 = a4 + r4;
  uint64_t f0 = o0;
  uint64_t f11 = o1;
  uint64_t f21 = o2;
  uint64_t f3 = o3;
  uint64_t f4 = o4;
  out[0U] = f0;
  out[1U] = f11;
  out[2U] = f21;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void fmul0(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t a0 = f1[0U];
  uint64_t a1 = f1[1U];
  uint64_t a2 = f1[2U];
  uint64_t a3 = f1[3U];
  uint64_t a4 = f1[4U];
  uint64_t b0 = f2[0U];
  uint64_t b1 = f2[1U];
  uint64_t b2 = f2[2U];
  uint64_t b3 = f2[3U];
  uint64_t b4 = f2[4U];
  uint64_t r = (uint64_t)0x1000003D10U;
  FStar_UInt128_uint128
  d0 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_mul_wide(a0,
            b3),
          FStar_UInt128_mul_wide(a1, b2)),
        FStar_UInt128_mul_wide(a2, b1)),
      FStar_UInt128_mul_wide(a3, b0));
  FStar_UInt128_uint128 c0 = FStar_UInt128_mul_wide(a4, b4);
  FStar_UInt128_uint128
  d1 = FStar_UInt128_add_mod(d0, FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(c0)));
  uint64_t c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(c0, (uint32_t)64U));
  uint64_t t3 = FStar_UInt128_uint128_to_uint64(d1) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 d2 = FStar_UInt128_shift_right(d1, (uint32_t)52U);
  FStar_UInt128_uint128
  d3 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(d2,
              FStar_UInt128_mul_wide(a0, b4)),
            FStar_UInt128_mul_wide(a1, b3)),
          FStar_UInt128_mul_wide(a2, b2)),
        FStar_UInt128_mul_wide(a3, b1)),
      FStar_UInt128_mul_wide(a4, b0));
  FStar_UInt128_uint128
  d4 = FStar_UInt128_add_mod(d3, FStar_UInt128_mul_wide(r << (uint32_t)12U, c1));
  uint64_t t4 = FStar_UInt128_uint128_to_uint64(d4) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 d5 = FStar_UInt128_shift_right(d4, (uint32_t)52U);
  uint64_t tx = t4 >> (uint32_t)48U;
  uint64_t t4_ = t4 & (uint64_t)0xffffffffffffU;
  FStar_UInt128_uint128 c2 = FStar_UInt128_mul_wide(a0, b0);
  FStar_UInt128_uint128
  d6 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(d5,
            FStar_UInt128_mul_wide(a1, b4)),
          FStar_UInt128_mul_wide(a2, b3)),
        FStar_UInt128_mul_wide(a3, b2)),
      FStar_UInt128_mul_wide(a4, b1));
  uint64_t u0 = FStar_UInt128_uint128_to_uint64(d6) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 d7 = FStar_UInt128_shift_right(d6, (uint32_t)52U);
  uint64_t u0_ = tx | u0 << (uint32_t)4U;
  FStar_UInt128_uint128
  c3 = FStar_UInt128_add_mod(c2, FStar_UInt128_mul_wide(u0_, r >> (uint32_t)4U));
  uint64_t r0 = FStar_UInt128_uint128_to_uint64(c3) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 c4 = FStar_UInt128_shift_right(c3, (uint32_t)52U);
  FStar_UInt128_uint128
  c5 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(c4, FStar_UInt128_mul_wide(a0, b1)),
      FStar_UInt128_mul_wide(a1, b0));
  FStar_UInt128_uint128
  d8 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(d7,
          FStar_UInt128_mul_wide(a2, b4)),
        FStar_UInt128_mul_wide(a3, b3)),
      FStar_UInt128_mul_wide(a4, b2));
  FStar_UInt128_uint128
  c6 =
    FStar_UInt128_add_mod(c5,
      FStar_UInt128_mul_wide(FStar_UInt128_uint128_to_uint64(d8) & (uint64_t)0xfffffffffffffU, r));
  FStar_UInt128_uint128 d9 = FStar_UInt128_shift_right(d8, (uint32_t)52U);
  uint64_t r1 = FStar_UInt128_uint128_to_uint64(c6) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 c7 = FStar_UInt128_shift_right(c6, (uint32_t)52U);
  FStar_UInt128_uint128
  c8 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(c7,
          FStar_UInt128_mul_wide(a0, b2)),
        FStar_UInt128_mul_wide(a1, b1)),
      FStar_UInt128_mul_wide(a2, b0));
  FStar_UInt128_uint128
  d10 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(d9, FStar_UInt128_mul_wide(a3, b4)),
      FStar_UInt128_mul_wide(a4, b3));
  FStar_UInt128_uint128
  c9 = FStar_UInt128_add_mod(c8, FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(d10)));
  uint64_t d11 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(d10, (uint32_t)64U));
  uint64_t r2 = FStar_UInt128_uint128_to_uint64(c9) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 c10 = FStar_UInt128_shift_right(c9, (uint32_t)52U);
  FStar_UInt128_uint128
  c11 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(c10,
        FStar_UInt128_mul_wide(r << (uint32_t)12U, d11)),
      FStar_UInt128_uint64_to_uint128(t3));
  uint64_t r3 = FStar_UInt128_uint128_to_uint64(c11) & (uint64_t)0xfffffffffffffU;
  uint64_t c12 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(c11, (uint32_t)52U));
  uint64_t r4 = c12 + t4_;
  uint64_t f0 = r0;
  uint64_t f11 = r1;
  uint64_t f21 = r2;
  uint64_t f3 = r3;
  uint64_t f4 = r4;
  out[0U] = f0;
  out[1U] = f11;
  out[2U] = f21;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void fsqr0(uint64_t *out, uint64_t *f)
{
  uint64_t a0 = f[0U];
  uint64_t a1 = f[1U];
  uint64_t a2 = f[2U];
  uint64_t a3 = f[3U];
  uint64_t a4 = f[4U];
  uint64_t r = (uint64_t)0x1000003D10U;
  FStar_UInt128_uint128
  d0 =
    FStar_UInt128_add_mod(FStar_UInt128_mul_wide(a0 * (uint64_t)2U, a3),
      FStar_UInt128_mul_wide(a1 * (uint64_t)2U, a2));
  FStar_UInt128_uint128 c0 = FStar_UInt128_mul_wide(a4, a4);
  FStar_UInt128_uint128
  d1 = FStar_UInt128_add_mod(d0, FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(c0)));
  uint64_t c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(c0, (uint32_t)64U));
  uint64_t t3 = FStar_UInt128_uint128_to_uint64(d1) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 d2 = FStar_UInt128_shift_right(d1, (uint32_t)52U);
  uint64_t a41 = a4 * (uint64_t)2U;
  FStar_UInt128_uint128
  d3 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(d2,
          FStar_UInt128_mul_wide(a0, a41)),
        FStar_UInt128_mul_wide(a1 * (uint64_t)2U, a3)),
      FStar_UInt128_mul_wide(a2, a2));
  FStar_UInt128_uint128
  d4 = FStar_UInt128_add_mod(d3, FStar_UInt128_mul_wide(r << (uint32_t)12U, c1));
  uint64_t t4 = FStar_UInt128_uint128_to_uint64(d4) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 d5 = FStar_UInt128_shift_right(d4, (uint32_t)52U);
  uint64_t tx = t4 >> (uint32_t)48U;
  uint64_t t4_ = t4 & (uint64_t)0xffffffffffffU;
  FStar_UInt128_uint128 c2 = FStar_UInt128_mul_wide(a0, a0);
  FStar_UInt128_uint128
  d6 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(d5, FStar_UInt128_mul_wide(a1, a41)),
      FStar_UInt128_mul_wide(a2 * (uint64_t)2U, a3));
  uint64_t u0 = FStar_UInt128_uint128_to_uint64(d6) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 d7 = FStar_UInt128_shift_right(d6, (uint32_t)52U);
  uint64_t u0_ = tx | u0 << (uint32_t)4U;
  FStar_UInt128_uint128
  c3 = FStar_UInt128_add_mod(c2, FStar_UInt128_mul_wide(u0_, r >> (uint32_t)4U));
  uint64_t r0 = FStar_UInt128_uint128_to_uint64(c3) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 c4 = FStar_UInt128_shift_right(c3, (uint32_t)52U);
  uint64_t a01 = a0 * (uint64_t)2U;
  FStar_UInt128_uint128 c5 = FStar_UInt128_add_mod(c4, FStar_UInt128_mul_wide(a01, a1));
  FStar_UInt128_uint128
  d8 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(d7, FStar_UInt128_mul_wide(a2, a41)),
      FStar_UInt128_mul_wide(a3, a3));
  FStar_UInt128_uint128
  c6 =
    FStar_UInt128_add_mod(c5,
      FStar_UInt128_mul_wide(FStar_UInt128_uint128_to_uint64(d8) & (uint64_t)0xfffffffffffffU, r));
  FStar_UInt128_uint128 d9 = FStar_UInt128_shift_right(d8, (uint32_t)52U);
  uint64_t r1 = FStar_UInt128_uint128_to_uint64(c6) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 c7 = FStar_UInt128_shift_right(c6, (uint32_t)52U);
  FStar_UInt128_uint128
  c8 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(c7, FStar_UInt128_mul_wide(a01, a2)),
      FStar_UInt128_mul_wide(a1, a1));
  FStar_UInt128_uint128 d10 = FStar_UInt128_add_mod(d9, FStar_UInt128_mul_wide(a3, a41));
  FStar_UInt128_uint128
  c9 = FStar_UInt128_add_mod(c8, FStar_UInt128_mul_wide(r, FStar_UInt128_uint128_to_uint64(d10)));
  uint64_t d11 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(d10, (uint32_t)64U));
  uint64_t r2 = FStar_UInt128_uint128_to_uint64(c9) & (uint64_t)0xfffffffffffffU;
  FStar_UInt128_uint128 c10 = FStar_UInt128_shift_right(c9, (uint32_t)52U);
  FStar_UInt128_uint128
  c11 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(c10,
        FStar_UInt128_mul_wide(r << (uint32_t)12U, d11)),
      FStar_UInt128_uint64_to_uint128(t3));
  uint64_t r3 = FStar_UInt128_uint128_to_uint64(c11) & (uint64_t)0xfffffffffffffU;
  uint64_t c12 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(c11, (uint32_t)52U));
  uint64_t r4 = c12 + t4_;
  uint64_t f0 = r0;
  uint64_t f1 = r1;
  uint64_t f2 = r2;
  uint64_t f3 = r3;
  uint64_t f4 = r4;
  out[0U] = f0;
  out[1U] = f1;
  out[2U] = f2;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void fnormalize_weak(uint64_t *out, uint64_t *f)
{
  uint64_t t0 = f[0U];
  uint64_t t1 = f[1U];
  uint64_t t2 = f[2U];
  uint64_t t3 = f[3U];
  uint64_t t4 = f[4U];
  uint64_t x0 = t4 >> (uint32_t)48U;
  uint64_t t410 = t4 & (uint64_t)0xffffffffffffU;
  uint64_t x = x0;
  uint64_t t01 = t0;
  uint64_t t11 = t1;
  uint64_t t21 = t2;
  uint64_t t31 = t3;
  uint64_t t41 = t410;
  uint64_t t02 = t01 + x * (uint64_t)0x1000003D1U;
  uint64_t t12 = t11 + (t02 >> (uint32_t)52U);
  uint64_t t03 = t02 & (uint64_t)0xfffffffffffffU;
  uint64_t t22 = t21 + (t12 >> (uint32_t)52U);
  uint64_t t13 = t12 & (uint64_t)0xfffffffffffffU;
  uint64_t t32 = t31 + (t22 >> (uint32_t)52U);
  uint64_t t23 = t22 & (uint64_t)0xfffffffffffffU;
  uint64_t t42 = t41 + (t32 >> (uint32_t)52U);
  uint64_t t33 = t32 & (uint64_t)0xfffffffffffffU;
  uint64_t f0 = t03;
  uint64_t f1 = t13;
  uint64_t f2 = t23;
  uint64_t f3 = t33;
  uint64_t f4 = t42;
  out[0U] = f0;
  out[1U] = f1;
  out[2U] = f2;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void fnormalize(uint64_t *out, uint64_t *f)
{
  uint64_t f00 = f[0U];
  uint64_t f10 = f[1U];
  uint64_t f20 = f[2U];
  uint64_t f30 = f[3U];
  uint64_t f40 = f[4U];
  uint64_t x0 = f40 >> (uint32_t)48U;
  uint64_t t40 = f40 & (uint64_t)0xffffffffffffU;
  uint64_t x1 = x0;
  uint64_t t00 = f00;
  uint64_t t10 = f10;
  uint64_t t20 = f20;
  uint64_t t30 = f30;
  uint64_t t42 = t40;
  uint64_t t01 = t00 + x1 * (uint64_t)0x1000003D1U;
  uint64_t t110 = t10 + (t01 >> (uint32_t)52U);
  uint64_t t020 = t01 & (uint64_t)0xfffffffffffffU;
  uint64_t t210 = t20 + (t110 >> (uint32_t)52U);
  uint64_t t120 = t110 & (uint64_t)0xfffffffffffffU;
  uint64_t t310 = t30 + (t210 >> (uint32_t)52U);
  uint64_t t220 = t210 & (uint64_t)0xfffffffffffffU;
  uint64_t t410 = t42 + (t310 >> (uint32_t)52U);
  uint64_t t320 = t310 & (uint64_t)0xfffffffffffffU;
  uint64_t t0 = t020;
  uint64_t t1 = t120;
  uint64_t t2 = t220;
  uint64_t t3 = t320;
  uint64_t t4 = t410;
  uint64_t x2 = t4 >> (uint32_t)48U;
  uint64_t t411 = t4 & (uint64_t)0xffffffffffffU;
  uint64_t x = x2;
  uint64_t r0 = t0;
  uint64_t r1 = t1;
  uint64_t r2 = t2;
  uint64_t r3 = t3;
  uint64_t r4 = t411;
  uint64_t m4 = FStar_UInt64_eq_mask(r4, (uint64_t)0xffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(r3, (uint64_t)0xfffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(r2, (uint64_t)0xfffffffffffffU);
  uint64_t m1 = FStar_UInt64_eq_mask(r1, (uint64_t)0xfffffffffffffU);
  uint64_t m0 = FStar_UInt64_gte_mask(r0, (uint64_t)0xffffefffffc2fU);
  uint64_t is_ge_p_m = (((m0 & m1) & m2) & m3) & m4;
  uint64_t m_to_one = is_ge_p_m & (uint64_t)1U;
  uint64_t x10 = m_to_one | x;
  uint64_t t010 = r0 + x10 * (uint64_t)0x1000003D1U;
  uint64_t t11 = r1 + (t010 >> (uint32_t)52U);
  uint64_t t02 = t010 & (uint64_t)0xfffffffffffffU;
  uint64_t t21 = r2 + (t11 >> (uint32_t)52U);
  uint64_t t12 = t11 & (uint64_t)0xfffffffffffffU;
  uint64_t t31 = r3 + (t21 >> (uint32_t)52U);
  uint64_t t22 = t21 & (uint64_t)0xfffffffffffffU;
  uint64_t t41 = r4 + (t31 >> (uint32_t)52U);
  uint64_t t32 = t31 & (uint64_t)0xfffffffffffffU;
  uint64_t s0 = t02;
  uint64_t s1 = t12;
  uint64_t s2 = t22;
  uint64_t s3 = t32;
  uint64_t s4 = t41;
  uint64_t t412 = s4 & (uint64_t)0xffffffffffffU;
  uint64_t k0 = s0;
  uint64_t k1 = s1;
  uint64_t k2 = s2;
  uint64_t k3 = s3;
  uint64_t k4 = t412;
  uint64_t f0 = k0;
  uint64_t f1 = k1;
  uint64_t f2 = k2;
  uint64_t f3 = k3;
  uint64_t f4 = k4;
  out[0U] = f0;
  out[1U] = f1;
  out[2U] = f2;
  out[3U] = f3;
  out[4U] = f4;
}

static inline void point_double(uint64_t *out, uint64_t *p)
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
  fsqr0(yy, y1);
  fsqr0(zz, z1);
  fmul_small_num(x3, x1, (uint64_t)2U);
  fmul0(x3, x3, y1);
  fmul0(tmp1, yy, y1);
  fmul0(z3, tmp1, z1);
  fmul_small_num(z3, z3, (uint64_t)8U);
  fnormalize_weak(z3, z3);
  fmul_small_num(bzz3, zz, (uint64_t)21U);
  fnormalize_weak(bzz3, bzz3);
  fmul_small_num(bzz9, bzz3, (uint64_t)3U);
  fsub0(bzz9, yy, bzz9, (uint64_t)6U);
  fadd0(tmp1, yy, bzz3);
  fmul0(tmp1, bzz9, tmp1);
  fmul0(y3, yy, zz);
  fmul0(x3, x3, bzz9);
  fmul_small_num(y3, y3, (uint64_t)168U);
  fadd0(y3, tmp1, y3);
  fnormalize_weak(y3, y3);
}

static inline void point_add(uint64_t *out, uint64_t *p, uint64_t *q)
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
  fmul0(xx, x1, x2);
  fmul0(yy, y1, y2);
  fmul0(zz, z1, z2);
  fadd0(xy_pairs, x1, y1);
  fadd0(tmp1, x2, y2);
  fmul0(xy_pairs, xy_pairs, tmp1);
  fadd0(tmp1, xx, yy);
  fsub0(xy_pairs, xy_pairs, tmp1, (uint64_t)4U);
  fadd0(yz_pairs, y1, z1);
  fadd0(tmp1, y2, z2);
  fmul0(yz_pairs, yz_pairs, tmp1);
  fadd0(tmp1, yy, zz);
  fsub0(yz_pairs, yz_pairs, tmp1, (uint64_t)4U);
  fadd0(xz_pairs, x1, z1);
  fadd0(tmp1, x2, z2);
  fmul0(xz_pairs, xz_pairs, tmp1);
  fadd0(tmp1, xx, zz);
  fsub0(xz_pairs, xz_pairs, tmp1, (uint64_t)4U);
  fmul_small_num(tmp1, zz, (uint64_t)21U);
  fnormalize_weak(tmp1, tmp1);
  fsub0(yy_m_bzz3, yy, tmp1, (uint64_t)2U);
  fadd0(yy_p_bzz3, yy, tmp1);
  fmul_small_num(x3, yz_pairs, (uint64_t)21U);
  fnormalize_weak(x3, x3);
  fmul_small_num(z3, xx, (uint64_t)3U);
  fmul_small_num(y3, z3, (uint64_t)21U);
  fnormalize_weak(y3, y3);
  fmul0(tmp1, xy_pairs, yy_m_bzz3);
  fmul0(x3, x3, xz_pairs);
  fsub0(x3, tmp1, x3, (uint64_t)2U);
  fnormalize_weak(x3, x3);
  fmul0(tmp1, yy_p_bzz3, yy_m_bzz3);
  fmul0(y3, y3, xz_pairs);
  fadd0(y3, tmp1, y3);
  fnormalize_weak(y3, y3);
  fmul0(tmp1, yz_pairs, yy_p_bzz3);
  fmul0(z3, z3, xy_pairs);
  fadd0(z3, tmp1, z3);
  fnormalize_weak(z3, z3);
}

static inline void point_mul(uint64_t *out, uint64_t *scalar, uint64_t *q)
{
  uint64_t *px = out;
  uint64_t *py = out + (uint32_t)5U;
  uint64_t *pz = out + (uint32_t)10U;
  memset(px, 0U, (uint32_t)5U * sizeof (uint64_t));
  memset(py, 0U, (uint32_t)5U * sizeof (uint64_t));
  py[0U] = (uint64_t)1U;
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
  uint64_t table[240U] = { 0U };
  memcpy(table, out, (uint32_t)15U * sizeof (uint64_t));
  uint64_t *t1 = table + (uint32_t)15U;
  memcpy(t1, q, (uint32_t)15U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)15U; i++)
  {
    uint64_t *t11 = table + i * (uint32_t)15U;
    uint64_t *t2 = table + i * (uint32_t)15U + (uint32_t)15U;
    point_add(t2, q, t11);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      point_double(out, out);
    }
    uint32_t bk = (uint32_t)256U;
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
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
    uint64_t a_bits_l[15U] = { 0U };
    memcpy(a_bits_l, table, (uint32_t)15U * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < (uint32_t)15U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)15U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)15U; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    point_add(out, out, a_bits_l);
  }
}

static inline void
point_mul_double_vartime(
  uint64_t *out,
  uint64_t *scalar1,
  uint64_t *q1,
  uint64_t *scalar2,
  uint64_t *q2
)
{
  uint64_t *px = out;
  uint64_t *py = out + (uint32_t)5U;
  uint64_t *pz = out + (uint32_t)10U;
  memset(px, 0U, (uint32_t)5U * sizeof (uint64_t));
  memset(py, 0U, (uint32_t)5U * sizeof (uint64_t));
  py[0U] = (uint64_t)1U;
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
  uint64_t table1[240U] = { 0U };
  memcpy(table1, out, (uint32_t)15U * sizeof (uint64_t));
  uint64_t *t10 = table1 + (uint32_t)15U;
  memcpy(t10, q1, (uint32_t)15U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)15U; i++)
  {
    uint64_t *t11 = table1 + i * (uint32_t)15U;
    uint64_t *t2 = table1 + i * (uint32_t)15U + (uint32_t)15U;
    point_add(t2, q1, t11);
  }
  uint64_t table2[240U] = { 0U };
  memcpy(table2, out, (uint32_t)15U * sizeof (uint64_t));
  uint64_t *t1 = table2 + (uint32_t)15U;
  memcpy(t1, q2, (uint32_t)15U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)15U; i++)
  {
    uint64_t *t11 = table2 + i * (uint32_t)15U;
    uint64_t *t2 = table2 + i * (uint32_t)15U + (uint32_t)15U;
    point_add(t2, q2, t11);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      point_double(out, out);
    }
    uint32_t bk = (uint32_t)256U;
    uint64_t mask_l0 = (uint64_t)16U - (uint64_t)1U;
    uint32_t i10 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j0 = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p10 = scalar1[i10] >> j0;
    uint64_t ite0;
    if (i10 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
    {
      ite0 = p10 | scalar1[i10 + (uint32_t)1U] << ((uint32_t)64U - j0);
    }
    else
    {
      ite0 = p10;
    }
    uint64_t bits_l = ite0 & mask_l0;
    uint64_t a_bits_l0[15U] = { 0U };
    uint32_t bits_l320 = (uint32_t)bits_l;
    uint64_t *a_bits_l1 = table1 + bits_l320 * (uint32_t)15U;
    memcpy(a_bits_l0, a_bits_l1, (uint32_t)15U * sizeof (uint64_t));
    point_add(out, out, a_bits_l0);
    uint32_t bk0 = (uint32_t)256U;
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
    uint32_t i1 = (bk0 - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bk0 - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = scalar2[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | scalar2[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l0 = ite & mask_l;
    uint64_t a_bits_l[15U] = { 0U };
    uint32_t bits_l32 = (uint32_t)bits_l0;
    uint64_t *a_bits_l10 = table2 + bits_l32 * (uint32_t)15U;
    memcpy(a_bits_l, a_bits_l10, (uint32_t)15U * sizeof (uint64_t));
    point_add(out, out, a_bits_l);
  }
}

static inline void point_mul_g(uint64_t *out, uint64_t *scalar)
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
  point_mul(out, scalar, g);
}

static inline void
point_mul_g_double_vartime(uint64_t *out, uint64_t *scalar1, uint64_t *scalar2, uint64_t *q2)
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
  point_mul_double_vartime(out, scalar1, g, scalar2, q2);
}

static inline bool
is_public_key_valid(uint8_t *pk_x, uint8_t *pk_y, uint64_t *fpk_x, uint64_t *fpk_y)
{
  bool is_x_valid = load_felem_vartime(fpk_x, pk_x);
  bool is_y_valid = load_felem_vartime(fpk_y, pk_y);
  if (is_x_valid && is_y_valid)
  {
    uint64_t y2[5U] = { 0U };
    uint64_t x3[5U] = { 0U };
    uint64_t b[5U] = { 0U };
    fsqr0(y2, fpk_y);
    fsqr0(x3, fpk_x);
    fmul0(x3, x3, fpk_x);
    b[0U] = (uint64_t)0x7U;
    b[1U] = (uint64_t)0U;
    b[2U] = (uint64_t)0U;
    b[3U] = (uint64_t)0U;
    b[4U] = (uint64_t)0U;
    fadd0(x3, x3, b);
    fnormalize(x3, x3);
    fnormalize(y2, y2);
    bool res = is_felem_eq_vartime(y2, x3);
    return res;
  }
  return false;
}

static inline bool fmul_eq_vartime(uint64_t *r, uint64_t *z, uint64_t *x)
{
  uint64_t tmp[5U] = { 0U };
  fmul0(tmp, r, z);
  fnormalize(tmp, tmp);
  bool b = is_felem_eq_vartime(tmp, x);
  return b;
}

static inline void fsquare_times_in_place(uint64_t *out, uint32_t b)
{
  for (uint32_t i = (uint32_t)0U; i < b; i++)
  {
    fsqr0(out, out);
  }
}

static inline void fsquare_times(uint64_t *out, uint64_t *a, uint32_t b)
{
  memcpy(out, a, (uint32_t)5U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < b; i++)
  {
    fsqr0(out, out);
  }
}

static inline void finv(uint64_t *out, uint64_t *f)
{
  uint64_t x2[5U] = { 0U };
  uint64_t x3[5U] = { 0U };
  uint64_t x22[5U] = { 0U };
  uint64_t x44[5U] = { 0U };
  uint64_t x88[5U] = { 0U };
  uint64_t tmp[5U] = { 0U };
  fsquare_times(x2, f, (uint32_t)1U);
  fmul0(x2, x2, f);
  fsquare_times(x3, x2, (uint32_t)1U);
  fmul0(x3, x3, f);
  fsquare_times(tmp, x3, (uint32_t)3U);
  fmul0(tmp, tmp, x3);
  fsquare_times_in_place(tmp, (uint32_t)3U);
  fmul0(tmp, tmp, x3);
  fsquare_times_in_place(tmp, (uint32_t)2U);
  fmul0(tmp, tmp, x2);
  fsquare_times(x22, tmp, (uint32_t)11U);
  fmul0(x22, x22, tmp);
  fsquare_times(x44, x22, (uint32_t)22U);
  fmul0(x44, x44, x22);
  fsquare_times(x88, x44, (uint32_t)44U);
  fmul0(x88, x88, x44);
  fsquare_times(tmp, x88, (uint32_t)88U);
  fmul0(tmp, tmp, x88);
  fsquare_times_in_place(tmp, (uint32_t)44U);
  fmul0(tmp, tmp, x44);
  fsquare_times_in_place(tmp, (uint32_t)3U);
  fmul0(tmp, tmp, x3);
  fsquare_times_in_place(tmp, (uint32_t)23U);
  fmul0(tmp, tmp, x22);
  fsquare_times_in_place(tmp, (uint32_t)5U);
  fmul0(tmp, tmp, f);
  fsquare_times_in_place(tmp, (uint32_t)3U);
  fmul0(tmp, tmp, x2);
  fsquare_times_in_place(tmp, (uint32_t)2U);
  fmul0(tmp, tmp, f);
  memcpy(out, tmp, (uint32_t)5U * sizeof (uint64_t));
}

inline bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *r,
  uint8_t *s,
  uint8_t *m,
  uint8_t *private_key,
  uint8_t *k
)
{
  uint64_t r_q[4U] = { 0U };
  uint64_t s_q[4U] = { 0U };
  uint64_t k_q[4U] = { 0U };
  load_qelem(k_q, k);
  uint64_t tmp[5U] = { 0U };
  uint8_t x_bytes[32U] = { 0U };
  uint64_t p[15U] = { 0U };
  point_mul_g(p, k_q);
  uint64_t *x = p;
  uint64_t *z = p + (uint32_t)10U;
  finv(tmp, z);
  fmul0(tmp, x, tmp);
  fnormalize(tmp, tmp);
  store_felem(x_bytes, tmp);
  load_qelem_modq(r_q, x_bytes);
  uint64_t z0[4U] = { 0U };
  uint64_t d_a[4U] = { 0U };
  uint64_t kinv[4U] = { 0U };
  load_qelem_modq(z0, m);
  load_qelem(d_a, private_key);
  qinv(kinv, k_q);
  qmul(s_q, r_q, d_a);
  qadd(s_q, z0, s_q);
  qmul(s_q, kinv, s_q);
  store_qelem(r, r_q);
  store_qelem(s, s_q);
  uint64_t is_r_zero = is_qelem_zero(r_q);
  uint64_t is_s_zero = is_qelem_zero(s_q);
  if (is_r_zero == (uint64_t)0xFFFFFFFFFFFFFFFFU || is_s_zero == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    return false;
  }
  return true;
}

inline bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(
  uint8_t *m,
  uint8_t *public_key_x,
  uint8_t *public_key_y,
  uint8_t *r,
  uint8_t *s
)
{
  uint64_t pk_x[5U] = { 0U };
  uint64_t pk_y[5U] = { 0U };
  uint64_t r_q[4U] = { 0U };
  uint64_t s_q[4U] = { 0U };
  uint64_t z[4U] = { 0U };
  bool is_xy_on_curve = is_public_key_valid(public_key_x, public_key_y, pk_x, pk_y);
  bool is_r_valid = load_qelem_vartime(r_q, r);
  bool is_s_valid = load_qelem_vartime(s_q, s);
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
  uint64_t sinv[4U] = { 0U };
  uint64_t u1[4U] = { 0U };
  uint64_t u2[4U] = { 0U };
  qinv(sinv, s_q);
  qmul(u1, z, sinv);
  qmul(u2, r_q, sinv);
  point_mul_g_double_vartime(res, u1, u2, p);
  uint64_t tmp[5U] = { 0U };
  uint64_t *pz = res + (uint32_t)10U;
  fnormalize(tmp, pz);
  bool b = is_felem_zero_vartime(tmp);
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
  load_felem(r_fe, r_bytes);
  fnormalize(tmp_x, x);
  bool is_rz_x = fmul_eq_vartime(r_fe, z1, tmp_x);
  if (!is_rz_x)
  {
    bool is_r_lt_p_m_q = is_felem_lt_prime_minus_order_vartime(r_fe);
    if (is_r_lt_p_m_q)
    {
      tmp_q[0U] = (uint64_t)0x25e8cd0364141U;
      tmp_q[1U] = (uint64_t)0xe6af48a03bbfdU;
      tmp_q[2U] = (uint64_t)0xffffffebaaedcU;
      tmp_q[3U] = (uint64_t)0xfffffffffffffU;
      tmp_q[4U] = (uint64_t)0xffffffffffffU;
      fadd0(tmp_q, r_fe, tmp_q);
      return fmul_eq_vartime(tmp_q, z1, tmp_x);
    }
    return false;
  }
  return true;
}

inline bool
Hacl_K256_ECDSA_ecdsa_sign_sha256(
  uint8_t *r,
  uint8_t *s,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *k
)
{
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  bool b = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(r, s, mHash, private_key, k);
  return b;
}

inline bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key_x,
  uint8_t *public_key_y,
  uint8_t *r,
  uint8_t *s
)
{
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  bool b = Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(mHash, public_key_x, public_key_y, r, s);
  return b;
}

