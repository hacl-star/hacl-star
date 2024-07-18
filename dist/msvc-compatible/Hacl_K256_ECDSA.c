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
  uint64_t c0 = 0ULL;
  for (uint32_t i = 0U; i < bLen / 4U; i++)
  {
    uint64_t t1 = a0[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res0 + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a0[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res0 + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a0[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res0 + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a0[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res0 + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = bLen / 4U * 4U; i < bLen; i++)
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
    for (uint32_t i = 0U; i < (aLen - bLen) / 4U; i++)
    {
      uint64_t t1 = a1[4U * i];
      uint64_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, 0ULL, res_i0);
      uint64_t t10 = a1[4U * i + 1U];
      uint64_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, 0ULL, res_i1);
      uint64_t t11 = a1[4U * i + 2U];
      uint64_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, 0ULL, res_i2);
      uint64_t t12 = a1[4U * i + 3U];
      uint64_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, 0ULL, res_i);
    }
    for (uint32_t i = (aLen - bLen) / 4U * 4U; i < aLen - bLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, 0ULL, res_i);
    }
    uint64_t c1 = c;
    return c1;
  }
  return c00;
}

static uint64_t add4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = 0ULL;
  {
    uint64_t t1 = a[4U * 0U];
    uint64_t t20 = b[4U * 0U];
    uint64_t *res_i0 = res + 4U * 0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[4U * 0U + 1U];
    uint64_t t21 = b[4U * 0U + 1U];
    uint64_t *res_i1 = res + 4U * 0U + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[4U * 0U + 2U];
    uint64_t t22 = b[4U * 0U + 2U];
    uint64_t *res_i2 = res + 4U * 0U + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[4U * 0U + 3U];
    uint64_t t2 = b[4U * 0U + 3U];
    uint64_t *res_i = res + 4U * 0U + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  return c;
}

static void add_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  {
    uint64_t t1 = a[4U * 0U];
    uint64_t t20 = b[4U * 0U];
    uint64_t *res_i0 = res + 4U * 0U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[4U * 0U + 1U];
    uint64_t t21 = b[4U * 0U + 1U];
    uint64_t *res_i1 = res + 4U * 0U + 1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[4U * 0U + 2U];
    uint64_t t22 = b[4U * 0U + 2U];
    uint64_t *res_i2 = res + 4U * 0U + 2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[4U * 0U + 3U];
    uint64_t t2 = b[4U * 0U + 3U];
    uint64_t *res_i = res + 4U * 0U + 3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = 0ULL;
  {
    uint64_t t1 = res[4U * 0U];
    uint64_t t20 = n[4U * 0U];
    uint64_t *res_i0 = tmp + 4U * 0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * 0U + 1U];
    uint64_t t21 = n[4U * 0U + 1U];
    uint64_t *res_i1 = tmp + 4U * 0U + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * 0U + 2U];
    uint64_t t22 = n[4U * 0U + 2U];
    uint64_t *res_i2 = tmp + 4U * 0U + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * 0U + 3U];
    uint64_t t2 = n[4U * 0U + 3U];
    uint64_t *res_i = tmp + 4U * 0U + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;);
}

static void sub_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  {
    uint64_t t1 = a[4U * 0U];
    uint64_t t20 = b[4U * 0U];
    uint64_t *res_i0 = res + 4U * 0U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[4U * 0U + 1U];
    uint64_t t21 = b[4U * 0U + 1U];
    uint64_t *res_i1 = res + 4U * 0U + 1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[4U * 0U + 2U];
    uint64_t t22 = b[4U * 0U + 2U];
    uint64_t *res_i2 = res + 4U * 0U + 2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[4U * 0U + 3U];
    uint64_t t2 = b[4U * 0U + 3U];
    uint64_t *res_i = res + 4U * 0U + 3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[4U] = { 0U };
  uint64_t c = 0ULL;
  {
    uint64_t t1 = res[4U * 0U];
    uint64_t t20 = n[4U * 0U];
    uint64_t *res_i0 = tmp + 4U * 0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * 0U + 1U];
    uint64_t t21 = n[4U * 0U + 1U];
    uint64_t *res_i1 = tmp + 4U * 0U + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * 0U + 2U];
    uint64_t t22 = n[4U * 0U + 2U];
    uint64_t *res_i2 = tmp + 4U * 0U + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * 0U + 3U];
    uint64_t t2 = n[4U * 0U + 3U];
    uint64_t *res_i = tmp + 4U * 0U + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  uint64_t c1 = c;
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t c2 = 0ULL - c00;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = res;
    uint64_t x = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x;);
}

static void mul4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  memset(res, 0U, 8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    uint64_t bj = b[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = 0ULL;
    {
      uint64_t a_i = a[4U * 0U];
      uint64_t *res_i0 = res_j + 4U * 0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[4U * 0U + 1U];
      uint64_t *res_i1 = res_j + 4U * 0U + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[4U * 0U + 2U];
      uint64_t *res_i2 = res_j + 4U * 0U + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[4U * 0U + 3U];
      uint64_t *res_i = res_j + 4U * 0U + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    uint64_t r = c;
    res[4U + i0] = r;);
}

static void sqr4(uint64_t *a, uint64_t *res)
{
  memset(res, 0U, 8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = 0ULL;
    for (uint32_t i = 0U; i < i0 / 4U; i++)
    {
      uint64_t a_i = ab[4U * i];
      uint64_t *res_i0 = res_j + 4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[4U * i + 1U];
      uint64_t *res_i1 = res_j + 4U * i + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[4U * i + 2U];
      uint64_t *res_i2 = res_j + 4U * i + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[4U * i + 3U];
      uint64_t *res_i = res_j + 4U * i + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / 4U * 4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    res[i0 + i0] = r;);
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64(8U, res, res, res);
  KRML_MAYBE_UNUSED_VAR(c0);
  uint64_t tmp[8U] = { 0U };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, 64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[2U * i] = lo;
    tmp[2U * i + 1U] = hi;);
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(8U, res, tmp, res);
  KRML_MAYBE_UNUSED_VAR(c1);
}

static inline uint64_t is_qelem_zero(uint64_t *f)
{
  uint64_t bn_zero[4U] = { 0U };
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
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
  return f0 == 0ULL && f1 == 0ULL && f2 == 0ULL && f3 == 0ULL;
}

static inline uint64_t load_qelem_check(uint64_t *f, uint8_t *b)
{
  uint64_t n[4U] = { 0U };
  n[0U] = 0xbfd25e8cd0364141ULL;
  n[1U] = 0xbaaedce6af48a03bULL;
  n[2U] = 0xfffffffffffffffeULL;
  n[3U] = 0xffffffffffffffffULL;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = f;
    uint64_t u = load64_be(b + (4U - i - 1U) * 8U);
    uint64_t x = u;
    os[i] = x;);
  uint64_t is_zero = is_qelem_zero(f);
  uint64_t acc = 0ULL;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t beq = FStar_UInt64_eq_mask(f[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(f[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL))););
  uint64_t is_lt_q = acc;
  return ~is_zero & is_lt_q;
}

static inline bool load_qelem_vartime(uint64_t *f, uint8_t *b)
{
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = f;
    uint64_t u = load64_be(b + (4U - i - 1U) * 8U);
    uint64_t x = u;
    os[i] = x;);
  bool is_zero = is_qelem_zero_vartime(f);
  uint64_t a0 = f[0U];
  uint64_t a1 = f[1U];
  uint64_t a2 = f[2U];
  uint64_t a3 = f[3U];
  bool is_lt_q_b;
  if (a3 < 0xffffffffffffffffULL)
  {
    is_lt_q_b = true;
  }
  else if (a2 < 0xfffffffffffffffeULL)
  {
    is_lt_q_b = true;
  }
  else if (a2 > 0xfffffffffffffffeULL)
  {
    is_lt_q_b = false;
  }
  else if (a1 < 0xbaaedce6af48a03bULL)
  {
    is_lt_q_b = true;
  }
  else if (a1 > 0xbaaedce6af48a03bULL)
  {
    is_lt_q_b = false;
  }
  else
  {
    is_lt_q_b = a0 < 0xbfd25e8cd0364141ULL;
  }
  return !is_zero && is_lt_q_b;
}

static inline void modq_short(uint64_t *out, uint64_t *a)
{
  uint64_t tmp[4U] = { 0U };
  tmp[0U] = 0x402da1732fc9bebfULL;
  tmp[1U] = 0x4551231950b75fc4ULL;
  tmp[2U] = 0x1ULL;
  tmp[3U] = 0x0ULL;
  uint64_t c = add4(a, tmp, out);
  uint64_t mask = 0ULL - c;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = out;
    uint64_t x = (mask & out[i]) | (~mask & a[i]);
    os[i] = x;);
}

static inline void load_qelem_modq(uint64_t *f, uint8_t *b)
{
  uint64_t tmp[4U] = { 0U };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = f;
    uint64_t u = load64_be(b + (4U - i - 1U) * 8U);
    uint64_t x = u;
    os[i] = x;);
  memcpy(tmp, f, 4U * sizeof (uint64_t));
  modq_short(f, tmp);
}

static inline void store_qelem(uint8_t *b, uint64_t *f)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(tmp);
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, store64_be(b + i * 8U, f[4U - i - 1U]););
}

static inline void qadd(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t n[4U] = { 0U };
  n[0U] = 0xbfd25e8cd0364141ULL;
  n[1U] = 0xbaaedce6af48a03bULL;
  n[2U] = 0xfffffffffffffffeULL;
  n[3U] = 0xffffffffffffffffULL;
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
  KRML_CHECK_SIZE(sizeof (uint64_t), len + 2U);
  uint64_t *tmp = (uint64_t *)alloca((len + 2U) * sizeof (uint64_t));
  memset(tmp, 0U, (len + 2U) * sizeof (uint64_t));
  memset(tmp, 0U, (len + 2U) * sizeof (uint64_t));
  KRML_MAYBE_FOR2(i0,
    0U,
    2U,
    1U,
    uint64_t bj = t01[i0];
    uint64_t *res_j = tmp + i0;
    uint64_t c = 0ULL;
    for (uint32_t i = 0U; i < len / 4U; i++)
    {
      uint64_t a_i = a[4U * i];
      uint64_t *res_i0 = res_j + 4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[4U * i + 1U];
      uint64_t *res_i1 = res_j + 4U * i + 1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[4U * i + 2U];
      uint64_t *res_i2 = res_j + 4U * i + 2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[4U * i + 3U];
      uint64_t *res_i = res_j + 4U * i + 3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    for (uint32_t i = len / 4U * 4U; i < len; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    tmp[len + i0] = r;);
  memcpy(res + 2U, a, len * sizeof (uint64_t));
  bn_add(resLen, res, len + 2U, tmp, res);
  uint64_t c = bn_add(resLen, res, 4U, e, res);
  return c;
}

static inline void modq(uint64_t *out, uint64_t *a)
{
  uint64_t r[4U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  tmp[0U] = 0x402da1732fc9bebfULL;
  tmp[1U] = 0x4551231950b75fc4ULL;
  tmp[2U] = 0x1ULL;
  tmp[3U] = 0x0ULL;
  uint64_t *t01 = tmp;
  uint64_t m[7U] = { 0U };
  uint64_t p[5U] = { 0U };
  mul_pow2_256_minus_q_add(4U, 7U, t01, a + 4U, a, m);
  mul_pow2_256_minus_q_add(3U, 5U, t01, m + 4U, m, p);
  uint64_t c2 = mul_pow2_256_minus_q_add(1U, 4U, t01, p + 4U, p, r);
  uint64_t c0 = c2;
  uint64_t c1 = add4(r, tmp, out);
  uint64_t mask = 0ULL - (c0 + c1);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
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
  n[0U] = 0xbfd25e8cd0364141ULL;
  n[1U] = 0xbaaedce6af48a03bULL;
  n[2U] = 0xfffffffffffffffeULL;
  n[3U] = 0xffffffffffffffffULL;
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
  if (a3 < 0x7fffffffffffffffULL)
  {
    return true;
  }
  if (a3 > 0x7fffffffffffffffULL)
  {
    return false;
  }
  if (a2 < 0xffffffffffffffffULL)
  {
    return true;
  }
  if (a1 < 0x5d576e7357a4501dULL)
  {
    return true;
  }
  if (a1 > 0x5d576e7357a4501dULL)
  {
    return false;
  }
  return a0 <= 0xdfe92f46681b20a0ULL;
}

static inline void qmul_shift_384(uint64_t *res, uint64_t *a, uint64_t *b)
{
  uint64_t l[8U] = { 0U };
  mul4(a, b, l);
  uint64_t res_b_padded[4U] = { 0U };
  memcpy(res_b_padded, l + 6U, 2U * sizeof (uint64_t));
  uint64_t c0 = Lib_IntTypes_Intrinsics_add_carry_u64(0ULL, res_b_padded[0U], 1ULL, res);
  uint64_t *a1 = res_b_padded + 1U;
  uint64_t *res1 = res + 1U;
  uint64_t c = c0;
  KRML_MAYBE_FOR3(i,
    0U,
    3U,
    1U,
    uint64_t t1 = a1[i];
    uint64_t *res_i = res1 + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, 0ULL, res_i););
  uint64_t c1 = c;
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t flag = l[5U] >> 63U;
  uint64_t mask = 0ULL - flag;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = res;
    uint64_t x = (mask & res[i]) | (~mask & res_b_padded[i]);
    os[i] = x;);
}

static inline void qsquare_times_in_place(uint64_t *out, uint32_t b)
{
  for (uint32_t i = 0U; i < b; i++)
  {
    qsqr(out, out);
  }
}

static inline void qsquare_times(uint64_t *out, uint64_t *a, uint32_t b)
{
  memcpy(out, a, 4U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < b; i++)
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
  qsquare_times(x_10, f, 1U);
  qmul(x_11, x_10, f);
  qmul(x_101, x_10, x_11);
  qmul(x_111, x_10, x_101);
  qmul(x_1001, x_10, x_111);
  qmul(x_1011, x_10, x_1001);
  qmul(x_1101, x_10, x_1011);
  uint64_t x6[4U] = { 0U };
  uint64_t x8[4U] = { 0U };
  uint64_t x14[4U] = { 0U };
  qsquare_times(x6, x_1101, 2U);
  qmul(x6, x6, x_1011);
  qsquare_times(x8, x6, 2U);
  qmul(x8, x8, x_11);
  qsquare_times(x14, x8, 6U);
  qmul(x14, x14, x6);
  uint64_t x56[4U] = { 0U };
  qsquare_times(out, x14, 14U);
  qmul(out, out, x14);
  qsquare_times(x56, out, 28U);
  qmul(x56, x56, out);
  qsquare_times(out, x56, 56U);
  qmul(out, out, x56);
  qsquare_times_in_place(out, 14U);
  qmul(out, out, x14);
  qsquare_times_in_place(out, 3U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, 5U);
  qmul(out, out, x_1011);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_1011);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, 5U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, 6U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, 3U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, 5U);
  qmul(out, out, x_1001);
  qsquare_times_in_place(out, 6U);
  qmul(out, out, x_101);
  qsquare_times_in_place(out, 10U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_111);
  qsquare_times_in_place(out, 9U);
  qmul(out, out, x8);
  qsquare_times_in_place(out, 5U);
  qmul(out, out, x_1001);
  qsquare_times_in_place(out, 6U);
  qmul(out, out, x_1011);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, 5U);
  qmul(out, out, x_11);
  qsquare_times_in_place(out, 6U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, 10U);
  qmul(out, out, x_1101);
  qsquare_times_in_place(out, 4U);
  qmul(out, out, x_1001);
  qsquare_times_in_place(out, 6U);
  qmul(out, out, f);
  qsquare_times_in_place(out, 8U);
  qmul(out, out, x6);
}

void Hacl_Impl_K256_Point_make_point_at_inf(uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + 5U;
  uint64_t *pz = p + 10U;
  memset(px, 0U, 5U * sizeof (uint64_t));
  memset(py, 0U, 5U * sizeof (uint64_t));
  py[0U] = 1ULL;
  memset(pz, 0U, 5U * sizeof (uint64_t));
}

static inline void to_aff_point(uint64_t *p_aff, uint64_t *p)
{
  uint64_t *x = p_aff;
  uint64_t *y = p_aff + 5U;
  uint64_t *x1 = p;
  uint64_t *y1 = p + 5U;
  uint64_t *z1 = p + 10U;
  uint64_t zinv[5U] = { 0U };
  Hacl_Impl_K256_Finv_finv(zinv, z1);
  Hacl_K256_Field_fmul(x, x1, zinv);
  Hacl_K256_Field_fmul(y, y1, zinv);
  Hacl_K256_Field_fnormalize(x, x);
  Hacl_K256_Field_fnormalize(y, y);
}

static inline void to_aff_point_x(uint64_t *x, uint64_t *p)
{
  uint64_t *x1 = p;
  uint64_t *z1 = p + 10U;
  uint64_t zinv[5U] = { 0U };
  Hacl_Impl_K256_Finv_finv(zinv, z1);
  Hacl_K256_Field_fmul(x, x1, zinv);
  Hacl_K256_Field_fnormalize(x, x);
}

static inline bool is_on_curve_vartime(uint64_t *p)
{
  uint64_t y2_exp[5U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + 5U;
  uint64_t b[5U] = { 0U };
  b[0U] = 0x7ULL;
  b[1U] = 0ULL;
  b[2U] = 0ULL;
  b[3U] = 0ULL;
  b[4U] = 0ULL;
  Hacl_K256_Field_fsqr(y2_exp, x);
  Hacl_K256_Field_fmul(y2_exp, y2_exp, x);
  Hacl_K256_Field_fadd(y2_exp, y2_exp, b);
  Hacl_K256_Field_fnormalize(y2_exp, y2_exp);
  uint64_t y2_comp[5U] = { 0U };
  Hacl_K256_Field_fsqr(y2_comp, y);
  Hacl_K256_Field_fnormalize(y2_comp, y2_comp);
  bool res = Hacl_K256_Field_is_felem_eq_vartime(y2_exp, y2_comp);
  bool res0 = res;
  return res0;
}

void Hacl_Impl_K256_Point_point_negate(uint64_t *out, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + 5U;
  uint64_t *pz = p + 10U;
  uint64_t *ox = out;
  uint64_t *oy = out + 5U;
  uint64_t *oz = out + 10U;
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
  uint64_t r0 = 18014381329608892ULL - a0;
  uint64_t r1 = 18014398509481980ULL - a1;
  uint64_t r2 = 18014398509481980ULL - a2;
  uint64_t r3 = 18014398509481980ULL - a3;
  uint64_t r4 = 1125899906842620ULL - a4;
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

static inline void aff_point_store(uint8_t *out, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + 5U;
  Hacl_K256_Field_store_felem(out, px);
  Hacl_K256_Field_store_felem(out + 32U, py);
}

void Hacl_Impl_K256_Point_point_store(uint8_t *out, uint64_t *p)
{
  uint64_t p_aff[10U] = { 0U };
  to_aff_point(p_aff, p);
  aff_point_store(out, p_aff);
}

bool Hacl_Impl_K256_Point_aff_point_load_vartime(uint64_t *p, uint8_t *b)
{
  uint8_t *px = b;
  uint8_t *py = b + 32U;
  uint64_t *bn_px = p;
  uint64_t *bn_py = p + 5U;
  bool is_x_valid = Hacl_K256_Field_load_felem_lt_prime_vartime(bn_px, px);
  bool is_y_valid = Hacl_K256_Field_load_felem_lt_prime_vartime(bn_py, py);
  if (is_x_valid && is_y_valid)
  {
    return is_on_curve_vartime(p);
  }
  return false;
}

static inline bool load_point_vartime(uint64_t *p, uint8_t *b)
{
  uint64_t p_aff[10U] = { 0U };
  bool res = Hacl_Impl_K256_Point_aff_point_load_vartime(p_aff, b);
  if (res)
  {
    uint64_t *x = p_aff;
    uint64_t *y = p_aff + 5U;
    uint64_t *x1 = p;
    uint64_t *y1 = p + 5U;
    uint64_t *z1 = p + 10U;
    memcpy(x1, x, 5U * sizeof (uint64_t));
    memcpy(y1, y, 5U * sizeof (uint64_t));
    memset(z1, 0U, 5U * sizeof (uint64_t));
    z1[0U] = 1ULL;
  }
  return res;
}

static inline bool aff_point_decompress_vartime(uint64_t *x, uint64_t *y, uint8_t *s)
{
  uint8_t s0 = s[0U];
  uint8_t s01 = s0;
  if (!(s01 == 0x02U || s01 == 0x03U))
  {
    return false;
  }
  uint8_t *xb = s + 1U;
  bool is_x_valid = Hacl_K256_Field_load_felem_lt_prime_vartime(x, xb);
  bool is_y_odd = s01 == 0x03U;
  if (!is_x_valid)
  {
    return false;
  }
  uint64_t y2[5U] = { 0U };
  uint64_t b[5U] = { 0U };
  b[0U] = 0x7ULL;
  b[1U] = 0ULL;
  b[2U] = 0ULL;
  b[3U] = 0ULL;
  b[4U] = 0ULL;
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
  bool is_y_valid0 = is_y_valid;
  if (!is_y_valid0)
  {
    return false;
  }
  uint64_t x0 = y[0U];
  bool is_y_odd1 = (x0 & 1ULL) == 1ULL;
  Hacl_K256_Field_fnegate_conditional_vartime(y, is_y_odd1 != is_y_odd);
  return true;
}

void Hacl_Impl_K256_PointDouble_point_double(uint64_t *out, uint64_t *p)
{
  uint64_t tmp[25U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + 5U;
  uint64_t *z1 = p + 10U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + 5U;
  uint64_t *z3 = out + 10U;
  uint64_t *yy = tmp;
  uint64_t *zz = tmp + 5U;
  uint64_t *bzz3 = tmp + 10U;
  uint64_t *bzz9 = tmp + 15U;
  uint64_t *tmp1 = tmp + 20U;
  Hacl_K256_Field_fsqr(yy, y1);
  Hacl_K256_Field_fsqr(zz, z1);
  Hacl_K256_Field_fmul_small_num(x3, x1, 2ULL);
  Hacl_K256_Field_fmul(x3, x3, y1);
  Hacl_K256_Field_fmul(tmp1, yy, y1);
  Hacl_K256_Field_fmul(z3, tmp1, z1);
  Hacl_K256_Field_fmul_small_num(z3, z3, 8ULL);
  Hacl_K256_Field_fnormalize_weak(z3, z3);
  Hacl_K256_Field_fmul_small_num(bzz3, zz, 21ULL);
  Hacl_K256_Field_fnormalize_weak(bzz3, bzz3);
  Hacl_K256_Field_fmul_small_num(bzz9, bzz3, 3ULL);
  Hacl_K256_Field_fsub(bzz9, yy, bzz9, 6ULL);
  Hacl_K256_Field_fadd(tmp1, yy, bzz3);
  Hacl_K256_Field_fmul(tmp1, bzz9, tmp1);
  Hacl_K256_Field_fmul(y3, yy, zz);
  Hacl_K256_Field_fmul(x3, x3, bzz9);
  Hacl_K256_Field_fmul_small_num(y3, y3, 168ULL);
  Hacl_K256_Field_fadd(y3, tmp1, y3);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
}

void Hacl_Impl_K256_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q)
{
  uint64_t tmp[45U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + 5U;
  uint64_t *z1 = p + 10U;
  uint64_t *x2 = q;
  uint64_t *y2 = q + 5U;
  uint64_t *z2 = q + 10U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + 5U;
  uint64_t *z3 = out + 10U;
  uint64_t *xx = tmp;
  uint64_t *yy = tmp + 5U;
  uint64_t *zz = tmp + 10U;
  uint64_t *xy_pairs = tmp + 15U;
  uint64_t *yz_pairs = tmp + 20U;
  uint64_t *xz_pairs = tmp + 25U;
  uint64_t *yy_m_bzz3 = tmp + 30U;
  uint64_t *yy_p_bzz3 = tmp + 35U;
  uint64_t *tmp1 = tmp + 40U;
  Hacl_K256_Field_fmul(xx, x1, x2);
  Hacl_K256_Field_fmul(yy, y1, y2);
  Hacl_K256_Field_fmul(zz, z1, z2);
  Hacl_K256_Field_fadd(xy_pairs, x1, y1);
  Hacl_K256_Field_fadd(tmp1, x2, y2);
  Hacl_K256_Field_fmul(xy_pairs, xy_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, xx, yy);
  Hacl_K256_Field_fsub(xy_pairs, xy_pairs, tmp1, 4ULL);
  Hacl_K256_Field_fadd(yz_pairs, y1, z1);
  Hacl_K256_Field_fadd(tmp1, y2, z2);
  Hacl_K256_Field_fmul(yz_pairs, yz_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, yy, zz);
  Hacl_K256_Field_fsub(yz_pairs, yz_pairs, tmp1, 4ULL);
  Hacl_K256_Field_fadd(xz_pairs, x1, z1);
  Hacl_K256_Field_fadd(tmp1, x2, z2);
  Hacl_K256_Field_fmul(xz_pairs, xz_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, xx, zz);
  Hacl_K256_Field_fsub(xz_pairs, xz_pairs, tmp1, 4ULL);
  Hacl_K256_Field_fmul_small_num(tmp1, zz, 21ULL);
  Hacl_K256_Field_fnormalize_weak(tmp1, tmp1);
  Hacl_K256_Field_fsub(yy_m_bzz3, yy, tmp1, 2ULL);
  Hacl_K256_Field_fadd(yy_p_bzz3, yy, tmp1);
  Hacl_K256_Field_fmul_small_num(x3, yz_pairs, 21ULL);
  Hacl_K256_Field_fnormalize_weak(x3, x3);
  Hacl_K256_Field_fmul_small_num(z3, xx, 3ULL);
  Hacl_K256_Field_fmul_small_num(y3, z3, 21ULL);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
  Hacl_K256_Field_fmul(tmp1, xy_pairs, yy_m_bzz3);
  Hacl_K256_Field_fmul(x3, x3, xz_pairs);
  Hacl_K256_Field_fsub(x3, tmp1, x3, 2ULL);
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
  tmp1[0U] = 0xe893209a45dbb031ULL;
  tmp1[1U] = 0x3daa8a1471e8ca7fULL;
  tmp1[2U] = 0xe86c90e49284eb15ULL;
  tmp1[3U] = 0x3086d221a7d46bcdULL;
  tmp2[0U] = 0x1571b4ae8ac47f71ULL;
  tmp2[1U] = 0x221208ac9df506c6ULL;
  tmp2[2U] = 0x6f547fa90abfe4c4ULL;
  tmp2[3U] = 0xe4437ed6010e8828ULL;
  qmul_shift_384(r1, k, tmp1);
  qmul_shift_384(r2, k, tmp2);
  tmp1[0U] = 0x6f547fa90abfe4c3ULL;
  tmp1[1U] = 0xe4437ed6010e8828ULL;
  tmp1[2U] = 0x0ULL;
  tmp1[3U] = 0x0ULL;
  tmp2[0U] = 0xd765cda83db1562cULL;
  tmp2[1U] = 0x8a280ac50774346dULL;
  tmp2[2U] = 0xfffffffffffffffeULL;
  tmp2[3U] = 0xffffffffffffffffULL;
  qmul(r1, r1, tmp1);
  qmul(r2, r2, tmp2);
  tmp1[0U] = 0xe0cfc810b51283cfULL;
  tmp1[1U] = 0xa880b9fc8ec739c2ULL;
  tmp1[2U] = 0x5ad9e3fd77ed9ba4ULL;
  tmp1[3U] = 0xac9c52b33fa3cf1fULL;
  qadd(r2, r1, r2);
  qmul(tmp2, r2, tmp1);
  qadd(r1, k, tmp2);
}

static inline void point_mul_lambda(uint64_t *res, uint64_t *p)
{
  uint64_t *rx = res;
  uint64_t *ry = res + 5U;
  uint64_t *rz = res + 10U;
  uint64_t *px = p;
  uint64_t *py = p + 5U;
  uint64_t *pz = p + 10U;
  uint64_t beta[5U] = { 0U };
  beta[0U] = 0x96c28719501eeULL;
  beta[1U] = 0x7512f58995c13ULL;
  beta[2U] = 0xc3434e99cf049ULL;
  beta[3U] = 0x7106e64479eaULL;
  beta[4U] = 0x7ae96a2b657cULL;
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
  beta[0U] = 0x96c28719501eeULL;
  beta[1U] = 0x7512f58995c13ULL;
  beta[2U] = 0xc3434e99cf049ULL;
  beta[3U] = 0x7106e64479eaULL;
  beta[4U] = 0x7ae96a2b657cULL;
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
  memcpy(q1, q, 15U * sizeof (uint64_t));
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
  uint64_t *t1 = table + 15U;
  Hacl_Impl_K256_Point_make_point_at_inf(t0);
  memcpy(t1, q, 15U * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint64_t *t11 = table + (i + 1U) * 15U;
    Hacl_Impl_K256_PointDouble_point_double(tmp, t11);
    memcpy(table + (2U * i + 2U) * 15U, tmp, 15U * sizeof (uint64_t));
    uint64_t *t2 = table + (2U * i + 2U) * 15U;
    Hacl_Impl_K256_PointAdd_point_add(tmp, q, t2);
    memcpy(table + (2U * i + 3U) * 15U, tmp, 15U * sizeof (uint64_t)););
  Hacl_Impl_K256_Point_make_point_at_inf(out);
  uint64_t tmp0[15U] = { 0U };
  for (uint32_t i0 = 0U; i0 < 64U; i0++)
  {
    KRML_MAYBE_FOR4(i, 0U, 4U, 1U, Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t k = 256U - 4U * i0 - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar, k, 4U);
    memcpy(tmp0, (uint64_t *)table, 15U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i1 + 1U));
      const uint64_t *res_j = table + (i1 + 1U) * 15U;
      KRML_MAYBE_FOR15(i,
        0U,
        15U,
        1U,
        uint64_t *os = tmp0;
        uint64_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;););
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp0);
  }
}

static inline void precomp_get_consttime(const uint64_t *table, uint64_t bits_l, uint64_t *tmp)
{
  memcpy(tmp, (uint64_t *)table, 15U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i0,
    0U,
    15U,
    1U,
    uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i0 + 1U));
    const uint64_t *res_j = table + (i0 + 1U) * 15U;
    KRML_MAYBE_FOR15(i,
      0U,
      15U,
      1U,
      uint64_t *os = tmp;
      uint64_t x = (c & res_j[i]) | (~c & tmp[i]);
      os[i] = x;););
}

static inline void point_mul_g(uint64_t *out, uint64_t *scalar)
{
  uint64_t q1[15U] = { 0U };
  uint64_t *gx = q1;
  uint64_t *gy = q1 + 5U;
  uint64_t *gz = q1 + 10U;
  gx[0U] = 0x2815b16f81798ULL;
  gx[1U] = 0xdb2dce28d959fULL;
  gx[2U] = 0xe870b07029bfcULL;
  gx[3U] = 0xbbac55a06295cULL;
  gx[4U] = 0x79be667ef9dcULL;
  gy[0U] = 0x7d08ffb10d4b8ULL;
  gy[1U] = 0x48a68554199c4ULL;
  gy[2U] = 0xe1108a8fd17b4ULL;
  gy[3U] = 0xc4655da4fbfc0ULL;
  gy[4U] = 0x483ada7726a3ULL;
  memset(gz, 0U, 5U * sizeof (uint64_t));
  gz[0U] = 1ULL;
  uint64_t
  q2[15U] =
    {
      4496295042185355ULL, 3125448202219451ULL, 1239608518490046ULL, 2687445637493112ULL,
      77979604880139ULL, 3360310474215011ULL, 1216410458165163ULL, 177901593587973ULL,
      3209978938104985ULL, 118285133003718ULL, 434519962075150ULL, 1114612377498854ULL,
      3488596944003813ULL, 450716531072892ULL, 66044973203836ULL
    };
  KRML_MAYBE_UNUSED_VAR(q2);
  uint64_t
  q3[15U] =
    {
      1277614565900951ULL, 378671684419493ULL, 3176260448102880ULL, 1575691435565077ULL,
      167304528382180ULL, 2600787765776588ULL, 7497946149293ULL, 2184272641272202ULL,
      2200235265236628ULL, 265969268774814ULL, 1913228635640715ULL, 2831959046949342ULL,
      888030405442963ULL, 1817092932985033ULL, 101515844997121ULL
    };
  KRML_MAYBE_UNUSED_VAR(q3);
  uint64_t
  q4[15U] =
    {
      34056422761564ULL, 3315864838337811ULL, 3797032336888745ULL, 2580641850480806ULL,
      208048944042500ULL, 1233795288689421ULL, 1048795233382631ULL, 646545158071530ULL,
      1816025742137285ULL, 12245672982162ULL, 2119364213800870ULL, 2034960311715107ULL,
      3172697815804487ULL, 4185144850224160ULL, 2792055915674ULL
    };
  KRML_MAYBE_UNUSED_VAR(q4);
  uint64_t *r1 = scalar;
  uint64_t *r2 = scalar + 1U;
  uint64_t *r3 = scalar + 2U;
  uint64_t *r4 = scalar + 3U;
  Hacl_Impl_K256_Point_make_point_at_inf(out);
  uint64_t tmp[15U] = { 0U };
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    KRML_MAYBE_FOR4(i0, 0U, 4U, 1U, Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t k = 64U - 4U * i - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r4, k, 4U);
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4, bits_l, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp);
    uint32_t k0 = 64U - 4U * i - 4U;
    uint64_t bits_l0 = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r3, k0, 4U);
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4, bits_l0, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp);
    uint32_t k1 = 64U - 4U * i - 4U;
    uint64_t bits_l1 = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r2, k1, 4U);
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4, bits_l1, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp);
    uint32_t k2 = 64U - 4U * i - 4U;
    uint64_t bits_l2 = Hacl_Bignum_Lib_bn_get_bits_u64(1U, r1, k2, 4U);
    precomp_get_consttime(Hacl_K256_PrecompTable_precomp_basepoint_table_w4, bits_l2, tmp);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp););
}

static inline void
point_mul_g_double_vartime(uint64_t *out, uint64_t *scalar1, uint64_t *scalar2, uint64_t *q2)
{
  uint64_t q1[15U] = { 0U };
  uint64_t *gx = q1;
  uint64_t *gy = q1 + 5U;
  uint64_t *gz = q1 + 10U;
  gx[0U] = 0x2815b16f81798ULL;
  gx[1U] = 0xdb2dce28d959fULL;
  gx[2U] = 0xe870b07029bfcULL;
  gx[3U] = 0xbbac55a06295cULL;
  gx[4U] = 0x79be667ef9dcULL;
  gy[0U] = 0x7d08ffb10d4b8ULL;
  gy[1U] = 0x48a68554199c4ULL;
  gy[2U] = 0xe1108a8fd17b4ULL;
  gy[3U] = 0xc4655da4fbfc0ULL;
  gy[4U] = 0x483ada7726a3ULL;
  memset(gz, 0U, 5U * sizeof (uint64_t));
  gz[0U] = 1ULL;
  uint64_t table2[480U] = { 0U };
  uint64_t tmp[15U] = { 0U };
  uint64_t *t0 = table2;
  uint64_t *t1 = table2 + 15U;
  Hacl_Impl_K256_Point_make_point_at_inf(t0);
  memcpy(t1, q2, 15U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    0U,
    15U,
    1U,
    uint64_t *t11 = table2 + (i + 1U) * 15U;
    Hacl_Impl_K256_PointDouble_point_double(tmp, t11);
    memcpy(table2 + (2U * i + 2U) * 15U, tmp, 15U * sizeof (uint64_t));
    uint64_t *t2 = table2 + (2U * i + 2U) * 15U;
    Hacl_Impl_K256_PointAdd_point_add(tmp, q2, t2);
    memcpy(table2 + (2U * i + 3U) * 15U, tmp, 15U * sizeof (uint64_t)););
  uint64_t tmp0[15U] = { 0U };
  uint32_t i0 = 255U;
  uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar1, i0, 5U);
  uint32_t bits_l32 = (uint32_t)bits_c;
  const uint64_t *a_bits_l = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l32 * 15U;
  memcpy(out, (uint64_t *)a_bits_l, 15U * sizeof (uint64_t));
  uint32_t i1 = 255U;
  uint64_t bits_c0 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar2, i1, 5U);
  uint32_t bits_l320 = (uint32_t)bits_c0;
  const uint64_t *a_bits_l0 = table2 + bits_l320 * 15U;
  memcpy(tmp0, (uint64_t *)a_bits_l0, 15U * sizeof (uint64_t));
  Hacl_Impl_K256_PointAdd_point_add(out, out, tmp0);
  uint64_t tmp1[15U] = { 0U };
  for (uint32_t i = 0U; i < 51U; i++)
  {
    KRML_MAYBE_FOR5(i2, 0U, 5U, 1U, Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t k = 255U - 5U * i - 5U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar2, k, 5U);
    uint32_t bits_l321 = (uint32_t)bits_l;
    const uint64_t *a_bits_l1 = table2 + bits_l321 * 15U;
    memcpy(tmp1, (uint64_t *)a_bits_l1, 15U * sizeof (uint64_t));
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp1);
    uint32_t k0 = 255U - 5U * i - 5U;
    uint64_t bits_l0 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, scalar1, k0, 5U);
    uint32_t bits_l322 = (uint32_t)bits_l0;
    const
    uint64_t
    *a_bits_l2 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l322 * 15U;
    memcpy(tmp1, (uint64_t *)a_bits_l2, 15U * sizeof (uint64_t));
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
  uint64_t *t1 = table2 + 15U;
  Hacl_Impl_K256_Point_make_point_at_inf(t0);
  memcpy(t1, p2, 15U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    0U,
    15U,
    1U,
    uint64_t *t11 = table2 + (i + 1U) * 15U;
    Hacl_Impl_K256_PointDouble_point_double(tmp, t11);
    memcpy(table2 + (2U * i + 2U) * 15U, tmp, 15U * sizeof (uint64_t));
    uint64_t *t2 = table2 + (2U * i + 2U) * 15U;
    Hacl_Impl_K256_PointAdd_point_add(tmp, p2, t2);
    memcpy(table2 + (2U * i + 3U) * 15U, tmp, 15U * sizeof (uint64_t)););
  uint64_t tmp0[15U] = { 0U };
  uint64_t tmp1[15U] = { 0U };
  uint32_t i0 = 125U;
  uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r1, i0, 5U);
  uint32_t bits_l32 = (uint32_t)bits_c;
  const uint64_t *a_bits_l = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l32 * 15U;
  memcpy(out, (uint64_t *)a_bits_l, 15U * sizeof (uint64_t));
  point_negate_conditional_vartime(out, is_negate1);
  uint32_t i1 = 125U;
  uint64_t bits_c0 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r2, i1, 5U);
  uint32_t bits_l320 = (uint32_t)bits_c0;
  const
  uint64_t
  *a_bits_l0 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l320 * 15U;
  memcpy(tmp1, (uint64_t *)a_bits_l0, 15U * sizeof (uint64_t));
  point_negate_conditional_vartime(tmp1, is_negate2);
  point_mul_lambda_inplace(tmp1);
  Hacl_Impl_K256_PointAdd_point_add(out, out, tmp1);
  uint64_t tmp10[15U] = { 0U };
  uint32_t i2 = 125U;
  uint64_t bits_c1 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r3, i2, 5U);
  uint32_t bits_l321 = (uint32_t)bits_c1;
  const uint64_t *a_bits_l1 = table2 + bits_l321 * 15U;
  memcpy(tmp0, (uint64_t *)a_bits_l1, 15U * sizeof (uint64_t));
  point_negate_conditional_vartime(tmp0, is_negate3);
  uint32_t i3 = 125U;
  uint64_t bits_c2 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r4, i3, 5U);
  uint32_t bits_l322 = (uint32_t)bits_c2;
  const uint64_t *a_bits_l2 = table2 + bits_l322 * 15U;
  memcpy(tmp10, (uint64_t *)a_bits_l2, 15U * sizeof (uint64_t));
  point_negate_conditional_vartime(tmp10, is_negate4);
  point_mul_lambda_inplace(tmp10);
  Hacl_Impl_K256_PointAdd_point_add(tmp0, tmp0, tmp10);
  Hacl_Impl_K256_PointAdd_point_add(out, out, tmp0);
  uint64_t tmp2[15U] = { 0U };
  for (uint32_t i = 0U; i < 25U; i++)
  {
    KRML_MAYBE_FOR5(i4, 0U, 5U, 1U, Hacl_Impl_K256_PointDouble_point_double(out, out););
    uint32_t k = 125U - 5U * i - 5U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r4, k, 5U);
    uint32_t bits_l323 = (uint32_t)bits_l;
    const uint64_t *a_bits_l3 = table2 + bits_l323 * 15U;
    memcpy(tmp2, (uint64_t *)a_bits_l3, 15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate4);
    point_mul_lambda_inplace(tmp2);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
    uint32_t k0 = 125U - 5U * i - 5U;
    uint64_t bits_l0 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r3, k0, 5U);
    uint32_t bits_l324 = (uint32_t)bits_l0;
    const uint64_t *a_bits_l4 = table2 + bits_l324 * 15U;
    memcpy(tmp2, (uint64_t *)a_bits_l4, 15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate3);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
    uint32_t k1 = 125U - 5U * i - 5U;
    uint64_t bits_l1 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r2, k1, 5U);
    uint32_t bits_l325 = (uint32_t)bits_l1;
    const
    uint64_t
    *a_bits_l5 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l325 * 15U;
    memcpy(tmp2, (uint64_t *)a_bits_l5, 15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate2);
    point_mul_lambda_inplace(tmp2);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
    uint32_t k2 = 125U - 5U * i - 5U;
    uint64_t bits_l2 = Hacl_Bignum_Lib_bn_get_bits_u64(4U, r1, k2, 5U);
    uint32_t bits_l326 = (uint32_t)bits_l2;
    const
    uint64_t
    *a_bits_l6 = Hacl_K256_PrecompTable_precomp_basepoint_table_w5 + bits_l326 * 15U;
    memcpy(tmp2, (uint64_t *)a_bits_l6, 15U * sizeof (uint64_t));
    point_negate_conditional_vartime(tmp2, is_negate1);
    Hacl_Impl_K256_PointAdd_point_add(out, out, tmp2);
  }
}

static inline bool
check_ecmult_endo_split(uint64_t *r1, uint64_t *r2, uint64_t *r3, uint64_t *r4)
{
  uint64_t f20 = r1[2U];
  uint64_t f30 = r1[3U];
  bool b1 = f20 == 0ULL && f30 == 0ULL;
  uint64_t f21 = r2[2U];
  uint64_t f31 = r2[3U];
  bool b2 = f21 == 0ULL && f31 == 0ULL;
  uint64_t f22 = r3[2U];
  uint64_t f32 = r3[3U];
  bool b3 = f22 == 0ULL && f32 == 0ULL;
  uint64_t f2 = r4[2U];
  uint64_t f3 = r4[3U];
  bool b4 = f2 == 0ULL && f3 == 0ULL;
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
  uint64_t *gy = g + 5U;
  uint64_t *gz = g + 10U;
  gx[0U] = 0x2815b16f81798ULL;
  gx[1U] = 0xdb2dce28d959fULL;
  gx[2U] = 0xe870b07029bfcULL;
  gx[3U] = 0xbbac55a06295cULL;
  gx[4U] = 0x79be667ef9dcULL;
  gy[0U] = 0x7d08ffb10d4b8ULL;
  gy[1U] = 0x48a68554199c4ULL;
  gy[2U] = 0xe1108a8fd17b4ULL;
  gy[3U] = 0xc4655da4fbfc0ULL;
  gy[4U] = 0x483ada7726a3ULL;
  memset(gz, 0U, 5U * sizeof (uint64_t));
  gz[0U] = 1ULL;
  uint64_t r1234[16U] = { 0U };
  uint64_t q1234[60U] = { 0U };
  uint64_t *r1 = r1234;
  uint64_t *r2 = r1234 + 4U;
  uint64_t *r3 = r1234 + 8U;
  uint64_t *r4 = r1234 + 12U;
  uint64_t *q1 = q1234;
  uint64_t *q2 = q1234 + 15U;
  uint64_t *q3 = q1234 + 30U;
  uint64_t *q4 = q1234 + 45U;
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

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t oneq[4U] = { 0x1ULL, 0x0ULL, 0x0ULL, 0x0ULL };
  KRML_MAYBE_UNUSED_VAR(oneq);
  uint64_t rsdk_q[16U] = { 0U };
  uint64_t *r_q = rsdk_q;
  uint64_t *s_q = rsdk_q + 4U;
  uint64_t *d_a = rsdk_q + 8U;
  uint64_t *k_q = rsdk_q + 12U;
  uint64_t is_b_valid0 = load_qelem_check(d_a, private_key);
  uint64_t oneq10[4U] = { 0x1ULL, 0x0ULL, 0x0ULL, 0x0ULL };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = d_a;
    uint64_t uu____0 = oneq10[i];
    uint64_t x = uu____0 ^ (is_b_valid0 & (d_a[i] ^ uu____0));
    os[i] = x;);
  uint64_t is_sk_valid = is_b_valid0;
  uint64_t is_b_valid = load_qelem_check(k_q, nonce);
  uint64_t oneq1[4U] = { 0x1ULL, 0x0ULL, 0x0ULL, 0x0ULL };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = k_q;
    uint64_t uu____1 = oneq1[i];
    uint64_t x = uu____1 ^ (is_b_valid & (k_q[i] ^ uu____1));
    os[i] = x;);
  uint64_t is_nonce_valid = is_b_valid;
  uint64_t are_sk_nonce_valid = is_sk_valid & is_nonce_valid;
  uint64_t tmp[5U] = { 0U };
  uint8_t x_bytes[32U] = { 0U };
  uint64_t p[15U] = { 0U };
  point_mul_g(p, k_q);
  to_aff_point_x(tmp, p);
  Hacl_K256_Field_store_felem(x_bytes, tmp);
  load_qelem_modq(r_q, x_bytes);
  uint64_t z[4U] = { 0U };
  uint64_t kinv[4U] = { 0U };
  load_qelem_modq(z, msgHash);
  qinv(kinv, k_q);
  qmul(s_q, r_q, d_a);
  qadd(s_q, z, s_q);
  qmul(s_q, kinv, s_q);
  store_qelem(signature, r_q);
  store_qelem(signature + 32U, s_q);
  uint64_t is_r_zero = is_qelem_zero(r_q);
  uint64_t is_s_zero = is_qelem_zero(s_q);
  uint64_t m = are_sk_nonce_valid & (~is_r_zero & ~is_s_zero);
  bool res = m == 0xFFFFFFFFFFFFFFFFULL;
  return res;
}

/**
Create an ECDSA signature using SHA2-256.

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
  Hacl_Hash_SHA2_hash_256(msgHash, msg, msg_len);
  bool b = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  return b;
}

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether `public key` is valid.
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(uint8_t *m, uint8_t *public_key, uint8_t *signature)
{
  uint64_t tmp[35U] = { 0U };
  uint64_t *pk = tmp;
  uint64_t *r_q = tmp + 15U;
  uint64_t *s_q = tmp + 19U;
  uint64_t *u1 = tmp + 23U;
  uint64_t *u2 = tmp + 27U;
  uint64_t *m_q = tmp + 31U;
  bool is_pk_valid = load_point_vartime(pk, public_key);
  bool is_r_valid = load_qelem_vartime(r_q, signature);
  bool is_s_valid = load_qelem_vartime(s_q, signature + 32U);
  bool is_rs_valid = is_r_valid && is_s_valid;
  load_qelem_modq(m_q, m);
  if (!(is_pk_valid && is_rs_valid))
  {
    return false;
  }
  uint64_t sinv[4U] = { 0U };
  qinv(sinv, s_q);
  qmul(u1, m_q, sinv);
  qmul(u2, r_q, sinv);
  uint64_t res[15U] = { 0U };
  point_mul_g_double_split_lambda_vartime(res, u1, u2, pk);
  uint64_t tmp1[5U] = { 0U };
  uint64_t *pz = res + 10U;
  Hacl_K256_Field_fnormalize(tmp1, pz);
  bool b = Hacl_K256_Field_is_felem_zero_vartime(tmp1);
  if (b)
  {
    return false;
  }
  uint64_t *x = res;
  uint64_t *z = res + 10U;
  uint8_t r_bytes[32U] = { 0U };
  uint64_t r_fe[5U] = { 0U };
  uint64_t tmp_q[5U] = { 0U };
  uint64_t tmp_x[5U] = { 0U };
  store_qelem(r_bytes, r_q);
  Hacl_K256_Field_load_felem(r_fe, r_bytes);
  Hacl_K256_Field_fnormalize(tmp_x, x);
  bool is_rz_x = fmul_eq_vartime(r_fe, z, tmp_x);
  if (!is_rz_x)
  {
    bool is_r_lt_p_m_q = Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime(r_fe);
    if (is_r_lt_p_m_q)
    {
      tmp_q[0U] = 0x25e8cd0364141ULL;
      tmp_q[1U] = 0xe6af48a03bbfdULL;
      tmp_q[2U] = 0xffffffebaaedcULL;
      tmp_q[3U] = 0xfffffffffffffULL;
      tmp_q[4U] = 0xffffffffffffULL;
      Hacl_K256_Field_fadd(tmp_q, r_fe, tmp_q);
      return fmul_eq_vartime(tmp_q, z, tmp_x);
    }
    return false;
  }
  return true;
}

/**
Verify an ECDSA signature using SHA2-256.

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
  Hacl_Hash_SHA2_hash_256(mHash, msg, msg_len);
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
  uint8_t *s = signature + 32U;
  bool is_sk_valid = load_qelem_vartime(s_q, s);
  if (!is_sk_valid)
  {
    return false;
  }
  bool is_sk_lt_q_halved = is_qelem_le_q_halved_vartime(s_q);
  qnegate_conditional_vartime(s_q, !is_sk_lt_q_halved);
  store_qelem(signature + 32U, s_q);
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
  uint8_t *s = signature + 32U;
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

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
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
Create an ECDSA signature using SHA2-256.

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
  Hacl_Hash_SHA2_hash_256(msgHash, msg, msg_len);
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

  The function also checks whether `public_key` is valid
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
Verify an ECDSA signature using SHA2-256.

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
  Hacl_Hash_SHA2_hash_256(mHash, msg, msg_len);
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
  if (pk0 != 0x04U)
  {
    return false;
  }
  memcpy(pk_raw, pk + 1U, 64U * sizeof (uint8_t));
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
  pk[0U] = 0x04U;
  memcpy(pk + 1U, pk_raw, 64U * sizeof (uint8_t));
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
  uint8_t *pk_xb = pk + 1U;
  bool b = aff_point_decompress_vartime(xa, ya, pk);
  if (b)
  {
    memcpy(pk_raw, pk_xb, 32U * sizeof (uint8_t));
    Hacl_K256_Field_store_felem(pk_raw + 32U, ya);
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
  uint8_t *pk_y = pk_raw + 32U;
  uint8_t x0 = pk_y[31U];
  bool is_pk_y_odd = ((uint32_t)x0 & 1U) == 1U;
  uint8_t ite;
  if (is_pk_y_odd)
  {
    ite = 0x03U;
  }
  else
  {
    ite = 0x02U;
  }
  pk[0U] = ite;
  memcpy(pk + 1U, pk_x, 32U * sizeof (uint8_t));
}


/******************/
/* Key validation */
/******************/

/**
Public key validation.

  The function returns `true` if a public key is valid and `false` otherwise.

  The argument `public_key` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The public key (x || y) is valid (with respect to SP 800-56A):
    • the public key is not the “point at infinity”, represented as O.
    • the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_K256_ECDSA_is_public_key_valid(uint8_t *public_key)
{
  uint64_t p[15U] = { 0U };
  bool is_pk_valid = load_point_vartime(p, public_key);
  return is_pk_valid;
}

/**
Private key validation.

  The function returns `true` if a private key is valid and `false` otherwise.

  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve
*/
bool Hacl_K256_ECDSA_is_private_key_valid(uint8_t *private_key)
{
  uint64_t s_q[4U] = { 0U };
  uint64_t res = load_qelem_check(s_q, private_key);
  return res == 0xFFFFFFFFFFFFFFFFULL;
}


/******************/
/* ECDH agreement */
/******************/

/**
Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve.
*/
bool Hacl_K256_ECDSA_secret_to_public(uint8_t *public_key, uint8_t *private_key)
{
  uint64_t tmp[19U] = { 0U };
  uint64_t *pk = tmp;
  uint64_t *sk = tmp + 15U;
  uint64_t is_b_valid = load_qelem_check(sk, private_key);
  uint64_t oneq[4U] = { 0x1ULL, 0x0ULL, 0x0ULL, 0x0ULL };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = sk;
    uint64_t uu____0 = oneq[i];
    uint64_t x = uu____0 ^ (is_b_valid & (sk[i] ^ uu____0));
    os[i] = x;);
  uint64_t is_sk_valid = is_b_valid;
  point_mul_g(pk, sk);
  Hacl_Impl_K256_Point_point_store(public_key, pk);
  return is_sk_valid == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Execute the diffie-hellmann key exchange.

  The function returns `true` for successful creation of an ECDH shared secret and
  `false` otherwise.

  The outparam `shared_secret` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `their_pubkey` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `their_pubkey` are valid.
*/
bool Hacl_K256_ECDSA_ecdh(uint8_t *shared_secret, uint8_t *their_pubkey, uint8_t *private_key)
{
  uint64_t tmp[34U] = { 0U };
  uint64_t *pk = tmp;
  uint64_t *ss = tmp + 15U;
  uint64_t *sk = tmp + 30U;
  bool is_pk_valid = load_point_vartime(pk, their_pubkey);
  uint64_t is_b_valid = load_qelem_check(sk, private_key);
  uint64_t oneq[4U] = { 0x1ULL, 0x0ULL, 0x0ULL, 0x0ULL };
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = sk;
    uint64_t uu____0 = oneq[i];
    uint64_t x = uu____0 ^ (is_b_valid & (sk[i] ^ uu____0));
    os[i] = x;);
  uint64_t is_sk_valid = is_b_valid;
  if (is_pk_valid)
  {
    Hacl_Impl_K256_PointMul_point_mul(ss, sk, pk);
    Hacl_Impl_K256_Point_point_store(shared_secret, ss);
  }
  return is_sk_valid == 0xFFFFFFFFFFFFFFFFULL && is_pk_valid;
}

