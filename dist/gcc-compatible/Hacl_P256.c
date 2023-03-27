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


#include "internal/Hacl_P256.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
#include "lib_intrinsics.h"

static inline bool bn_is_zero_vartime4(uint64_t *f)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  return f0 == (uint64_t)0U && f1 == (uint64_t)0U && f2 == (uint64_t)0U && f3 == (uint64_t)0U;
}

static inline uint64_t bn_is_zero_mask4(uint64_t *f)
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

static inline bool bn_is_eq_vartime4(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[0U];
  uint64_t a1 = a[1U];
  uint64_t a2 = a[2U];
  uint64_t a3 = a[3U];
  uint64_t b0 = b[0U];
  uint64_t b1 = b[1U];
  uint64_t b2 = b[2U];
  uint64_t b3 = b[3U];
  return a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3;
}

static inline uint64_t bn_is_eq_mask4(uint64_t *a, uint64_t *b)
{
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], b[i]);
    mask = uu____0 & mask;);
  uint64_t mask1 = mask;
  return mask1;
}

static inline void bn_copy_conditional4(uint64_t *res, uint64_t mask, uint64_t *x, uint64_t *y)
{
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = res;
    uint64_t uu____0 = x[i];
    uint64_t x1 = uu____0 ^ (mask & (y[i] ^ uu____0));
    os[i] = x1;);
}

static inline void bn_cmovznz4(uint64_t *res, uint64_t cin, uint64_t *x, uint64_t *y)
{
  uint64_t mask = ~FStar_UInt64_eq_mask(cin, (uint64_t)0U);
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = res;
    uint64_t uu____0 = x[i];
    uint64_t x1 = uu____0 ^ (mask & (y[i] ^ uu____0));
    os[i] = x1;);
}

static inline void bn_add_mod4(uint64_t *res, uint64_t *n, uint64_t *x, uint64_t *y)
{
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t t1 = x[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = y[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
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
    uint64_t x1 = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x1;);
}

static inline uint64_t bn_sub4(uint64_t *res, uint64_t *x, uint64_t *y)
{
  uint64_t c = (uint64_t)0U;
  {
    uint64_t t1 = x[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = y[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  uint64_t c0 = c;
  return c0;
}

static inline void bn_sub_mod4(uint64_t *res, uint64_t *n, uint64_t *x, uint64_t *y)
{
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t t1 = x[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = y[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t21 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t22 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t2 = y[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
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
    uint64_t x1 = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x1;);
}

void Hacl_Impl_P256_Bignum_bn_mul4(uint64_t *res, uint64_t *x, uint64_t *y)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t bj = y[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    {
      uint64_t a_i = x[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = x[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    uint64_t r = c;
    res[(uint32_t)4U + i0] = r;);
}

static inline void bn_sqr4(uint64_t *res, uint64_t *x)
{
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *ab = x;
    uint64_t a_j = x[i0];
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
    FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(x[i], x[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;);
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, tmp, res);
}

static inline void bn_lshift256(uint64_t *res, uint64_t *x)
{
  res[0U] = (uint64_t)0U;
  res[1U] = (uint64_t)0U;
  res[2U] = (uint64_t)0U;
  res[3U] = (uint64_t)0U;
  res[4U] = x[0U];
  res[5U] = x[1U];
  res[6U] = x[2U];
  res[7U] = x[3U];
}

static inline void bn_to_bytes_be4(uint8_t *res, uint64_t *f)
{
  uint8_t tmp[32U] = { 0U };
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    store64_be(res + i * (uint32_t)8U, f[(uint32_t)4U - i - (uint32_t)1U]););
}

static inline void bn_from_bytes_be4(uint64_t *res, uint8_t *b)
{
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = res;
    uint64_t u = load64_be(b + ((uint32_t)4U - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;);
}

static inline void bn2_to_bytes_be4(uint8_t *res, uint64_t *x, uint64_t *y)
{
  bn_to_bytes_be4(res, x);
  bn_to_bytes_be4(res + (uint32_t)32U, y);
}

static inline void make_prime(uint64_t *n)
{
  n[0U] = (uint64_t)0xffffffffffffffffU;
  n[1U] = (uint64_t)0xffffffffU;
  n[2U] = (uint64_t)0x0U;
  n[3U] = (uint64_t)0xffffffff00000001U;
}

static inline void make_order(uint64_t *n)
{
  n[0U] = (uint64_t)0xf3b9cac2fc632551U;
  n[1U] = (uint64_t)0xbce6faada7179e84U;
  n[2U] = (uint64_t)0xffffffffffffffffU;
  n[3U] = (uint64_t)0xffffffff00000000U;
}

static inline void make_a_coeff(uint64_t *a)
{
  a[0U] = (uint64_t)0xfffffffffffffffcU;
  a[1U] = (uint64_t)0x3ffffffffU;
  a[2U] = (uint64_t)0x0U;
  a[3U] = (uint64_t)0xfffffffc00000004U;
}

static inline void make_b_coeff(uint64_t *b)
{
  b[0U] = (uint64_t)0xd89cdf6229c4bddfU;
  b[1U] = (uint64_t)0xacf005cd78843090U;
  b[2U] = (uint64_t)0xe5a220abf7212ed6U;
  b[3U] = (uint64_t)0xdc30061d04874834U;
}

static inline void make_g_x(uint64_t *n)
{
  n[0U] = (uint64_t)0x79e730d418a9143cU;
  n[1U] = (uint64_t)0x75ba95fc5fedb601U;
  n[2U] = (uint64_t)0x79fb732b77622510U;
  n[3U] = (uint64_t)0x18905f76a53755c6U;
}

static inline void make_g_y(uint64_t *n)
{
  n[0U] = (uint64_t)0xddf25357ce95560aU;
  n[1U] = (uint64_t)0x8b4ab8e4ba19e45cU;
  n[2U] = (uint64_t)0xd2e88688dd21f325U;
  n[3U] = (uint64_t)0x8571ff1825885d85U;
}

static inline void make_fzero(uint64_t *n)
{
  n[0U] = (uint64_t)0U;
  n[1U] = (uint64_t)0U;
  n[2U] = (uint64_t)0U;
  n[3U] = (uint64_t)0U;
}

static inline void make_fone(uint64_t *n)
{
  n[0U] = (uint64_t)0x1U;
  n[1U] = (uint64_t)0xffffffff00000000U;
  n[2U] = (uint64_t)0xffffffffffffffffU;
  n[3U] = (uint64_t)0xfffffffeU;
}

static inline uint64_t bn_is_lt_prime_mask4(uint64_t *f)
{
  uint64_t tmp[4U] = { 0U };
  make_prime(tmp);
  uint64_t c = bn_sub4(tmp, f, tmp);
  return (uint64_t)0U - c;
}

static inline uint64_t feq_mask(uint64_t *a, uint64_t *b)
{
  uint64_t r = bn_is_eq_mask4(a, b);
  return r;
}

static inline void fmod_short(uint64_t *res, uint64_t *x)
{
  uint64_t tmp[4U] = { 0U };
  make_prime(tmp);
  uint64_t c = bn_sub4(tmp, x, tmp);
  bn_cmovznz4(res, c, tmp, x);
}

static inline void fadd0(uint64_t *res, uint64_t *x, uint64_t *y)
{
  uint64_t n[4U] = { 0U };
  make_prime(n);
  bn_add_mod4(res, n, x, y);
}

static inline void fsub0(uint64_t *res, uint64_t *x, uint64_t *y)
{
  uint64_t n[4U] = { 0U };
  make_prime(n);
  bn_sub_mod4(res, n, x, y);
}

static inline void fnegate_conditional_vartime(uint64_t *f, bool is_negate)
{
  uint64_t zero[4U] = { 0U };
  if (is_negate)
  {
    fsub0(f, zero, f);
  }
}

static inline void mont_reduction(uint64_t *res, uint64_t *x)
{
  uint64_t n[4U] = { 0U };
  make_prime(n);
  uint64_t c0 = (uint64_t)0U;
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t qj = (uint64_t)1U * x[i0];
    uint64_t *res_j0 = x + i0;
    uint64_t c = (uint64_t)0U;
    {
      uint64_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = x + (uint32_t)4U + i0;
    uint64_t res_j = x[(uint32_t)4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb););
  memcpy(res, x + (uint32_t)4U, (uint32_t)4U * sizeof (uint64_t));
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
    uint64_t x1 = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x1;);
}

static inline void from_mont(uint64_t *res, uint64_t *a)
{
  uint64_t tmp[8U] = { 0U };
  uint64_t *t_low = tmp;
  memcpy(t_low, a, (uint32_t)4U * sizeof (uint64_t));
  mont_reduction(res, tmp);
}

void Hacl_Impl_P256_Field_fmul(uint64_t *res, uint64_t *x, uint64_t *y)
{
  uint64_t tmp[8U] = { 0U };
  Hacl_Impl_P256_Bignum_bn_mul4(tmp, x, y);
  mont_reduction(res, tmp);
}

static inline void fsqr0(uint64_t *res, uint64_t *x)
{
  uint64_t tmp[8U] = { 0U };
  bn_sqr4(tmp, x);
  mont_reduction(res, tmp);
}

static inline void fcube(uint64_t *res, uint64_t *x)
{
  fsqr0(res, x);
  Hacl_Impl_P256_Field_fmul(res, res, x);
}

static inline void fmul_by_3(uint64_t *res, uint64_t *x)
{
  fadd0(res, x, x);
  fadd0(res, res, x);
}

static inline void fmul_by_4(uint64_t *res, uint64_t *x)
{
  fadd0(res, x, x);
  fadd0(res, res, res);
}

static inline void fmul_by_8(uint64_t *res, uint64_t *x)
{
  fmul_by_4(res, x);
  fadd0(res, res, res);
}

void Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(uint64_t *i, uint64_t *o)
{
  uint64_t tempBuffer[36U] = { 0U };
  uint64_t i0 = i[0U];
  uint64_t i1 = i[1U];
  uint64_t i2 = i[2U];
  uint64_t i3 = i[3U];
  uint64_t i4 = i[4U];
  uint64_t i5 = i[5U];
  uint64_t i6 = i[6U];
  uint64_t i7 = i[7U];
  uint32_t c0 = (uint32_t)i0;
  uint32_t c1 = (uint32_t)(i0 >> (uint32_t)32U);
  uint32_t c2 = (uint32_t)i1;
  uint32_t c3 = (uint32_t)(i1 >> (uint32_t)32U);
  uint32_t c4 = (uint32_t)i2;
  uint32_t c5 = (uint32_t)(i2 >> (uint32_t)32U);
  uint32_t c6 = (uint32_t)i3;
  uint32_t c7 = (uint32_t)(i3 >> (uint32_t)32U);
  uint32_t c8 = (uint32_t)i4;
  uint32_t c9 = (uint32_t)(i4 >> (uint32_t)32U);
  uint32_t c10 = (uint32_t)i5;
  uint32_t c11 = (uint32_t)(i5 >> (uint32_t)32U);
  uint32_t c12 = (uint32_t)i6;
  uint32_t c13 = (uint32_t)(i6 >> (uint32_t)32U);
  uint32_t c14 = (uint32_t)i7;
  uint32_t c15 = (uint32_t)(i7 >> (uint32_t)32U);
  uint64_t *t01 = tempBuffer;
  uint64_t *t110 = tempBuffer + (uint32_t)4U;
  uint64_t *t210 = tempBuffer + (uint32_t)8U;
  uint64_t *t310 = tempBuffer + (uint32_t)12U;
  uint64_t *t410 = tempBuffer + (uint32_t)16U;
  uint64_t *t510 = tempBuffer + (uint32_t)20U;
  uint64_t *t610 = tempBuffer + (uint32_t)24U;
  uint64_t *t710 = tempBuffer + (uint32_t)28U;
  uint64_t *t810 = tempBuffer + (uint32_t)32U;
  uint64_t b0 = (uint64_t)c0 | (uint64_t)c1 << (uint32_t)32U;
  uint64_t b10 = (uint64_t)c2 | (uint64_t)c3 << (uint32_t)32U;
  uint64_t b20 = (uint64_t)c4 | (uint64_t)c5 << (uint32_t)32U;
  uint64_t b30 = (uint64_t)c6 | (uint64_t)c7 << (uint32_t)32U;
  t01[0U] = b0;
  t01[1U] = b10;
  t01[2U] = b20;
  t01[3U] = b30;
  fmod_short(t01, t01);
  uint64_t b00 = (uint64_t)0U;
  uint64_t b11 = (uint64_t)(uint32_t)0U | (uint64_t)c11 << (uint32_t)32U;
  uint64_t b21 = (uint64_t)c12 | (uint64_t)c13 << (uint32_t)32U;
  uint64_t b31 = (uint64_t)c14 | (uint64_t)c15 << (uint32_t)32U;
  t110[0U] = b00;
  t110[1U] = b11;
  t110[2U] = b21;
  t110[3U] = b31;
  fmod_short(t110, t110);
  uint64_t b01 = (uint64_t)0U;
  uint64_t b12 = (uint64_t)(uint32_t)0U | (uint64_t)c12 << (uint32_t)32U;
  uint64_t b22 = (uint64_t)c13 | (uint64_t)c14 << (uint32_t)32U;
  uint64_t b32 = (uint64_t)c15 | (uint64_t)(uint32_t)0U << (uint32_t)32U;
  t210[0U] = b01;
  t210[1U] = b12;
  t210[2U] = b22;
  t210[3U] = b32;
  uint64_t b02 = (uint64_t)c8 | (uint64_t)c9 << (uint32_t)32U;
  uint64_t b13 = (uint64_t)c10 | (uint64_t)(uint32_t)0U << (uint32_t)32U;
  uint64_t b23 = (uint64_t)0U;
  uint64_t b33 = (uint64_t)c14 | (uint64_t)c15 << (uint32_t)32U;
  t310[0U] = b02;
  t310[1U] = b13;
  t310[2U] = b23;
  t310[3U] = b33;
  fmod_short(t310, t310);
  uint64_t b03 = (uint64_t)c9 | (uint64_t)c10 << (uint32_t)32U;
  uint64_t b14 = (uint64_t)c11 | (uint64_t)c13 << (uint32_t)32U;
  uint64_t b24 = (uint64_t)c14 | (uint64_t)c15 << (uint32_t)32U;
  uint64_t b34 = (uint64_t)c13 | (uint64_t)c8 << (uint32_t)32U;
  t410[0U] = b03;
  t410[1U] = b14;
  t410[2U] = b24;
  t410[3U] = b34;
  fmod_short(t410, t410);
  uint64_t b04 = (uint64_t)c11 | (uint64_t)c12 << (uint32_t)32U;
  uint64_t b15 = (uint64_t)c13 | (uint64_t)(uint32_t)0U << (uint32_t)32U;
  uint64_t b25 = (uint64_t)0U;
  uint64_t b35 = (uint64_t)c8 | (uint64_t)c10 << (uint32_t)32U;
  t510[0U] = b04;
  t510[1U] = b15;
  t510[2U] = b25;
  t510[3U] = b35;
  fmod_short(t510, t510);
  uint64_t b05 = (uint64_t)c12 | (uint64_t)c13 << (uint32_t)32U;
  uint64_t b16 = (uint64_t)c14 | (uint64_t)c15 << (uint32_t)32U;
  uint64_t b26 = (uint64_t)0U;
  uint64_t b36 = (uint64_t)c9 | (uint64_t)c11 << (uint32_t)32U;
  t610[0U] = b05;
  t610[1U] = b16;
  t610[2U] = b26;
  t610[3U] = b36;
  fmod_short(t610, t610);
  uint64_t b06 = (uint64_t)c13 | (uint64_t)c14 << (uint32_t)32U;
  uint64_t b17 = (uint64_t)c15 | (uint64_t)c8 << (uint32_t)32U;
  uint64_t b27 = (uint64_t)c9 | (uint64_t)c10 << (uint32_t)32U;
  uint64_t b37 = (uint64_t)(uint32_t)0U | (uint64_t)c12 << (uint32_t)32U;
  t710[0U] = b06;
  t710[1U] = b17;
  t710[2U] = b27;
  t710[3U] = b37;
  fmod_short(t710, t710);
  uint64_t b07 = (uint64_t)c14 | (uint64_t)c15 << (uint32_t)32U;
  uint64_t b1 = (uint64_t)(uint32_t)0U | (uint64_t)c9 << (uint32_t)32U;
  uint64_t b2 = (uint64_t)c10 | (uint64_t)c11 << (uint32_t)32U;
  uint64_t b3 = (uint64_t)(uint32_t)0U | (uint64_t)c13 << (uint32_t)32U;
  t810[0U] = b07;
  t810[1U] = b1;
  t810[2U] = b2;
  t810[3U] = b3;
  fmod_short(t810, t810);
  uint64_t *t010 = tempBuffer;
  uint64_t *t11 = tempBuffer + (uint32_t)4U;
  uint64_t *t21 = tempBuffer + (uint32_t)8U;
  uint64_t *t31 = tempBuffer + (uint32_t)12U;
  uint64_t *t41 = tempBuffer + (uint32_t)16U;
  uint64_t *t51 = tempBuffer + (uint32_t)20U;
  uint64_t *t61 = tempBuffer + (uint32_t)24U;
  uint64_t *t71 = tempBuffer + (uint32_t)28U;
  uint64_t *t81 = tempBuffer + (uint32_t)32U;
  fadd0(t21, t21, t21);
  fadd0(t11, t11, t11);
  fadd0(o, t010, t11);
  fadd0(o, t21, o);
  fadd0(o, t31, o);
  fadd0(o, t41, o);
  fsub0(o, o, t51);
  fsub0(o, o, t61);
  fsub0(o, o, t71);
  fsub0(o, o, t81);
}

static inline void fexp_vartime(uint64_t *out, uint64_t *a, uint64_t *b)
{
  uint64_t table[128U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  uint64_t *t0 = table;
  uint64_t *t1 = table + (uint32_t)4U;
  make_fone(t0);
  memcpy(t1, a, (uint32_t)4U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    (uint32_t)0U,
    (uint32_t)15U,
    (uint32_t)1U,
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)4U;
    fsqr0(tmp, t11);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)4U,
      tmp,
      (uint32_t)4U * sizeof (uint64_t));
    uint64_t *t2 = table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)4U;
    Hacl_Impl_P256_Field_fmul(tmp, a, t2);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)4U,
      tmp,
      (uint32_t)4U * sizeof (uint64_t)););
  uint64_t mask_l0 = (uint64_t)31U;
  uint32_t i0 = (uint32_t)3U;
  uint32_t j0 = (uint32_t)63U;
  uint64_t p10 = b[i0] >> j0;
  uint64_t ite0;
  if (i0 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
  {
    ite0 = p10 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j0);
  }
  else
  {
    ite0 = p10;
  }
  uint64_t bits_c = ite0 & mask_l0;
  uint32_t bits_l32 = (uint32_t)bits_c;
  const uint64_t *a_bits_l = table + bits_l32 * (uint32_t)4U;
  memcpy(out, (uint64_t *)a_bits_l, (uint32_t)4U * sizeof (uint64_t));
  uint64_t tmp0[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)51U; i++)
  {
    KRML_MAYBE_FOR5(i1, (uint32_t)0U, (uint32_t)5U, (uint32_t)1U, fsqr0(out, out););
    uint32_t bk = (uint32_t)255U;
    uint64_t mask_l = (uint64_t)31U;
    uint32_t i1 = (bk - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j = (bk - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    uint32_t bits_l320 = (uint32_t)bits_l;
    const uint64_t *a_bits_l0 = table + bits_l320 * (uint32_t)4U;
    memcpy(tmp0, (uint64_t *)a_bits_l0, (uint32_t)4U * sizeof (uint64_t));
    Hacl_Impl_P256_Field_fmul(out, out, tmp0);
  }
}

static inline void finv(uint64_t *res, uint64_t *a)
{
  uint64_t b[4U] = { 0U };
  b[0U] = (uint64_t)0xfffffffffffffffdU;
  b[1U] = (uint64_t)0xffffffffU;
  b[2U] = (uint64_t)0x0U;
  b[3U] = (uint64_t)0xffffffff00000001U;
  uint64_t tmp[4U] = { 0U };
  memcpy(tmp, a, (uint32_t)4U * sizeof (uint64_t));
  fexp_vartime(res, tmp, b);
}

static inline void fsqrt(uint64_t *res, uint64_t *a)
{
  uint64_t b[4U] = { 0U };
  b[0U] = (uint64_t)0x0U;
  b[1U] = (uint64_t)0x40000000U;
  b[2U] = (uint64_t)0x4000000000000000U;
  b[3U] = (uint64_t)0x3fffffffc0000000U;
  uint64_t tmp[4U] = { 0U };
  memcpy(tmp, a, (uint32_t)4U * sizeof (uint64_t));
  fexp_vartime(res, tmp, b);
}

static inline void make_base_point(uint64_t *p)
{
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t *z = p + (uint32_t)8U;
  make_g_x(x);
  make_g_y(y);
  make_fone(z);
}

static inline void make_point_at_inf(uint64_t *p)
{
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t *z = p + (uint32_t)8U;
  make_fzero(x);
  make_fzero(y);
  make_fzero(z);
}

uint64_t Hacl_Impl_P256_Point_is_point_at_inf(uint64_t *p)
{
  uint64_t *pz = p + (uint32_t)8U;
  return bn_is_zero_mask4(pz);
}

static inline bool is_point_at_inf_vartime(uint64_t *p)
{
  uint64_t *pz = p + (uint32_t)8U;
  return bn_is_zero_vartime4(pz);
}

static inline void copy_point_conditional(uint64_t *res, uint64_t *p, uint64_t *q_mask)
{
  uint64_t mask = Hacl_Impl_P256_Point_is_point_at_inf(q_mask);
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *pz = p + (uint32_t)8U;
  uint64_t *rx = res;
  uint64_t *ry = res + (uint32_t)4U;
  uint64_t *rz = res + (uint32_t)8U;
  bn_copy_conditional4(rx, mask, rx, px);
  bn_copy_conditional4(ry, mask, ry, py);
  bn_copy_conditional4(rz, mask, rz, pz);
}

static inline void point_to_mont(uint64_t *res, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *pz = p + (uint32_t)8U;
  uint64_t *rx = res;
  uint64_t *ry = res + (uint32_t)4U;
  uint64_t *rz = res + (uint32_t)8U;
  uint64_t tmp[8U] = { 0U };
  bn_lshift256(tmp, px);
  Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(tmp, rx);
  uint64_t tmp0[8U] = { 0U };
  bn_lshift256(tmp0, py);
  Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(tmp0, ry);
  uint64_t tmp1[8U] = { 0U };
  bn_lshift256(tmp1, pz);
  Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(tmp1, rz);
}

static inline void norm_jacob_point_x(uint64_t *res, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *pz = p + (uint32_t)8U;
  fsqr0(res, pz);
  finv(res, res);
  Hacl_Impl_P256_Field_fmul(res, px, res);
  from_mont(res, res);
}

static inline void norm_jacob_point(uint64_t *res, uint64_t *p)
{
  uint64_t tmp[12U] = { 0U };
  uint64_t *tx = tmp;
  uint64_t *ty = tmp + (uint32_t)4U;
  uint64_t *tz = tmp + (uint32_t)8U;
  norm_jacob_point_x(tx, p);
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *pz = p + (uint32_t)8U;
  fcube(ty, pz);
  finv(ty, ty);
  Hacl_Impl_P256_Field_fmul(ty, py, ty);
  from_mont(ty, ty);
  uint64_t zero[4U] = { 0U };
  uint64_t bit = Hacl_Impl_P256_Point_is_point_at_inf(p);
  tz[0U] = (uint64_t)1U;
  tz[1U] = (uint64_t)0U;
  tz[2U] = (uint64_t)0U;
  tz[3U] = (uint64_t)0U;
  bn_copy_conditional4(tz, bit, tz, zero);
  memcpy(res, tmp, (uint32_t)12U * sizeof (uint64_t));
}

static inline void to_jacob_point(uint64_t *res, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *rx = res;
  uint64_t *ry = res + (uint32_t)4U;
  uint64_t *rz = res + (uint32_t)8U;
  memcpy(rx, px, (uint32_t)4U * sizeof (uint64_t));
  memcpy(ry, py, (uint32_t)4U * sizeof (uint64_t));
  rz[0U] = (uint64_t)1U;
  rz[1U] = (uint64_t)0U;
  rz[2U] = (uint64_t)0U;
  rz[3U] = (uint64_t)0U;
}

static inline bool is_point_eq_vartime(uint64_t *p, uint64_t *q)
{
  uint64_t p_norm[12U] = { 0U };
  uint64_t q_norm[12U] = { 0U };
  norm_jacob_point(p_norm, p);
  norm_jacob_point(q_norm, q);
  uint64_t *px = p_norm;
  uint64_t *py = p_norm + (uint32_t)4U;
  uint64_t *pz = p_norm + (uint32_t)8U;
  uint64_t *qx = q_norm;
  uint64_t *qy = q_norm + (uint32_t)4U;
  uint64_t *qz = q_norm + (uint32_t)8U;
  bool is_x_eq = bn_is_eq_vartime4(px, qx);
  bool is_y_eq = bn_is_eq_vartime4(py, qy);
  bool is_z_eq = bn_is_eq_vartime4(pz, qz);
  bool is_pq_equal = is_x_eq && is_y_eq && is_z_eq;
  return is_pq_equal;
}

static inline bool is_point_on_curve_vartime(uint64_t *p)
{
  uint64_t rp[4U] = { 0U };
  uint64_t tx[4U] = { 0U };
  uint64_t ty[4U] = { 0U };
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  uint64_t tmp[8U] = { 0U };
  bn_lshift256(tmp, px);
  Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(tmp, tx);
  uint64_t tmp0[8U] = { 0U };
  bn_lshift256(tmp0, py);
  Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(tmp0, ty);
  uint64_t tmp1[4U] = { 0U };
  fcube(rp, tx);
  make_a_coeff(tmp1);
  Hacl_Impl_P256_Field_fmul(tmp1, tmp1, tx);
  fadd0(rp, tmp1, rp);
  make_b_coeff(tmp1);
  fadd0(rp, tmp1, rp);
  fsqr0(ty, ty);
  uint64_t r = feq_mask(ty, rp);
  bool r0 = r == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  return r0;
}

void Hacl_Impl_P256_Point_aff_point_store(uint8_t *res, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  bn2_to_bytes_be4(res, px, py);
}

bool Hacl_Impl_P256_Point_load_point_vartime(uint64_t *p, uint8_t *b)
{
  uint8_t *p_x = b;
  uint8_t *p_y = b + (uint32_t)32U;
  uint64_t point_aff[8U] = { 0U };
  uint64_t *bn_p_x = point_aff;
  uint64_t *bn_p_y = point_aff + (uint32_t)4U;
  bn_from_bytes_be4(bn_p_x, p_x);
  bn_from_bytes_be4(bn_p_y, p_y);
  uint64_t *px = point_aff;
  uint64_t *py = point_aff + (uint32_t)4U;
  uint64_t lessX = bn_is_lt_prime_mask4(px);
  uint64_t lessY = bn_is_lt_prime_mask4(py);
  uint64_t res0 = lessX & lessY;
  bool is_xy_valid = res0 == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  bool res;
  if (!is_xy_valid)
  {
    res = false;
  }
  else
  {
    res = is_point_on_curve_vartime(point_aff);
  }
  if (res)
  {
    to_jacob_point(p, point_aff);
  }
  return res;
}

static inline bool aff_point_decompress_vartime(uint64_t *x, uint64_t *y, uint8_t *s)
{
  uint8_t s0 = s[0U];
  uint8_t s01 = s0;
  if (!(s01 == (uint8_t)0x02U || s01 == (uint8_t)0x03U))
  {
    return false;
  }
  uint8_t *xb = s + (uint32_t)1U;
  bn_from_bytes_be4(x, xb);
  uint64_t is_x_valid = bn_is_lt_prime_mask4(x);
  bool is_x_valid1 = is_x_valid == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  bool is_y_odd = s01 == (uint8_t)0x03U;
  if (!is_x_valid1)
  {
    return false;
  }
  uint64_t y2M[4U] = { 0U };
  uint64_t xM[4U] = { 0U };
  uint64_t yM[4U] = { 0U };
  uint64_t tmp[8U] = { 0U };
  bn_lshift256(tmp, x);
  Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(tmp, xM);
  uint64_t tmp0[4U] = { 0U };
  fcube(y2M, xM);
  make_a_coeff(tmp0);
  Hacl_Impl_P256_Field_fmul(tmp0, tmp0, xM);
  fadd0(y2M, tmp0, y2M);
  make_b_coeff(tmp0);
  fadd0(y2M, tmp0, y2M);
  fsqrt(yM, y2M);
  from_mont(y, yM);
  fsqr0(yM, yM);
  uint64_t r = feq_mask(yM, y2M);
  bool is_y_valid = r == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  bool is_y_valid0 = is_y_valid;
  if (!is_y_valid0)
  {
    return false;
  }
  uint64_t is_y_odd1 = y[0U] & (uint64_t)1U;
  bool is_y_odd2 = is_y_odd1 == (uint64_t)1U;
  fnegate_conditional_vartime(y, is_y_odd2 != is_y_odd);
  return true;
}

static inline void point_double(uint64_t *p, uint64_t *res, uint64_t *tmp)
{
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *pz = p + (uint32_t)8U;
  uint64_t *x3 = res;
  uint64_t *y3 = res + (uint32_t)4U;
  uint64_t *z3 = res + (uint32_t)8U;
  uint64_t *delta = tmp;
  uint64_t *gamma = tmp + (uint32_t)4U;
  uint64_t *beta = tmp + (uint32_t)8U;
  uint64_t *alpha = tmp + (uint32_t)12U;
  uint64_t *ftmp = tmp + (uint32_t)16U;
  uint64_t *px1 = p;
  uint64_t *py1 = p + (uint32_t)4U;
  uint64_t *pz1 = p + (uint32_t)8U;
  fsqr0(delta, pz1);
  fsqr0(gamma, py1);
  Hacl_Impl_P256_Field_fmul(beta, px1, gamma);
  fsub0(alpha, px1, delta);
  fmul_by_3(ftmp, alpha);
  fadd0(alpha, px1, delta);
  Hacl_Impl_P256_Field_fmul(alpha, ftmp, alpha);
  fsqr0(x3, alpha);
  fmul_by_4(beta, beta);
  fadd0(ftmp, beta, beta);
  fsub0(x3, x3, ftmp);
  fadd0(z3, py, pz);
  fsqr0(z3, z3);
  fsub0(z3, z3, delta);
  fsub0(z3, z3, gamma);
  fsub0(y3, beta, x3);
  Hacl_Impl_P256_Field_fmul(y3, alpha, y3);
  fsqr0(gamma, gamma);
  fmul_by_8(gamma, gamma);
  fsub0(y3, y3, gamma);
}

static inline void point_add(uint64_t *p, uint64_t *q, uint64_t *res, uint64_t *tmp)
{
  uint64_t *z1 = p + (uint32_t)8U;
  uint64_t *z2 = q + (uint32_t)8U;
  uint64_t *u1 = tmp;
  uint64_t *u2 = tmp + (uint32_t)4U;
  uint64_t *s1 = tmp + (uint32_t)8U;
  uint64_t *s2 = tmp + (uint32_t)12U;
  uint64_t *h = tmp + (uint32_t)16U;
  uint64_t *r = tmp + (uint32_t)20U;
  uint64_t *hhh = tmp + (uint32_t)24U;
  uint64_t *ftmp = tmp + (uint32_t)28U;
  uint64_t *x3 = res;
  uint64_t *y3 = res + (uint32_t)4U;
  uint64_t *z3 = res + (uint32_t)8U;
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)4U;
  uint64_t *pz = p + (uint32_t)8U;
  uint64_t *qx = q;
  uint64_t *qy = q + (uint32_t)4U;
  uint64_t *qz = q + (uint32_t)8U;
  fsqr0(s1, qz);
  fsqr0(s2, pz);
  Hacl_Impl_P256_Field_fmul(u1, px, s1);
  Hacl_Impl_P256_Field_fmul(u2, qx, s2);
  Hacl_Impl_P256_Field_fmul(s1, qz, s1);
  Hacl_Impl_P256_Field_fmul(s1, py, s1);
  Hacl_Impl_P256_Field_fmul(s2, pz, s2);
  Hacl_Impl_P256_Field_fmul(s2, qy, s2);
  fsub0(h, u2, u1);
  fsub0(r, s2, s1);
  fsqr0(hhh, h);
  Hacl_Impl_P256_Field_fmul(u1, hhh, u1);
  Hacl_Impl_P256_Field_fmul(hhh, h, hhh);
  fsqr0(x3, r);
  fsub0(x3, x3, hhh);
  fadd0(ftmp, u1, u1);
  fsub0(x3, x3, ftmp);
  Hacl_Impl_P256_Field_fmul(y3, s1, hhh);
  fsub0(u1, u1, x3);
  Hacl_Impl_P256_Field_fmul(u1, r, u1);
  fsub0(y3, u1, y3);
  Hacl_Impl_P256_Field_fmul(h, z1, h);
  Hacl_Impl_P256_Field_fmul(z3, h, z2);
  copy_point_conditional(res, q, p);
  copy_point_conditional(res, p, q);
}

static inline void cswap(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  KRML_MAYBE_FOR12(i,
    (uint32_t)0U,
    (uint32_t)12U,
    (uint32_t)1U,
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;);
}

static inline void montgomery_ladder(uint64_t *p, uint64_t *q, uint8_t *scalar, uint64_t *tmp)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint32_t bit0 = (uint32_t)255U - i;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)31U - bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(bit, p, q);
    uint64_t *tmp32 = tmp;
    uint64_t *r1_copy = tmp + (uint32_t)32U;
    memcpy(r1_copy, q, (uint32_t)12U * sizeof (uint64_t));
    point_add(p, r1_copy, q, tmp32);
    point_double(p, p, tmp32);
    cswap(bit, p, q);
  }
}

static inline void scalarMultiplicationWithoutNorm(uint64_t *p, uint64_t *res, uint8_t *scalar)
{
  uint64_t tmp[100U] = { 0U };
  uint64_t *q = tmp;
  make_point_at_inf(q);
  point_to_mont(res, p);
  uint64_t *buff = tmp + (uint32_t)12U;
  montgomery_ladder(q, res, scalar, buff);
  memcpy(res, q, (uint32_t)12U * sizeof (uint64_t));
}

static inline void point_mul(uint64_t *res, uint64_t *p, uint64_t *scalar)
{
  uint64_t tmp[12U] = { 0U };
  memcpy(tmp, p, (uint32_t)12U * sizeof (uint64_t));
  uint8_t bytes_scalar[32U] = { 0U };
  bn_to_bytes_be4(bytes_scalar, scalar);
  scalarMultiplicationWithoutNorm(tmp, res, bytes_scalar);
}

static inline void point_mul_g(uint64_t *res, uint64_t *scalar)
{
  uint8_t bytes_scalar[32U] = { 0U };
  bn_to_bytes_be4(bytes_scalar, scalar);
  uint64_t g[12U] = { 0U };
  make_base_point(g);
  uint64_t tmp[100U] = { 0U };
  uint64_t *q = tmp;
  make_point_at_inf(q);
  uint64_t *buff = tmp + (uint32_t)12U;
  montgomery_ladder(q, g, bytes_scalar, buff);
  memcpy(res, q, (uint32_t)12U * sizeof (uint64_t));
}

void Hacl_Impl_P256_PointMul_point_mul_bytes(uint64_t *res, uint64_t *p, uint8_t *scalar)
{
  uint64_t s_q[4U] = { 0U };
  bn_from_bytes_be4(s_q, scalar);
  point_mul(res, p, s_q);
  norm_jacob_point(res, res);
}

void Hacl_Impl_P256_PointMul_point_mul_g_bytes(uint64_t *res, uint8_t *scalar)
{
  uint64_t s_q[4U] = { 0U };
  bn_from_bytes_be4(s_q, scalar);
  point_mul_g(res, s_q);
  norm_jacob_point(res, res);
}

static inline void
point_mul_double_g(uint64_t *res, uint64_t *scalar1, uint64_t *scalar2, uint64_t *p)
{
  uint64_t sg1[12U] = { 0U };
  uint64_t sp2[12U] = { 0U };
  uint64_t tmp[88U] = { 0U };
  point_mul_g(sg1, scalar1);
  point_mul(sp2, p, scalar2);
  bool is_points_eq = is_point_eq_vartime(sg1, sp2);
  if (is_points_eq)
  {
    point_double(sg1, res, tmp);
  }
  else
  {
    point_add(sg1, sp2, res, tmp);
  }
}

static inline void make_qone(uint64_t *f)
{
  f[0U] = (uint64_t)0xc46353d039cdaafU;
  f[1U] = (uint64_t)0x4319055258e8617bU;
  f[2U] = (uint64_t)0x0U;
  f[3U] = (uint64_t)0xffffffffU;
}

static inline uint64_t bn_is_lt_order_mask4(uint64_t *f)
{
  uint64_t tmp[4U] = { 0U };
  make_order(tmp);
  uint64_t c = bn_sub4(tmp, f, tmp);
  return (uint64_t)0U - c;
}

static inline uint64_t bn_is_lt_order_and_gt_zero_mask4(uint64_t *f)
{
  uint64_t is_lt_order = bn_is_lt_order_mask4(f);
  uint64_t is_eq_zero = bn_is_zero_mask4(f);
  return is_lt_order & ~is_eq_zero;
}

static inline void qmod_short(uint64_t *res, uint64_t *x)
{
  uint64_t tmp[4U] = { 0U };
  make_order(tmp);
  uint64_t c = bn_sub4(tmp, x, tmp);
  bn_cmovznz4(res, c, tmp, x);
}

static inline void qadd(uint64_t *res, uint64_t *x, uint64_t *y)
{
  uint64_t n[4U] = { 0U };
  make_order(n);
  bn_add_mod4(res, n, x, y);
}

static inline void qmont_reduction(uint64_t *res, uint64_t *x)
{
  uint64_t n[4U] = { 0U };
  make_order(n);
  uint64_t c0 = (uint64_t)0U;
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t qj = (uint64_t)0xccd1c8aaee00bc4fU * x[i0];
    uint64_t *res_j0 = x + i0;
    uint64_t c = (uint64_t)0U;
    {
      uint64_t a_i = n[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = x + (uint32_t)4U + i0;
    uint64_t res_j = x[(uint32_t)4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb););
  memcpy(res, x + (uint32_t)4U, (uint32_t)4U * sizeof (uint64_t));
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
    uint64_t x1 = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x1;);
}

static inline void from_qmont(uint64_t *res, uint64_t *x)
{
  uint64_t tmp[8U] = { 0U };
  uint64_t *t_low = tmp;
  memcpy(t_low, x, (uint32_t)4U * sizeof (uint64_t));
  qmont_reduction(res, tmp);
}

static inline void qmul(uint64_t *res, uint64_t *x, uint64_t *y)
{
  uint64_t tmp[8U] = { 0U };
  Hacl_Impl_P256_Bignum_bn_mul4(tmp, x, y);
  qmont_reduction(res, tmp);
}

static inline void qsqr(uint64_t *res, uint64_t *x)
{
  uint64_t tmp[8U] = { 0U };
  bn_sqr4(tmp, x);
  qmont_reduction(res, tmp);
}

static inline void qexp_vartime(uint64_t *out, uint64_t *a, uint64_t *b)
{
  uint64_t table[128U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  uint64_t *t0 = table;
  uint64_t *t1 = table + (uint32_t)4U;
  make_qone(t0);
  memcpy(t1, a, (uint32_t)4U * sizeof (uint64_t));
  KRML_MAYBE_FOR15(i,
    (uint32_t)0U,
    (uint32_t)15U,
    (uint32_t)1U,
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)4U;
    qsqr(tmp, t11);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)4U,
      tmp,
      (uint32_t)4U * sizeof (uint64_t));
    uint64_t *t2 = table + ((uint32_t)2U * i + (uint32_t)2U) * (uint32_t)4U;
    qmul(tmp, a, t2);
    memcpy(table + ((uint32_t)2U * i + (uint32_t)3U) * (uint32_t)4U,
      tmp,
      (uint32_t)4U * sizeof (uint64_t)););
  uint64_t mask_l0 = (uint64_t)31U;
  uint32_t i0 = (uint32_t)3U;
  uint32_t j0 = (uint32_t)63U;
  uint64_t p10 = b[i0] >> j0;
  uint64_t ite0;
  if (i0 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
  {
    ite0 = p10 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j0);
  }
  else
  {
    ite0 = p10;
  }
  uint64_t bits_c = ite0 & mask_l0;
  uint32_t bits_l32 = (uint32_t)bits_c;
  const uint64_t *a_bits_l = table + bits_l32 * (uint32_t)4U;
  memcpy(out, (uint64_t *)a_bits_l, (uint32_t)4U * sizeof (uint64_t));
  uint64_t tmp0[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)51U; i++)
  {
    KRML_MAYBE_FOR5(i1, (uint32_t)0U, (uint32_t)5U, (uint32_t)1U, qsqr(out, out););
    uint32_t bk = (uint32_t)255U;
    uint64_t mask_l = (uint64_t)31U;
    uint32_t i1 = (bk - (uint32_t)5U * i - (uint32_t)5U) / (uint32_t)64U;
    uint32_t j = (bk - (uint32_t)5U * i - (uint32_t)5U) % (uint32_t)64U;
    uint64_t p1 = b[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    uint32_t bits_l320 = (uint32_t)bits_l;
    const uint64_t *a_bits_l0 = table + bits_l320 * (uint32_t)4U;
    memcpy(tmp0, (uint64_t *)a_bits_l0, (uint32_t)4U * sizeof (uint64_t));
    qmul(out, out, tmp0);
  }
}

static inline void qinv(uint64_t *res, uint64_t *r)
{
  uint64_t b[4U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  memcpy(tmp, r, (uint32_t)4U * sizeof (uint64_t));
  b[0U] = (uint64_t)0xf3b9cac2fc63254fU;
  b[1U] = (uint64_t)0xbce6faada7179e84U;
  b[2U] = (uint64_t)0xffffffffffffffffU;
  b[3U] = (uint64_t)0xffffffff00000000U;
  qexp_vartime(res, tmp, b);
}

static inline void qmul_mont(uint64_t *sinv, uint64_t *b, uint64_t *res)
{
  uint64_t tmp[4U] = { 0U };
  from_qmont(tmp, b);
  qmul(res, sinv, tmp);
}

static inline bool
ecdsa_verify_msg_as_qelem(
  uint64_t *m_q,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t tmp[32U] = { 0U };
  uint64_t *pk = tmp;
  uint64_t *r_q = tmp + (uint32_t)12U;
  uint64_t *s_q = tmp + (uint32_t)16U;
  uint64_t *u1 = tmp + (uint32_t)20U;
  uint64_t *u2 = tmp + (uint32_t)24U;
  uint64_t *x = tmp + (uint32_t)28U;
  bool is_pk_valid = Hacl_Impl_P256_Point_load_point_vartime(pk, public_key);
  bn_from_bytes_be4(r_q, signature_r);
  bn_from_bytes_be4(s_q, signature_s);
  uint64_t is_r_valid = bn_is_lt_order_and_gt_zero_mask4(r_q);
  uint64_t is_s_valid = bn_is_lt_order_and_gt_zero_mask4(s_q);
  bool
  is_rs_valid =
    is_r_valid
    == (uint64_t)0xFFFFFFFFFFFFFFFFU
    && is_s_valid == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  if (!(is_pk_valid && is_rs_valid))
  {
    return false;
  }
  uint64_t sinv[4U] = { 0U };
  qinv(sinv, s_q);
  qmul_mont(sinv, m_q, u1);
  qmul_mont(sinv, r_q, u2);
  uint64_t res[12U] = { 0U };
  point_mul_double_g(res, u1, u2, pk);
  norm_jacob_point(res, res);
  bool is_res_point_at_inf = is_point_at_inf_vartime(res);
  uint64_t *res_x = res;
  qmod_short(x, res_x);
  bool b = !is_res_point_at_inf;
  if (!b)
  {
    return false;
  }
  bool res0 = bn_is_eq_vartime4(x, r_q);
  return res0;
}

static inline bool
ecdsa_sign_msg_as_qelem(
  uint8_t *signature,
  uint64_t *m_q,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t rsdk_q[16U] = { 0U };
  uint64_t *r_q = rsdk_q;
  uint64_t *s_q = rsdk_q + (uint32_t)4U;
  uint64_t *d_a = rsdk_q + (uint32_t)8U;
  uint64_t *k_q = rsdk_q + (uint32_t)12U;
  bn_from_bytes_be4(d_a, private_key);
  bn_from_bytes_be4(k_q, nonce);
  uint64_t p[12U] = { 0U };
  point_mul_g(p, k_q);
  norm_jacob_point_x(r_q, p);
  qmod_short(r_q, r_q);
  uint64_t kinv[4U] = { 0U };
  qinv(kinv, k_q);
  qmul(s_q, r_q, d_a);
  from_qmont(m_q, m_q);
  qadd(s_q, m_q, s_q);
  qmul(s_q, kinv, s_q);
  bn2_to_bytes_be4(signature, r_q, s_q);
  uint64_t is_r_zero = bn_is_zero_mask4(r_q);
  uint64_t is_s_zero = bn_is_zero_mask4(s_q);
  bool res = (~is_r_zero & ~is_s_zero) == (uint64_t)0xFFFFFFFFFFFFFFFFU;
  return res;
}


/*******************************************************************************

ECDSA and ECDH functions over the P-256 NIST curve.

This module implements signing and verification, key validation, conversions
between various point representations, and ECDH key agreement.

*******************************************************************************/

/**************/
/* Signatures */
/**************/

/*
  Per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/

/**
Hash the message with SHA2-256, then sign the resulting digest with the P256 signature function.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}

/**
Hash the message with SHA2-384, then sign the resulting digest with the P256 signature function.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[48U] = { 0U };
  Hacl_Hash_SHA2_hash_384(msg, msg_len, mHash);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}

/**
Hash the message with SHA2-512, then sign the resulting digest with the P256 signature function.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[64U] = { 0U };
  Hacl_Hash_SHA2_hash_512(msg, msg_len, mHash);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}

/**
P256 signature WITHOUT hashing first.

  This function is intended to receive a hash of the input.
  For convenience, we recommend using one of the hash-and-sign combined functions above.

  The argument `msg` MUST be at least 32 bytes (i.e. `msg_len >= 32`).

  NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
  smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
  reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
  need to perform the left-padding themselves.

  Input:
  • signature: uint8 [64]
  • msg: uint8 [msg_len]
  • private_key: uint8 [32]
  • nonce: uint8 [32]
  Output: bool, where True stands for the correct signature generation.
  False value means that an error has occurred.

  The private key and the nonce are expected to be more than 0 and less than the curve order.
  The message msg is expected to be hashed by a strong hash function,
  the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_sign_p256_without_hash(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  memcpy(mHash, msg, (uint32_t)32U * sizeof (uint8_t));
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_sign_msg_as_qelem(signature, m_q, private_key, nonce);
  return res;
}


/****************/
/* Verification */
/****************/

/*
  Verify a message signature. These functions internally validate the public key using validate_public_key.
*/

/**

  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification.
*/
bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}

/**

  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification.
*/
bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[48U] = { 0U };
  Hacl_Hash_SHA2_hash_384(msg, msg_len, mHash);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}

/**

  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification.
*/
bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[64U] = { 0U };
  Hacl_Hash_SHA2_hash_512(msg, msg_len, mHash);
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}

/**

  Input:
  • msg: uint8 [msg_len]
  • public_key: uint8 [64]
  • signature_r: uint8 [32]
  • signature_s: uint8 [32]
  Output: bool, where true stands for the correct signature verification.
  The message m is expected to be hashed by a strong hash function,
  the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_verif_without_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
)
{
  uint64_t m_q[4U] = { 0U };
  uint8_t mHash[32U] = { 0U };
  memcpy(mHash, msg, (uint32_t)32U * sizeof (uint8_t));
  uint8_t *mHash32 = mHash;
  bn_from_bytes_be4(m_q, mHash32);
  qmod_short(m_q, m_q);
  bool res = ecdsa_verify_msg_as_qelem(m_q, public_key, signature_r, signature_s);
  return res;
}


/******************/
/* Key validation */
/******************/

/**
Validate a public key.

  Input: public_key: uint8 [64].
  Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:
    • Verify that the public key is not the “point at infinity”, represented as O.
    • Verify that the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • Verify that y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_validate_public_key(uint8_t *public_key)
{
  uint64_t point_jac[12U] = { 0U };
  bool res = Hacl_Impl_P256_Point_load_point_vartime(point_jac, public_key);
  return res;
}

/**
Validate a private key, e.g. prior to signing.

  Input: private_key: uint8 [32].
  Output: bool, where true stands for the scalar to be more than 0 and less than order.
*/
bool Hacl_P256_validate_private_key(uint8_t *private_key)
{
  uint64_t bn_sk[4U] = { 0U };
  bn_from_bytes_be4(bn_sk, private_key);
  uint64_t res = bn_is_lt_order_and_gt_zero_mask4(bn_sk);
  return res == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}


/*****************************************/
/* Point representations and conversions */
/*****************************************/

/*
  Elliptic curve points have 2 32-byte coordinates (x, y) and can be represented in 3 ways:

  - "raw" form (64 bytes): the concatenation of the 2 coordinates, also known as "internal"
  - "compressed" form (33 bytes): first the sign byte of y (either 0x02 or 0x03), followed by x
  - "uncompressed" form (65 bytes): first a constant byte (always 0x04), followed by the "raw" form

  For all of the conversation functions below, the input and output MUST NOT overlap.
*/

/**
Convert 65-byte uncompressed to raw.

  The function errors out if the first byte is incorrect, or if the resulting point is invalid.

  Input:
  • pk: uint8 [65]
  • pk_raw: uint8 [64]
  Output: bool, where true stands for the correct decompression.
*/
bool Hacl_P256_uncompressed_to_raw(uint8_t *pk, uint8_t *pk_raw)
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
Convert 33-byte compressed to raw.

  The function errors out if the first byte is incorrect, or if the resulting point is invalid.

  Input:
  • pk: uint8 [33]
  • pk_raw: uint8 [64]
  Output: bool, where true stands for the correct decompression.
*/
bool Hacl_P256_compressed_to_raw(uint8_t *pk, uint8_t *pk_raw)
{
  uint64_t xa[4U] = { 0U };
  uint64_t ya[4U] = { 0U };
  uint8_t *pk_xb = pk + (uint32_t)1U;
  bool b = aff_point_decompress_vartime(xa, ya, pk);
  if (b)
  {
    memcpy(pk_raw, pk_xb, (uint32_t)32U * sizeof (uint8_t));
    bn_to_bytes_be4(pk_raw + (uint32_t)32U, ya);
  }
  return b;
}

/**
Convert raw to 65-byte uncompressed.

  This function effectively prepends a 0x04 byte.

  Input:
  • pk_raw: uint8 [64]
  • pk: uint8 [65]
*/
void Hacl_P256_raw_to_uncompressed(uint8_t *pk_raw, uint8_t *pk)
{
  pk[0U] = (uint8_t)0x04U;
  memcpy(pk + (uint32_t)1U, pk_raw, (uint32_t)64U * sizeof (uint8_t));
}

/**
Convert raw to 33-byte compressed.

  Input: pk_raw: uint8 [64]
  Output: pk: uint8 [33]
*/
void Hacl_P256_raw_to_compressed(uint8_t *pk_raw, uint8_t *pk)
{
  uint8_t *pk_x = pk_raw;
  uint8_t *pk_y = pk_raw + (uint32_t)32U;
  uint64_t bn_f[4U] = { 0U };
  bn_from_bytes_be4(bn_f, pk_y);
  uint64_t is_odd_f = bn_f[0U] & (uint64_t)1U;
  pk[0U] = (uint8_t)is_odd_f + (uint8_t)0x02U;
  memcpy(pk + (uint32_t)1U, pk_x, (uint32_t)32U * sizeof (uint8_t));
}


/******************/
/* ECDH agreement */
/******************/

/**
Convert a private key into a raw public key.

  This function performs no key validation.

  Input: private_key: uint8 [32]
  Output: public_key: uint8 [64]
  Returns:
  - `true`, for success, meaning the public key is not a point at infinity
  - `false`, otherwise.

  `scalar` and `result` MUST NOT overlap.
*/
bool Hacl_P256_dh_initiator(uint8_t *public_key, uint8_t *private_key)
{
  uint64_t pk[12U] = { 0U };
  Hacl_Impl_P256_PointMul_point_mul_g_bytes(pk, private_key);
  uint64_t flag = Hacl_Impl_P256_Point_is_point_at_inf(pk);
  Hacl_Impl_P256_Point_aff_point_store(public_key, pk);
  return flag == (uint64_t)0U;
}

/**
ECDH key agreement.

  This function takes a 32-byte secret key, another party's 64-byte raw public key,
  and computeds the 64-byte ECDH shared key.

  This function ONLY validates the public key.

  Input:
  • their_public_key: uint8 [64]
  • private_key: uint8 [32]
  • shared_secret: uint8 [64]
  Output: bool, where True stands for the correct key generation.
  False value means that an error has occurred (possibly the provided public key was incorrect or
  the result represents point at infinity).
*/
bool
Hacl_P256_dh_responder(uint8_t *shared_secret, uint8_t *their_pubkey, uint8_t *private_key)
{
  uint64_t ss[12U] = { 0U };
  uint64_t pk[12U] = { 0U };
  bool is_pk_valid = Hacl_Impl_P256_Point_load_point_vartime(pk, their_pubkey);
  uint64_t flag;
  if (is_pk_valid)
  {
    Hacl_Impl_P256_PointMul_point_mul_bytes(ss, pk, private_key);
    flag = Hacl_Impl_P256_Point_is_point_at_inf(ss);
  }
  else
  {
    flag = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  }
  Hacl_Impl_P256_Point_aff_point_store(shared_secret, ss);
  return flag == (uint64_t)0U;
}

