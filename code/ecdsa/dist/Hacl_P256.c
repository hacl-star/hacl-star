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


#include "Hacl_P256.h"

static inline void mul64(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static inline void copy_conditional_p256(uint64_t *out, uint64_t *x, uint64_t mask)
{
  uint32_t len = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t x_i = x[i];
    uint64_t out_i = out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    out[i] = r_i;
  }
}

static inline void cmovznz4_p256(uint64_t cin, uint64_t *x, uint64_t *y, uint64_t *r)
{
  uint64_t mask = ~FStar_UInt64_eq_mask(cin, (uint64_t)0U);
  uint32_t len = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t x_i = x[i];
    uint64_t y_i = y[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    r[i] = r_i;
  }
}

static inline uint64_t mul_wide_add2_u64(uint64_t a, uint64_t b, uint64_t c_in, uint64_t *out)
{
  uint64_t out0 = out[0U];
  uint128_t res = (uint128_t)a * b + (uint128_t)c_in + (uint128_t)out0;
  out[0U] = (uint64_t)res;
  return (uint64_t)(res >> (uint32_t)64U);
}

static inline uint64_t
bn_add_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  return c;
}

static inline void felem_add_p256(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len0 / (uint32_t)4U * (uint32_t)4U; i < len0; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = out + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t t = c0;
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len1 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = out[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = out[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r = c;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      t,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p256(carry, tempBuffer, out, out);
}

static inline void felem_double_p256(uint64_t *arg1, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg1[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len0 / (uint32_t)4U * (uint32_t)4U; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg1[i];
    uint64_t *res_i = out + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t t = c0;
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len1 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = out[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = out[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r = c;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      t,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p256(carry, tempBuffer, out, out);
}

static inline void felem_sub_p256(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = out + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t t = c;
  uint64_t y0 = (uint64_t)0U - t;
  uint64_t y1 = ((uint64_t)0U - t) >> (uint32_t)32U;
  uint64_t y2 = (uint64_t)0U;
  uint64_t y3 = t - (t << (uint32_t)32U);
  uint64_t *r0 = out;
  uint64_t *r1 = out + (uint32_t)1U;
  uint64_t *r2 = out + (uint32_t)2U;
  uint64_t *r3 = out + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, out[0U], y0, r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc, out[1U], y1, r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, out[2U], y2, r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, out[3U], y3, r3);
  uint64_t r = cc3;
}

static inline void
montgomery_multiplication_buffer_dh_p256(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  uint32_t resLen = len1 + len1;
  memset(t, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t a_i = a[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c = mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    t[len1 + i0] = r;
  }
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t *uu____0 = t2 + (uint32_t)4U;
    uint32_t len31 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len31; i++)
    {
      uu____0[i] = (uint64_t)0U;
    }
    uint64_t temp = (uint64_t)0U;
    uint64_t f0 = (uint64_t)0xffffffffffffffffU;
    uint64_t f1 = (uint64_t)0xffffffffU;
    uint64_t f3 = (uint64_t)0xffffffff00000001U;
    uint64_t *o0 = t2;
    uint64_t *o1 = t2 + (uint32_t)1U;
    uint64_t *o2 = t2 + (uint32_t)2U;
    uint64_t *o3 = t2 + (uint32_t)3U;
    uint64_t *o4 = t2 + (uint32_t)4U;
    mul64(f0, t10, o0, &temp);
    uint64_t h0 = temp;
    mul64(f1, t10, o1, &temp);
    uint64_t l = o1[0U];
    uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
    uint64_t h = temp;
    o2[0U] = h + c1;
    mul64(f3, t10, o3, o4);
    uint32_t len32 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      uint64_t *res_i0 = t2 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = t2 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = t2 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = t2 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
    }
    for (uint32_t i = len32 / (uint32_t)4U * (uint32_t)4U; i < len32; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      uint64_t *res_i = t2 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
    }
    uint64_t carry = c;
    uint32_t len3 = (uint32_t)7U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len2 = (uint32_t)4U;
  uint64_t cin = t[len2];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len4 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t210 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t211 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t212 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
  }
  for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t21 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
  }
  uint64_t r = c;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p256(carry, tempBuffer, x_, result);
}

static inline void montgomery_square_buffer_dh_p256(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  uint32_t resLen = len1 + len1;
  memset(t, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    t[i0 + i0] = r;
  }
  uint64_t c0 = bn_add_eq_len_u64(resLen, t, t, t);
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t tmp[resLen];
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t res = (uint128_t)a[i] * a[i];
    uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
    uint64_t lo = (uint64_t)res;
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = bn_add_eq_len_u64(resLen, t, tmp, t);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t *uu____0 = t2 + (uint32_t)4U;
    uint32_t len31 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len31; i++)
    {
      uu____0[i] = (uint64_t)0U;
    }
    uint64_t temp = (uint64_t)0U;
    uint64_t f0 = (uint64_t)0xffffffffffffffffU;
    uint64_t f1 = (uint64_t)0xffffffffU;
    uint64_t f3 = (uint64_t)0xffffffff00000001U;
    uint64_t *o0 = t2;
    uint64_t *o1 = t2 + (uint32_t)1U;
    uint64_t *o2 = t2 + (uint32_t)2U;
    uint64_t *o3 = t2 + (uint32_t)3U;
    uint64_t *o4 = t2 + (uint32_t)4U;
    mul64(f0, t10, o0, &temp);
    uint64_t h0 = temp;
    mul64(f1, t10, o1, &temp);
    uint64_t l = o1[0U];
    uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
    uint64_t h = temp;
    o2[0U] = h + c10;
    mul64(f3, t10, o3, o4);
    uint32_t len32 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      uint64_t *res_i0 = t2 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = t2 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = t2 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = t2 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
    }
    for (uint32_t i = len32 / (uint32_t)4U * (uint32_t)4U; i < len32; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      uint64_t *res_i = t2 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
    }
    uint64_t carry = c;
    uint32_t len3 = (uint32_t)7U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len2 = (uint32_t)4U;
  uint64_t cin = t[len2];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len4 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t210 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t211 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t212 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
  }
  for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t21 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
  }
  uint64_t r = c;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p256(carry, tempBuffer, x_, result);
}

static inline void exponent_p256(uint64_t *t, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)4U;
  uint64_t *t2 = tempBuffer + (uint32_t)8U;
  uint64_t *t3 = tempBuffer + (uint32_t)12U;
  uint64_t *t4 = tempBuffer + (uint32_t)16U;
  uint64_t *t5 = tempBuffer + (uint32_t)20U;
  uint64_t *t6 = tempBuffer + (uint32_t)24U;
  uint64_t *t7 = tempBuffer + (uint32_t)28U;
  montgomery_square_buffer_dh_p256(t, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t, t2);
  montgomery_square_buffer_dh_p256(t2, t0);
  montgomery_square_buffer_dh_p256(t0, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t2, t6);
  montgomery_square_buffer_dh_p256(t6, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)3U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t6, t7);
  montgomery_square_buffer_dh_p256(t7, t0);
  montgomery_square_buffer_dh_p256(t0, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t2, t1);
  montgomery_square_buffer_dh_p256(t1, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t1, t3);
  montgomery_square_buffer_dh_p256(t3, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)9U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t1, t4);
  montgomery_square_buffer_dh_p256(t4, t0);
  montgomery_square_buffer_dh_p256(t0, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t2, t5);
  montgomery_square_buffer_dh_p256(t5, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)31U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)128U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t5, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t5, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)30U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t4, t0);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i++)
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t, result);
}

static inline void point_double_p256(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *pY = p + len;
  uint64_t *pZ = p + (uint32_t)2U * len;
  uint64_t *x3 = result;
  uint64_t *y3 = result + len;
  uint64_t *z3 = result + (uint32_t)2U * len;
  uint64_t *delta = tempBuffer;
  uint64_t *gamma = tempBuffer + len;
  uint64_t *beta = tempBuffer + (uint32_t)2U * len;
  uint64_t *alpha = tempBuffer + (uint32_t)3U * len;
  uint64_t *fourBeta = tempBuffer + (uint32_t)4U * len;
  uint64_t *eightBeta = tempBuffer + (uint32_t)5U * len;
  uint64_t *eightGamma = tempBuffer + (uint32_t)6U * len;
  uint64_t *tmp = tempBuffer + (uint32_t)7U * len;
  uint32_t coordinateLen = (uint32_t)4U;
  uint64_t *pX1 = p;
  uint64_t *pY1 = p + coordinateLen;
  uint64_t *pZ1 = p + (uint32_t)2U * coordinateLen;
  uint64_t *a0 = tmp;
  uint64_t *a1 = tmp + coordinateLen;
  uint64_t *alpha0 = tmp + (uint32_t)2U * coordinateLen;
  montgomery_square_buffer_dh_p256(pZ1, delta);
  montgomery_square_buffer_dh_p256(pY1, gamma);
  montgomery_multiplication_buffer_dh_p256(pX1, gamma, beta);
  felem_sub_p256(pX1, delta, a0);
  felem_add_p256(pX1, delta, a1);
  montgomery_multiplication_buffer_dh_p256(a0, a1, alpha0);
  felem_add_p256(alpha0, alpha0, alpha);
  felem_add_p256(alpha0, alpha, alpha);
  montgomery_square_buffer_dh_p256(alpha, x3);
  felem_add_p256(beta, beta, fourBeta);
  felem_add_p256(fourBeta, fourBeta, fourBeta);
  felem_add_p256(fourBeta, fourBeta, eightBeta);
  felem_sub_p256(x3, eightBeta, x3);
  felem_add_p256(pY, pZ, z3);
  montgomery_square_buffer_dh_p256(z3, z3);
  felem_sub_p256(z3, gamma, z3);
  felem_sub_p256(z3, delta, z3);
  felem_sub_p256(fourBeta, x3, y3);
  montgomery_multiplication_buffer_dh_p256(alpha, y3, y3);
  montgomery_square_buffer_dh_p256(gamma, gamma);
  felem_add_p256(gamma, gamma, eightGamma);
  felem_add_p256(eightGamma, eightGamma, eightGamma);
  felem_add_p256(eightGamma, eightGamma, eightGamma);
  felem_sub_p256(y3, eightGamma, y3);
}

static inline void
point_add_p256(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t12 = tempBuffer;
  uint64_t *t5 = tempBuffer + (uint32_t)48U;
  uint64_t *t4 = t12;
  uint64_t *u10 = t12 + (uint32_t)16U;
  uint64_t *u20 = t12 + (uint32_t)20U;
  uint64_t *s10 = t12 + (uint32_t)24U;
  uint64_t *s20 = t12 + (uint32_t)28U;
  uint64_t *pX = p;
  uint64_t *pY = p + (uint32_t)4U;
  uint64_t *pZ = p + (uint32_t)8U;
  uint64_t *qX = q;
  uint64_t *qY = q + (uint32_t)4U;
  uint64_t *qZ = q + (uint32_t)8U;
  uint64_t *z2Square = t4;
  uint64_t *z1Square = t4 + (uint32_t)4U;
  uint64_t *z2Cube = t4 + (uint32_t)8U;
  uint64_t *z1Cube = t4 + (uint32_t)12U;
  montgomery_square_buffer_dh_p256(qZ, z2Square);
  montgomery_square_buffer_dh_p256(pZ, z1Square);
  montgomery_multiplication_buffer_dh_p256(z2Square, qZ, z2Cube);
  montgomery_multiplication_buffer_dh_p256(z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer_dh_p256(z2Square, pX, u10);
  montgomery_multiplication_buffer_dh_p256(z1Square, qX, u20);
  montgomery_multiplication_buffer_dh_p256(z2Cube, pY, s10);
  montgomery_multiplication_buffer_dh_p256(z1Cube, qY, s20);
  uint64_t *t40 = t12;
  uint64_t *u1 = t12 + (uint32_t)16U;
  uint64_t *u2 = t12 + (uint32_t)20U;
  uint64_t *s11 = t12 + (uint32_t)24U;
  uint64_t *s2 = t12 + (uint32_t)28U;
  uint64_t *h0 = t12 + (uint32_t)32U;
  uint64_t *r0 = t12 + (uint32_t)36U;
  uint64_t *uh0 = t12 + (uint32_t)40U;
  uint64_t *hCube0 = t12 + (uint32_t)44U;
  uint64_t *temp = t40;
  felem_sub_p256(u2, u1, h0);
  felem_sub_p256(s2, s11, r0);
  montgomery_square_buffer_dh_p256(h0, temp);
  montgomery_multiplication_buffer_dh_p256(temp, u1, uh0);
  montgomery_multiplication_buffer_dh_p256(temp, h0, hCube0);
  uint64_t *x3y3z3u1u2s1s2 = t12;
  uint64_t *rhuhhCube = t12 + (uint32_t)32U;
  uint64_t *h = rhuhhCube;
  uint64_t *r = rhuhhCube + (uint32_t)4U;
  uint64_t *uh = rhuhhCube + (uint32_t)8U;
  uint64_t *hCube = rhuhhCube + (uint32_t)12U;
  uint64_t *s1 = x3y3z3u1u2s1s2 + (uint32_t)24U;
  uint64_t *x3 = t5;
  uint64_t *tempBuffer30 = t5 + (uint32_t)4U;
  uint64_t *rSquare = tempBuffer30;
  uint64_t *rH = tempBuffer30 + (uint32_t)4U;
  uint64_t *twoUh = tempBuffer30 + (uint32_t)8U;
  montgomery_square_buffer_dh_p256(r, rSquare);
  felem_sub_p256(rSquare, hCube, rH);
  felem_add_p256(uh, uh, twoUh);
  felem_sub_p256(rH, twoUh, x3);
  uint64_t *x30 = t5;
  uint64_t *y3 = t5 + (uint32_t)4U;
  uint64_t *tempBuffer3 = t5 + (uint32_t)8U;
  uint64_t *s1hCube = tempBuffer3;
  uint64_t *u1hx3 = tempBuffer3 + (uint32_t)4U;
  uint64_t *ru1hx3 = tempBuffer3 + (uint32_t)8U;
  montgomery_multiplication_buffer_dh_p256(s1, hCube, s1hCube);
  felem_sub_p256(uh, x30, u1hx3);
  montgomery_multiplication_buffer_dh_p256(u1hx3, r, ru1hx3);
  felem_sub_p256(ru1hx3, s1hCube, y3);
  uint64_t *z1 = p + (uint32_t)8U;
  uint64_t *z2 = q + (uint32_t)8U;
  uint64_t *z3 = t5 + (uint32_t)8U;
  uint64_t *t1 = t5 + (uint32_t)12U;
  uint64_t *z1z2 = t1;
  montgomery_multiplication_buffer_dh_p256(z1, z2, z1z2);
  montgomery_multiplication_buffer_dh_p256(z1z2, h, z3);
  uint64_t *x3_out = t5;
  uint64_t *y3_out = t5 + (uint32_t)4U;
  uint64_t *z3_out = t5 + (uint32_t)8U;
  uint64_t *z = p + (uint32_t)8U;
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len0 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len0; i++)
  {
    uint64_t a_i = z[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t mask = tmp1;
  uint64_t *p_x0 = q;
  uint64_t *p_y0 = q + (uint32_t)4U;
  uint64_t *p_z0 = q + (uint32_t)8U;
  copy_conditional_p256(x3_out, p_x0, mask);
  copy_conditional_p256(y3_out, p_y0, mask);
  copy_conditional_p256(z3_out, p_z0, mask);
  uint64_t *z0 = q + (uint32_t)8U;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t a_i = z0[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t mask0 = tmp;
  uint64_t *p_x = p;
  uint64_t *p_y = p + (uint32_t)4U;
  uint64_t *p_z = p + (uint32_t)8U;
  copy_conditional_p256(x3_out, p_x, mask0);
  copy_conditional_p256(y3_out, p_y, mask0);
  copy_conditional_p256(z3_out, p_z, mask0);
  memcpy(result, x3_out, (uint32_t)4U * sizeof (uint64_t));
  memcpy(result + (uint32_t)4U, y3_out, (uint32_t)4U * sizeof (uint64_t));
  memcpy(result + (uint32_t)8U, z3_out, (uint32_t)4U * sizeof (uint64_t));
}

static inline void
montgomery_ladderP256L(uint64_t *p, uint64_t *q, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint32_t cycleLoop = (uint32_t)4U * (uint32_t)8U * (uint32_t)8U;
  for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
  {
    uint32_t bit0 = (uint32_t)4U * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - i0;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)4U
      * (uint32_t)8U
      - (uint32_t)1U
      - bit0 / (uint32_t)8U]
      >> bit0 % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len0 = (uint32_t)12U;
    for (uint32_t i = (uint32_t)0U; i < len0; i++)
    {
      uint64_t dummy = mask & (p[i] ^ q[i]);
      p[i] = p[i] ^ dummy;
      q[i] = q[i] ^ dummy;
    }
    point_add_p256(p, q, q, tempBuffer);
    point_double_p256(p, p, tempBuffer);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len = (uint32_t)12U;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint64_t dummy = mask0 & (p[i] ^ q[i]);
      p[i] = p[i] ^ dummy;
      q[i] = q[i] ^ dummy;
    }
  }
}

static inline void solinas_reduction_impl_p256(uint64_t *i, uint64_t *o)
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
  uint64_t as_uint64_high0 = (uint64_t)c1;
  uint64_t as_uint64_high1 = as_uint64_high0 << (uint32_t)32U;
  uint64_t as_uint64_low0 = (uint64_t)c0;
  uint64_t b0 = as_uint64_low0 ^ as_uint64_high1;
  uint64_t as_uint64_high2 = (uint64_t)c3;
  uint64_t as_uint64_high10 = as_uint64_high2 << (uint32_t)32U;
  uint64_t as_uint64_low1 = (uint64_t)c2;
  uint64_t b1 = as_uint64_low1 ^ as_uint64_high10;
  uint64_t as_uint64_high3 = (uint64_t)c5;
  uint64_t as_uint64_high11 = as_uint64_high3 << (uint32_t)32U;
  uint64_t as_uint64_low2 = (uint64_t)c4;
  uint64_t b20 = as_uint64_low2 ^ as_uint64_high11;
  uint64_t as_uint64_high4 = (uint64_t)c7;
  uint64_t as_uint64_high12 = as_uint64_high4 << (uint32_t)32U;
  uint64_t as_uint64_low3 = (uint64_t)c6;
  uint64_t b3 = as_uint64_low3 ^ as_uint64_high12;
  t01[0U] = b0;
  t01[1U] = b1;
  t01[2U] = b20;
  t01[3U] = b3;
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer1[len];
  memset(tempBuffer1, 0U, len * sizeof (uint64_t));
  uint64_t
  p0[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len10 = (uint32_t)4U;
  uint64_t c16 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len10 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t01[(uint32_t)4U * i8];
    uint64_t t220 = p0[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i8;
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t12, t220, res_i0);
    uint64_t t120 = t01[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p0[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i8 + (uint32_t)1U;
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t120, t221, res_i1);
    uint64_t t121 = t01[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p0[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i8 + (uint32_t)2U;
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t121, t222, res_i2);
    uint64_t t122 = t01[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p0[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i8 + (uint32_t)3U;
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t122, t22, res_i);
  }
  for (uint32_t i8 = len10 / (uint32_t)4U * (uint32_t)4U; i8 < len10; i8++)
  {
    uint64_t t12 = t01[i8];
    uint64_t t22 = p0[i8];
    uint64_t *res_i = tempBuffer1 + i8;
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t12, t22, res_i);
  }
  uint64_t r = c16;
  uint64_t r0 = r;
  cmovznz4_p256(r0, tempBuffer1, t01, t01);
  uint64_t b00 = (uint64_t)0U;
  uint64_t as_uint64_high5 = (uint64_t)c11;
  uint64_t as_uint64_high13 = as_uint64_high5 << (uint32_t)32U;
  uint64_t as_uint64_low4 = (uint64_t)(uint32_t)0U;
  uint64_t b10 = as_uint64_low4 ^ as_uint64_high13;
  uint64_t as_uint64_high6 = (uint64_t)c13;
  uint64_t as_uint64_high14 = as_uint64_high6 << (uint32_t)32U;
  uint64_t as_uint64_low5 = (uint64_t)c12;
  uint64_t b21 = as_uint64_low5 ^ as_uint64_high14;
  uint64_t as_uint64_high7 = (uint64_t)c15;
  uint64_t as_uint64_high15 = as_uint64_high7 << (uint32_t)32U;
  uint64_t as_uint64_low6 = (uint64_t)c14;
  uint64_t b30 = as_uint64_low6 ^ as_uint64_high15;
  t110[0U] = b00;
  t110[1U] = b10;
  t110[2U] = b21;
  t110[3U] = b30;
  uint32_t len0 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len0);
  uint64_t tempBuffer10[len0];
  memset(tempBuffer10, 0U, len0 * sizeof (uint64_t));
  uint64_t
  p1[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len11 = (uint32_t)4U;
  uint64_t c17 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len11 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t110[(uint32_t)4U * i8];
    uint64_t t220 = p1[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer10 + (uint32_t)4U * i8;
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t12, t220, res_i0);
    uint64_t t120 = t110[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p1[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer10 + (uint32_t)4U * i8 + (uint32_t)1U;
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t120, t221, res_i1);
    uint64_t t121 = t110[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p1[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer10 + (uint32_t)4U * i8 + (uint32_t)2U;
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t121, t222, res_i2);
    uint64_t t122 = t110[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p1[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer10 + (uint32_t)4U * i8 + (uint32_t)3U;
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t122, t22, res_i);
  }
  for (uint32_t i8 = len11 / (uint32_t)4U * (uint32_t)4U; i8 < len11; i8++)
  {
    uint64_t t12 = t110[i8];
    uint64_t t22 = p1[i8];
    uint64_t *res_i = tempBuffer10 + i8;
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t12, t22, res_i);
  }
  uint64_t r1 = c17;
  uint64_t r2 = r1;
  cmovznz4_p256(r2, tempBuffer10, t110, t110);
  uint64_t b01 = (uint64_t)0U;
  uint64_t as_uint64_high8 = (uint64_t)c12;
  uint64_t as_uint64_high16 = as_uint64_high8 << (uint32_t)32U;
  uint64_t as_uint64_low7 = (uint64_t)(uint32_t)0U;
  uint64_t b11 = as_uint64_low7 ^ as_uint64_high16;
  uint64_t as_uint64_high9 = (uint64_t)c14;
  uint64_t as_uint64_high17 = as_uint64_high9 << (uint32_t)32U;
  uint64_t as_uint64_low8 = (uint64_t)c13;
  uint64_t b22 = as_uint64_low8 ^ as_uint64_high17;
  uint64_t as_uint64_high18 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high19 = as_uint64_high18 << (uint32_t)32U;
  uint64_t as_uint64_low9 = (uint64_t)c15;
  uint64_t b31 = as_uint64_low9 ^ as_uint64_high19;
  t210[0U] = b01;
  t210[1U] = b11;
  t210[2U] = b22;
  t210[3U] = b31;
  uint64_t as_uint64_high20 = (uint64_t)c9;
  uint64_t as_uint64_high110 = as_uint64_high20 << (uint32_t)32U;
  uint64_t as_uint64_low10 = (uint64_t)c8;
  uint64_t b02 = as_uint64_low10 ^ as_uint64_high110;
  uint64_t as_uint64_high21 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high111 = as_uint64_high21 << (uint32_t)32U;
  uint64_t as_uint64_low11 = (uint64_t)c10;
  uint64_t b12 = as_uint64_low11 ^ as_uint64_high111;
  uint64_t b23 = (uint64_t)0U;
  uint64_t as_uint64_high22 = (uint64_t)c15;
  uint64_t as_uint64_high112 = as_uint64_high22 << (uint32_t)32U;
  uint64_t as_uint64_low12 = (uint64_t)c14;
  uint64_t b32 = as_uint64_low12 ^ as_uint64_high112;
  t310[0U] = b02;
  t310[1U] = b12;
  t310[2U] = b23;
  t310[3U] = b32;
  uint32_t len2 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len2);
  uint64_t tempBuffer11[len2];
  memset(tempBuffer11, 0U, len2 * sizeof (uint64_t));
  uint64_t
  p2[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len12 = (uint32_t)4U;
  uint64_t c18 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len12 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t310[(uint32_t)4U * i8];
    uint64_t t220 = p2[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer11 + (uint32_t)4U * i8;
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t12, t220, res_i0);
    uint64_t t120 = t310[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p2[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer11 + (uint32_t)4U * i8 + (uint32_t)1U;
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t120, t221, res_i1);
    uint64_t t121 = t310[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p2[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer11 + (uint32_t)4U * i8 + (uint32_t)2U;
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t121, t222, res_i2);
    uint64_t t122 = t310[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p2[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer11 + (uint32_t)4U * i8 + (uint32_t)3U;
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t122, t22, res_i);
  }
  for (uint32_t i8 = len12 / (uint32_t)4U * (uint32_t)4U; i8 < len12; i8++)
  {
    uint64_t t12 = t310[i8];
    uint64_t t22 = p2[i8];
    uint64_t *res_i = tempBuffer11 + i8;
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t12, t22, res_i);
  }
  uint64_t r3 = c18;
  uint64_t r4 = r3;
  cmovznz4_p256(r4, tempBuffer11, t310, t310);
  uint64_t as_uint64_high23 = (uint64_t)c10;
  uint64_t as_uint64_high113 = as_uint64_high23 << (uint32_t)32U;
  uint64_t as_uint64_low13 = (uint64_t)c9;
  uint64_t b03 = as_uint64_low13 ^ as_uint64_high113;
  uint64_t as_uint64_high24 = (uint64_t)c13;
  uint64_t as_uint64_high114 = as_uint64_high24 << (uint32_t)32U;
  uint64_t as_uint64_low14 = (uint64_t)c11;
  uint64_t b13 = as_uint64_low14 ^ as_uint64_high114;
  uint64_t as_uint64_high25 = (uint64_t)c15;
  uint64_t as_uint64_high115 = as_uint64_high25 << (uint32_t)32U;
  uint64_t as_uint64_low15 = (uint64_t)c14;
  uint64_t b24 = as_uint64_low15 ^ as_uint64_high115;
  uint64_t as_uint64_high26 = (uint64_t)c8;
  uint64_t as_uint64_high116 = as_uint64_high26 << (uint32_t)32U;
  uint64_t as_uint64_low16 = (uint64_t)c13;
  uint64_t b33 = as_uint64_low16 ^ as_uint64_high116;
  t410[0U] = b03;
  t410[1U] = b13;
  t410[2U] = b24;
  t410[3U] = b33;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer12[len3];
  memset(tempBuffer12, 0U, len3 * sizeof (uint64_t));
  uint64_t
  p3[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len13 = (uint32_t)4U;
  uint64_t c19 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len13 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t410[(uint32_t)4U * i8];
    uint64_t t220 = p3[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer12 + (uint32_t)4U * i8;
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t12, t220, res_i0);
    uint64_t t120 = t410[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p3[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer12 + (uint32_t)4U * i8 + (uint32_t)1U;
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t120, t221, res_i1);
    uint64_t t121 = t410[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p3[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer12 + (uint32_t)4U * i8 + (uint32_t)2U;
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t121, t222, res_i2);
    uint64_t t122 = t410[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p3[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer12 + (uint32_t)4U * i8 + (uint32_t)3U;
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t122, t22, res_i);
  }
  for (uint32_t i8 = len13 / (uint32_t)4U * (uint32_t)4U; i8 < len13; i8++)
  {
    uint64_t t12 = t410[i8];
    uint64_t t22 = p3[i8];
    uint64_t *res_i = tempBuffer12 + i8;
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t12, t22, res_i);
  }
  uint64_t r5 = c19;
  uint64_t r6 = r5;
  cmovznz4_p256(r6, tempBuffer12, t410, t410);
  uint64_t as_uint64_high27 = (uint64_t)c12;
  uint64_t as_uint64_high117 = as_uint64_high27 << (uint32_t)32U;
  uint64_t as_uint64_low17 = (uint64_t)c11;
  uint64_t b04 = as_uint64_low17 ^ as_uint64_high117;
  uint64_t as_uint64_high28 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high118 = as_uint64_high28 << (uint32_t)32U;
  uint64_t as_uint64_low18 = (uint64_t)c13;
  uint64_t b14 = as_uint64_low18 ^ as_uint64_high118;
  uint64_t b25 = (uint64_t)0U;
  uint64_t as_uint64_high29 = (uint64_t)c10;
  uint64_t as_uint64_high119 = as_uint64_high29 << (uint32_t)32U;
  uint64_t as_uint64_low19 = (uint64_t)c8;
  uint64_t b34 = as_uint64_low19 ^ as_uint64_high119;
  t510[0U] = b04;
  t510[1U] = b14;
  t510[2U] = b25;
  t510[3U] = b34;
  uint32_t len4 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len4);
  uint64_t tempBuffer13[len4];
  memset(tempBuffer13, 0U, len4 * sizeof (uint64_t));
  uint64_t
  p4[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len14 = (uint32_t)4U;
  uint64_t c20 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len14 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t510[(uint32_t)4U * i8];
    uint64_t t220 = p4[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer13 + (uint32_t)4U * i8;
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t12, t220, res_i0);
    uint64_t t120 = t510[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p4[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer13 + (uint32_t)4U * i8 + (uint32_t)1U;
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t120, t221, res_i1);
    uint64_t t121 = t510[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p4[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer13 + (uint32_t)4U * i8 + (uint32_t)2U;
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t121, t222, res_i2);
    uint64_t t122 = t510[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p4[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer13 + (uint32_t)4U * i8 + (uint32_t)3U;
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t122, t22, res_i);
  }
  for (uint32_t i8 = len14 / (uint32_t)4U * (uint32_t)4U; i8 < len14; i8++)
  {
    uint64_t t12 = t510[i8];
    uint64_t t22 = p4[i8];
    uint64_t *res_i = tempBuffer13 + i8;
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t12, t22, res_i);
  }
  uint64_t r7 = c20;
  uint64_t r8 = r7;
  cmovznz4_p256(r8, tempBuffer13, t510, t510);
  uint64_t as_uint64_high30 = (uint64_t)c13;
  uint64_t as_uint64_high120 = as_uint64_high30 << (uint32_t)32U;
  uint64_t as_uint64_low20 = (uint64_t)c12;
  uint64_t b05 = as_uint64_low20 ^ as_uint64_high120;
  uint64_t as_uint64_high31 = (uint64_t)c15;
  uint64_t as_uint64_high121 = as_uint64_high31 << (uint32_t)32U;
  uint64_t as_uint64_low21 = (uint64_t)c14;
  uint64_t b15 = as_uint64_low21 ^ as_uint64_high121;
  uint64_t b2 = (uint64_t)0U;
  uint64_t as_uint64_high32 = (uint64_t)c11;
  uint64_t as_uint64_high122 = as_uint64_high32 << (uint32_t)32U;
  uint64_t as_uint64_low22 = (uint64_t)c9;
  uint64_t b35 = as_uint64_low22 ^ as_uint64_high122;
  t610[0U] = b05;
  t610[1U] = b15;
  t610[2U] = b2;
  t610[3U] = b35;
  uint32_t len5 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len5);
  uint64_t tempBuffer14[len5];
  memset(tempBuffer14, 0U, len5 * sizeof (uint64_t));
  uint64_t
  p5[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len15 = (uint32_t)4U;
  uint64_t c21 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len15 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t610[(uint32_t)4U * i8];
    uint64_t t220 = p5[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer14 + (uint32_t)4U * i8;
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t12, t220, res_i0);
    uint64_t t120 = t610[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p5[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer14 + (uint32_t)4U * i8 + (uint32_t)1U;
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t120, t221, res_i1);
    uint64_t t121 = t610[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p5[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer14 + (uint32_t)4U * i8 + (uint32_t)2U;
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t121, t222, res_i2);
    uint64_t t122 = t610[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p5[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer14 + (uint32_t)4U * i8 + (uint32_t)3U;
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t122, t22, res_i);
  }
  for (uint32_t i8 = len15 / (uint32_t)4U * (uint32_t)4U; i8 < len15; i8++)
  {
    uint64_t t12 = t610[i8];
    uint64_t t22 = p5[i8];
    uint64_t *res_i = tempBuffer14 + i8;
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t12, t22, res_i);
  }
  uint64_t r9 = c21;
  uint64_t r10 = r9;
  cmovznz4_p256(r10, tempBuffer14, t610, t610);
  uint64_t as_uint64_high33 = (uint64_t)c14;
  uint64_t as_uint64_high123 = as_uint64_high33 << (uint32_t)32U;
  uint64_t as_uint64_low23 = (uint64_t)c13;
  uint64_t b06 = as_uint64_low23 ^ as_uint64_high123;
  uint64_t as_uint64_high34 = (uint64_t)c8;
  uint64_t as_uint64_high124 = as_uint64_high34 << (uint32_t)32U;
  uint64_t as_uint64_low24 = (uint64_t)c15;
  uint64_t b16 = as_uint64_low24 ^ as_uint64_high124;
  uint64_t as_uint64_high35 = (uint64_t)c10;
  uint64_t as_uint64_high125 = as_uint64_high35 << (uint32_t)32U;
  uint64_t as_uint64_low25 = (uint64_t)c9;
  uint64_t b26 = as_uint64_low25 ^ as_uint64_high125;
  uint64_t as_uint64_high36 = (uint64_t)c12;
  uint64_t as_uint64_high126 = as_uint64_high36 << (uint32_t)32U;
  uint64_t as_uint64_low26 = (uint64_t)(uint32_t)0U;
  uint64_t b36 = as_uint64_low26 ^ as_uint64_high126;
  t710[0U] = b06;
  t710[1U] = b16;
  t710[2U] = b26;
  t710[3U] = b36;
  uint32_t len6 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len6);
  uint64_t tempBuffer15[len6];
  memset(tempBuffer15, 0U, len6 * sizeof (uint64_t));
  uint64_t
  p6[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len16 = (uint32_t)4U;
  uint64_t c22 = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len16 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t710[(uint32_t)4U * i8];
    uint64_t t220 = p6[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer15 + (uint32_t)4U * i8;
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t12, t220, res_i0);
    uint64_t t120 = t710[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p6[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer15 + (uint32_t)4U * i8 + (uint32_t)1U;
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t120, t221, res_i1);
    uint64_t t121 = t710[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p6[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer15 + (uint32_t)4U * i8 + (uint32_t)2U;
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t121, t222, res_i2);
    uint64_t t122 = t710[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p6[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer15 + (uint32_t)4U * i8 + (uint32_t)3U;
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t122, t22, res_i);
  }
  for (uint32_t i8 = len16 / (uint32_t)4U * (uint32_t)4U; i8 < len16; i8++)
  {
    uint64_t t12 = t710[i8];
    uint64_t t22 = p6[i8];
    uint64_t *res_i = tempBuffer15 + i8;
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t12, t22, res_i);
  }
  uint64_t r11 = c22;
  uint64_t r12 = r11;
  cmovznz4_p256(r12, tempBuffer15, t710, t710);
  uint64_t as_uint64_high37 = (uint64_t)c15;
  uint64_t as_uint64_high127 = as_uint64_high37 << (uint32_t)32U;
  uint64_t as_uint64_low27 = (uint64_t)c14;
  uint64_t b07 = as_uint64_low27 ^ as_uint64_high127;
  uint64_t as_uint64_high38 = (uint64_t)c9;
  uint64_t as_uint64_high128 = as_uint64_high38 << (uint32_t)32U;
  uint64_t as_uint64_low28 = (uint64_t)(uint32_t)0U;
  uint64_t b17 = as_uint64_low28 ^ as_uint64_high128;
  uint64_t as_uint64_high39 = (uint64_t)c11;
  uint64_t as_uint64_high129 = as_uint64_high39 << (uint32_t)32U;
  uint64_t as_uint64_low29 = (uint64_t)c10;
  uint64_t b27 = as_uint64_low29 ^ as_uint64_high129;
  uint64_t as_uint64_high = (uint64_t)c13;
  uint64_t as_uint64_high130 = as_uint64_high << (uint32_t)32U;
  uint64_t as_uint64_low = (uint64_t)(uint32_t)0U;
  uint64_t b37 = as_uint64_low ^ as_uint64_high130;
  t810[0U] = b07;
  t810[1U] = b17;
  t810[2U] = b27;
  t810[3U] = b37;
  uint32_t len7 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len7);
  uint64_t tempBuffer16[len7];
  memset(tempBuffer16, 0U, len7 * sizeof (uint64_t));
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len1 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t810[(uint32_t)4U * i8];
    uint64_t t220 = p[(uint32_t)4U * i8];
    uint64_t *res_i0 = tempBuffer16 + (uint32_t)4U * i8;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t220, res_i0);
    uint64_t t120 = t810[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer16 + (uint32_t)4U * i8 + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t120, t221, res_i1);
    uint64_t t121 = t810[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer16 + (uint32_t)4U * i8 + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t121, t222, res_i2);
    uint64_t t122 = t810[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer16 + (uint32_t)4U * i8 + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t122, t22, res_i);
  }
  for (uint32_t i8 = len1 / (uint32_t)4U * (uint32_t)4U; i8 < len1; i8++)
  {
    uint64_t t12 = t810[i8];
    uint64_t t22 = p[i8];
    uint64_t *res_i = tempBuffer16 + i8;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t22, res_i);
  }
  uint64_t r13 = c;
  uint64_t r14 = r13;
  cmovznz4_p256(r14, tempBuffer16, t810, t810);
  uint64_t *t010 = tempBuffer;
  uint64_t *t11 = tempBuffer + (uint32_t)4U;
  uint64_t *t21 = tempBuffer + (uint32_t)8U;
  uint64_t *t31 = tempBuffer + (uint32_t)12U;
  uint64_t *t41 = tempBuffer + (uint32_t)16U;
  uint64_t *t51 = tempBuffer + (uint32_t)20U;
  uint64_t *t61 = tempBuffer + (uint32_t)24U;
  uint64_t *t71 = tempBuffer + (uint32_t)28U;
  uint64_t *t81 = tempBuffer + (uint32_t)32U;
  felem_double_p256(t21, t21);
  felem_double_p256(t11, t11);
  felem_add_p256(t010, t11, o);
  felem_add_p256(t21, o, o);
  felem_add_p256(t31, o, o);
  felem_add_p256(t41, o, o);
  felem_sub_p256(o, t51, o);
  felem_sub_p256(o, t61, o);
  felem_sub_p256(o, t71, o);
  felem_sub_p256(o, t81, o);
}

static inline void toDomain_p256(uint64_t *value, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t multBuffer[(uint32_t)2U * len];
  memset(multBuffer, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  uint64_t *oToZero = multBuffer;
  uint64_t *oToCopy = multBuffer + len1;
  memcpy(oToCopy, value, len1 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    oToZero[i] = (uint64_t)0U;
  }
  solinas_reduction_impl_p256(multBuffer, result);
}

static inline void fromDomain_p256(uint64_t *f, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, f, len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len1);
  uint64_t t2[(uint32_t)2U * len1];
  memset(t2, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t *uu____0 = t2 + (uint32_t)4U;
    uint32_t len31 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len31; i++)
    {
      uu____0[i] = (uint64_t)0U;
    }
    uint64_t temp = (uint64_t)0U;
    uint64_t f0 = (uint64_t)0xffffffffffffffffU;
    uint64_t f1 = (uint64_t)0xffffffffU;
    uint64_t f3 = (uint64_t)0xffffffff00000001U;
    uint64_t *o0 = t2;
    uint64_t *o1 = t2 + (uint32_t)1U;
    uint64_t *o2 = t2 + (uint32_t)2U;
    uint64_t *o3 = t2 + (uint32_t)3U;
    uint64_t *o4 = t2 + (uint32_t)4U;
    mul64(f0, t10, o0, &temp);
    uint64_t h0 = temp;
    mul64(f1, t10, o1, &temp);
    uint64_t l = o1[0U];
    uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
    uint64_t h = temp;
    o2[0U] = h + c1;
    mul64(f3, t10, o3, o4);
    uint32_t len32 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      uint64_t *res_i0 = t2 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = t2 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = t2 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = t2 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
    }
    for (uint32_t i = len32 / (uint32_t)4U * (uint32_t)4U; i < len32; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      uint64_t *res_i = t2 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
    }
    uint64_t carry = c;
    uint32_t len3 = (uint32_t)7U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len2 = (uint32_t)4U;
  uint64_t cin = t[len2];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len4 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t210 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t211 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t212 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
  }
  for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t21 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
  }
  uint64_t r = c;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p256(carry, tempBuffer, x_, result);
}

static inline void norm_p256(uint64_t *p, uint64_t *resultPoint, uint64_t *tempBuffer)
{
  uint64_t *xf = p;
  uint64_t *yf = p + (uint32_t)4U;
  uint64_t *zf = p + (uint32_t)8U;
  uint64_t *z2f = tempBuffer + (uint32_t)4U;
  uint64_t *z3f = tempBuffer + (uint32_t)8U;
  uint64_t *t8 = tempBuffer + (uint32_t)12U;
  montgomery_square_buffer_dh_p256(zf, z2f);
  montgomery_multiplication_buffer_dh_p256(z2f, zf, z3f);
  exponent_p256(z2f, z2f, t8);
  exponent_p256(z3f, z3f, t8);
  montgomery_multiplication_buffer_dh_p256(xf, z2f, z2f);
  montgomery_multiplication_buffer_dh_p256(yf, z3f, z3f);
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t zeroBuffer[len];
  memset(zeroBuffer, 0U, len * sizeof (uint64_t));
  uint64_t *resultX = resultPoint;
  uint64_t *resultY = resultPoint + len;
  uint64_t *resultZ = resultPoint + (uint32_t)2U * len;
  uint32_t len10 = (uint32_t)4U;
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = p + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t bit = r;
  fromDomain_p256(z2f, resultX);
  fromDomain_p256(z3f, resultY);
  resultZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    resultZ[i] = (uint64_t)0U;
  }
  copy_conditional_p256(resultZ, zeroBuffer, bit);
}

static inline void fromFormPoint_p256(uint64_t *i, uint8_t *o)
{
  uint32_t len = (uint32_t)4U;
  uint32_t scalarLen = (uint32_t)32U;
  uint64_t *resultBufferX = i;
  uint64_t *resultBufferY = i + len;
  uint8_t *resultX = o;
  uint8_t *resultY = o + scalarLen;
  uint32_t len1 = (uint32_t)4U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i0;
    uint64_t left = resultBufferX[i0];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i0] = right;
    resultBufferX[lenRight] = left;
  }
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    store64_be(resultX + i0 * (uint32_t)8U, resultBufferX[i0]);
  }
  uint32_t len11 = (uint32_t)4U;
  uint32_t lenByTwo0 = len11 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo0; i0++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i0;
    uint64_t left = resultBufferY[i0];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i0] = right;
    resultBufferY[lenRight] = left;
  }
  uint32_t len12 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len12; i0++)
  {
    store64_be(resultY + i0 * (uint32_t)8U, resultBufferY[i0]);
  }
}

static inline void toFormPoint_p256(uint8_t *i, uint64_t *o)
{
  uint32_t len = (uint32_t)4U;
  uint32_t coordLen = (uint32_t)32U;
  uint8_t *pointScalarX = i;
  uint8_t *pointScalarY = i + coordLen;
  uint64_t *pointX = o;
  uint64_t *pointY = o + len;
  uint64_t *pointZ = o + (uint32_t)2U * len;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t *os = pointX;
    uint8_t *bj = pointScalarX + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
  }
  uint32_t len2 = (uint32_t)4U;
  uint32_t lenByTwo = len2 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i0;
    uint64_t left = pointX[i0];
    uint64_t right = pointX[lenRight];
    pointX[i0] = right;
    pointX[lenRight] = left;
  }
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    uint64_t *os = pointY;
    uint8_t *bj = pointScalarY + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
  }
  uint32_t len20 = (uint32_t)4U;
  uint32_t lenByTwo0 = len20 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo0; i0++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i0;
    uint64_t left = pointY[i0];
    uint64_t right = pointY[lenRight];
    pointY[i0] = right;
    pointY[lenRight] = left;
  }
  pointZ[0U] = (uint64_t)1U;
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)1U; i0 < len11; i0++)
  {
    pointZ[i0] = (uint64_t)0U;
  }
}

static inline bool isPointOnCurvePublic_p256(uint64_t *p)
{
  uint32_t sz = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t y2Buffer[sz];
  memset(y2Buffer, 0U, sz * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t xBuffer[sz];
  memset(xBuffer, 0U, sz * sizeof (uint64_t));
  uint64_t *x = p;
  uint64_t *y = p + sz;
  toDomain_p256(y, y2Buffer);
  montgomery_square_buffer_dh_p256(y2Buffer, y2Buffer);
  uint32_t sz1 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t xToDomainBuffer[sz1];
  memset(xToDomainBuffer, 0U, sz1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t minusThreeXBuffer[sz1];
  memset(minusThreeXBuffer, 0U, sz1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t b_constant[sz1];
  memset(b_constant, 0U, sz1 * sizeof (uint64_t));
  toDomain_p256(x, xToDomainBuffer);
  montgomery_square_buffer_dh_p256(xToDomainBuffer, xBuffer);
  montgomery_multiplication_buffer_dh_p256(xBuffer, xToDomainBuffer, xBuffer);
  felem_add_p256(xToDomainBuffer, xToDomainBuffer, minusThreeXBuffer);
  felem_add_p256(xToDomainBuffer, minusThreeXBuffer, minusThreeXBuffer);
  felem_sub_p256(xBuffer, minusThreeXBuffer, xBuffer);
  b_constant[0U] = (uint64_t)15608596021259845087U;
  b_constant[1U] = (uint64_t)12461466548982526096U;
  b_constant[2U] = (uint64_t)16546823903870267094U;
  b_constant[3U] = (uint64_t)15866188208926050356U;
  felem_add_p256(xBuffer, b_constant, xBuffer);
  uint64_t tmp = (uint64_t)0U;
  tmp = (uint64_t)18446744073709551615U;
  uint32_t len = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t a_i = y2Buffer[i];
    uint64_t b_i = xBuffer[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  return !(r == (uint64_t)0U);
}

static bool verifyQValidCurvePoint_p256(uint64_t *pubKey)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer1[len];
  memset(tempBuffer1, 0U, len * sizeof (uint64_t));
  uint64_t *x = pubKey;
  uint64_t *y = pubKey + len;
  uint64_t
  p0[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len10 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len10 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = x[(uint32_t)4U * i];
    uint64_t t20 = p0[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len10 / (uint32_t)4U * (uint32_t)4U; i < len10; i++)
  {
    uint64_t t1 = x[i];
    uint64_t t2 = p0[i];
    uint64_t *res_i = tempBuffer1 + i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
  }
  uint64_t r = c0;
  uint64_t carryX = r;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len1 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = y[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = y[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = y[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = y[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = y[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r0 = c;
  uint64_t carryY = r0;
  bool lessX = carryX == (uint64_t)1U;
  bool lessY = carryY == (uint64_t)1U;
  bool coordinatesValid = lessX && lessY;
  if (!coordinatesValid)
  {
    return false;
  }
  bool belongsToCurve = isPointOnCurvePublic_p256(pubKey);
  return coordinatesValid && belongsToCurve;
}

uint64_t Hacl_P256_ecp256dh_i(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len1;
  uint32_t len20 = (uint32_t)4U;
  uint64_t *x = q;
  uint64_t *y = q + len20;
  uint64_t *z = q + (uint32_t)2U * len20;
  uint32_t len3 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len3; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len30; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len31 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len31; i++)
  {
    z[i] = (uint64_t)0U;
  }
  resultBuffer[0U] = (uint64_t)0x79e730d418a9143cU;
  resultBuffer[1U] = (uint64_t)0x75ba95fc5fedb601U;
  resultBuffer[2U] = (uint64_t)0x79fb732b77622510U;
  resultBuffer[3U] = (uint64_t)0x18905f76a53755c6U;
  resultBuffer[4U] = (uint64_t)0xddf25357ce95560aU;
  resultBuffer[5U] = (uint64_t)0x8b4ab8e4ba19e45cU;
  resultBuffer[6U] = (uint64_t)0xd2e88688dd21f325U;
  resultBuffer[7U] = (uint64_t)0x8571ff1825885d85U;
  resultBuffer[8U] = (uint64_t)0x1U;
  resultBuffer[9U] = (uint64_t)0xffffffff00000000U;
  resultBuffer[10U] = (uint64_t)0xffffffffffffffffU;
  resultBuffer[11U] = (uint64_t)0xfffffffeU;
  montgomery_ladderP256L(q, resultBuffer, scalar, buff);
  norm_p256(q, resultBuffer, buff);
  uint32_t len10 = (uint32_t)4U;
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = resultBuffer + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t r0 = r;
  fromFormPoint_p256(resultBuffer, result);
  bool flag = r0 == (uint64_t)0U;
  return (uint64_t)flag;
}

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p256(pubKey, pkF);
  uint32_t len1 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint_p256(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len2 = (uint32_t)4U;
    uint64_t *q = tempBuffer;
    uint64_t *buff = tempBuffer + (uint32_t)3U * len2;
    uint32_t len30 = (uint32_t)4U;
    uint64_t *x = q;
    uint64_t *y = q + len30;
    uint64_t *z = q + (uint32_t)2U * len30;
    uint32_t len4 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len4; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len40 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len40; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len41 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len41; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len31 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len31;
    uint64_t *p_z = pkF + (uint32_t)2U * len31;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len31;
    uint64_t *r_z = rF + (uint32_t)2U * len31;
    toDomain_p256(p_x, r_x);
    toDomain_p256(p_y, r_y);
    toDomain_p256(p_z, r_z);
    montgomery_ladderP256L(q, rF, scalar, buff);
    norm_p256(q, rF, buff);
    uint32_t len20 = (uint32_t)4U;
    uint32_t start = len20 * (uint32_t)2U;
    uint64_t *zCoordinate = rF + start;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t a_i = zCoordinate[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t r = tmp;
    uint64_t flag0 = r;
    flag = flag0 == (uint64_t)0U;
  }
  else
  {
    flag = false;
  }
  fromFormPoint_p256(rF, result);
  bool flag0 = flag;
  return (uint64_t)flag0;
}

