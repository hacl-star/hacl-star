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

static inline void cmovznz4(uint64_t *out, uint64_t *x, uint64_t *y, uint64_t mask)
{
  uint64_t mask1 = FStar_UInt64_eq_mask(mask, (uint64_t)0U);
  uint64_t r0 = (x[0U] & mask1) | (y[0U] & ~mask1);
  uint64_t r1 = (x[1U] & mask1) | (y[1U] & ~mask1);
  uint64_t r2 = (x[2U] & mask1) | (y[2U] & ~mask1);
  uint64_t r3 = (x[3U] & mask1) | (y[3U] & ~mask1);
  out[0U] = r0;
  out[1U] = r1;
  out[2U] = r2;
  out[3U] = r3;
}

static inline void copy_conditional(uint64_t *out, uint64_t *x, uint64_t mask)
{
  uint64_t out_0 = out[0U];
  uint64_t out_1 = out[1U];
  uint64_t out_2 = out[2U];
  uint64_t out_3 = out[3U];
  uint64_t x_0 = x[0U];
  uint64_t x_1 = x[1U];
  uint64_t x_2 = x[2U];
  uint64_t x_3 = x[3U];
  uint64_t r_0 = out_0 ^ (mask & (out_0 ^ x_0));
  uint64_t r_1 = out_1 ^ (mask & (out_1 ^ x_1));
  uint64_t r_2 = out_2 ^ (mask & (out_2 ^ x_2));
  uint64_t r_3 = out_3 ^ (mask & (out_3 ^ x_3));
  out[0U] = r_0;
  out[1U] = r_1;
  out[2U] = r_2;
  out[3U] = r_3;
}

static inline void mul64(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
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
  uint32_t len10 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len10 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
  for (uint32_t i = len10 / (uint32_t)4U * (uint32_t)4U; i < len10; i++)
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
  uint64_t mask = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = out[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    out[i] = r_i;
  }
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
montgomery_multiplication_buffer_by_one_dh_p256(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, a, len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint32_t len2 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t t10 = t[0U];
    uint64_t temp = (uint64_t)0U;
    uint64_t f0 = (uint64_t)0xffffffffffffffffU;
    uint64_t f1 = (uint64_t)0xffffffffU;
    uint64_t f3 = (uint64_t)0xffffffff00000001U;
    uint64_t *o0 = t2;
    uint64_t *o1 = t2 + (uint32_t)1U;
    uint64_t *o2 = t2 + (uint32_t)2U;
    uint64_t *o3 = t2 + (uint32_t)3U;
    uint64_t *o4 = t2 + (uint32_t)4U;
    uint128_t res0 = (uint128_t)f0 * t10;
    uint64_t l00 = (uint64_t)res0;
    uint64_t h040 = (uint64_t)(res0 >> (uint32_t)64U);
    o0[0U] = l00;
    temp = h040;
    uint64_t h0 = temp;
    uint128_t res = (uint128_t)f1 * t10;
    uint64_t l01 = (uint64_t)res;
    uint64_t h041 = (uint64_t)(res >> (uint32_t)64U);
    o1[0U] = l01;
    temp = h041;
    uint64_t l = o1[0U];
    uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
    uint64_t h = temp;
    o2[0U] = h + c1;
    uint128_t res1 = (uint128_t)f3 * t10;
    uint64_t l0 = (uint64_t)res1;
    uint64_t h04 = (uint64_t)(res1 >> (uint32_t)64U);
    o3[0U] = l0;
    o4[0U] = h04;
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len30 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
    for (uint32_t i = len30 / (uint32_t)4U * (uint32_t)4U; i < len30; i++)
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
  uint32_t len40 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len40 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len40 / (uint32_t)4U * (uint32_t)4U; i < len40; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r = c;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  uint64_t mask = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = x_[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    result[i] = r_i;
  }
}

static inline void montgomery_multiplication_buffer_dh_p256(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t round[8U] = { 0U };
  uint64_t t1[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t f00 = a[0U];
  uint64_t f10 = a[1U];
  uint64_t f2 = a[2U];
  uint64_t f30 = a[3U];
  uint64_t *b00 = t;
  uint64_t temp2 = (uint64_t)0U;
  uint64_t f110 = b[1U];
  uint64_t f210 = b[2U];
  uint64_t f310 = b[3U];
  uint64_t *o00 = b00;
  uint64_t *o10 = b00 + (uint32_t)1U;
  uint64_t *o20 = b00 + (uint32_t)2U;
  uint64_t *o30 = b00 + (uint32_t)3U;
  uint64_t f020 = b[0U];
  mul64(f020, f00, o00, &temp2);
  uint64_t h0 = temp2;
  mul64(f110, f00, o10, &temp2);
  uint64_t l0 = o10[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o10);
  uint64_t h1 = temp2;
  mul64(f210, f00, o20, &temp2);
  uint64_t l1 = o20[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l1, h1, o20);
  uint64_t h2 = temp2;
  mul64(f310, f00, o30, &temp2);
  uint64_t l2 = o30[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o30);
  uint64_t temp00 = temp2;
  uint64_t c00 = c3 + temp00;
  t[4U] = c00;
  uint64_t *b10 = t + (uint32_t)1U;
  uint64_t temp3[4U] = { 0U };
  uint64_t temp10 = (uint64_t)0U;
  uint64_t f111 = b[1U];
  uint64_t f211 = b[2U];
  uint64_t f311 = b[3U];
  uint64_t *o01 = temp3;
  uint64_t *o11 = temp3 + (uint32_t)1U;
  uint64_t *o21 = temp3 + (uint32_t)2U;
  uint64_t *o31 = temp3 + (uint32_t)3U;
  uint64_t f021 = b[0U];
  mul64(f021, f10, o01, &temp10);
  uint64_t h3 = temp10;
  mul64(f111, f10, o11, &temp10);
  uint64_t l3 = o11[0U];
  uint64_t c11 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l3, h3, o11);
  uint64_t h4 = temp10;
  mul64(f211, f10, o21, &temp10);
  uint64_t l4 = o21[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l4, h4, o21);
  uint64_t h5 = temp10;
  mul64(f311, f10, o31, &temp10);
  uint64_t l5 = o31[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l5, h5, o31);
  uint64_t temp01 = temp10;
  uint64_t c = c30 + temp01;
  uint64_t *r00 = b10;
  uint64_t *r10 = b10 + (uint32_t)1U;
  uint64_t *r20 = b10 + (uint32_t)2U;
  uint64_t *r30 = b10 + (uint32_t)3U;
  uint64_t cc00 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, temp3[0U], b10[0U], r00);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc00, temp3[1U], b10[1U], r10);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, temp3[2U], b10[2U], r20);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, temp3[3U], b10[3U], r30);
  uint64_t c31 = cc3;
  uint64_t c12 = c + c31;
  t[5U] = c12;
  uint64_t *b2 = t + (uint32_t)2U;
  uint64_t temp4[4U] = { 0U };
  uint64_t temp11 = (uint64_t)0U;
  uint64_t f112 = b[1U];
  uint64_t f212 = b[2U];
  uint64_t f312 = b[3U];
  uint64_t *o02 = temp4;
  uint64_t *o12 = temp4 + (uint32_t)1U;
  uint64_t *o22 = temp4 + (uint32_t)2U;
  uint64_t *o32 = temp4 + (uint32_t)3U;
  uint64_t f022 = b[0U];
  mul64(f022, f2, o02, &temp11);
  uint64_t h6 = temp11;
  mul64(f112, f2, o12, &temp11);
  uint64_t l6 = o12[0U];
  uint64_t c110 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l6, h6, o12);
  uint64_t h7 = temp11;
  mul64(f212, f2, o22, &temp11);
  uint64_t l7 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l7, h7, o22);
  uint64_t h8 = temp11;
  mul64(f312, f2, o32, &temp11);
  uint64_t l8 = o32[0U];
  uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l8, h8, o32);
  uint64_t temp02 = temp11;
  uint64_t c4 = c32 + temp02;
  uint64_t *r01 = b2;
  uint64_t *r11 = b2 + (uint32_t)1U;
  uint64_t *r21 = b2 + (uint32_t)2U;
  uint64_t *r31 = b2 + (uint32_t)3U;
  uint64_t cc01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, temp4[0U], b2[0U], r01);
  uint64_t cc10 = Lib_IntTypes_Intrinsics_add_carry_u64(cc01, temp4[1U], b2[1U], r11);
  uint64_t cc20 = Lib_IntTypes_Intrinsics_add_carry_u64(cc10, temp4[2U], b2[2U], r21);
  uint64_t cc30 = Lib_IntTypes_Intrinsics_add_carry_u64(cc20, temp4[3U], b2[3U], r31);
  uint64_t c33 = cc30;
  uint64_t c22 = c4 + c33;
  t[6U] = c22;
  uint64_t *b3 = t + (uint32_t)3U;
  uint64_t temp5[4U] = { 0U };
  uint64_t temp1 = (uint64_t)0U;
  uint64_t f11 = b[1U];
  uint64_t f21 = b[2U];
  uint64_t f31 = b[3U];
  uint64_t *o03 = temp5;
  uint64_t *o13 = temp5 + (uint32_t)1U;
  uint64_t *o23 = temp5 + (uint32_t)2U;
  uint64_t *o33 = temp5 + (uint32_t)3U;
  uint64_t f02 = b[0U];
  mul64(f02, f30, o03, &temp1);
  uint64_t h9 = temp1;
  mul64(f11, f30, o13, &temp1);
  uint64_t l9 = o13[0U];
  uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h9, o13);
  uint64_t h10 = temp1;
  mul64(f21, f30, o23, &temp1);
  uint64_t l10 = o23[0U];
  uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l10, h10, o23);
  uint64_t h11 = temp1;
  mul64(f31, f30, o33, &temp1);
  uint64_t l11 = o33[0U];
  uint64_t c34 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l11, h11, o33);
  uint64_t temp03 = temp1;
  uint64_t c5 = c34 + temp03;
  uint64_t *r02 = b3;
  uint64_t *r12 = b3 + (uint32_t)1U;
  uint64_t *r22 = b3 + (uint32_t)2U;
  uint64_t *r32 = b3 + (uint32_t)3U;
  uint64_t cc02 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, temp5[0U], b3[0U], r02);
  uint64_t cc11 = Lib_IntTypes_Intrinsics_add_carry_u64(cc02, temp5[1U], b3[1U], r12);
  uint64_t cc21 = Lib_IntTypes_Intrinsics_add_carry_u64(cc11, temp5[2U], b3[2U], r22);
  uint64_t cc31 = Lib_IntTypes_Intrinsics_add_carry_u64(cc21, temp5[3U], b3[3U], r32);
  uint64_t c35 = cc31;
  uint64_t c36 = c5 + c35;
  t[7U] = c36;
  uint64_t t11 = t[0U];
  uint64_t temp6 = (uint64_t)0U;
  uint64_t f01 = (uint64_t)0xffffffffffffffffU;
  uint64_t f12 = (uint64_t)0xffffffffU;
  uint64_t f32 = (uint64_t)0xffffffff00000001U;
  uint64_t *o04 = t2;
  uint64_t *o14 = t2 + (uint32_t)1U;
  uint64_t *o24 = t2 + (uint32_t)2U;
  uint64_t *o34 = t2 + (uint32_t)3U;
  mul64(f01, t11, o04, &temp6);
  uint64_t h12 = temp6;
  mul64(f12, t11, o14, &temp6);
  uint64_t l12 = o14[0U];
  uint64_t c13 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l12, h12, o14);
  uint64_t h13 = temp6;
  temp6 = (uint64_t)0U;
  o24[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c13, (uint64_t)0U, h13, o24);
  uint64_t h40 = temp6;
  mul64(f32, t11, o34, &temp6);
  uint64_t l13 = o34[0U];
  uint64_t c37 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l13, h40, o34);
  uint64_t temp04 = temp6;
  t2[4U] = c37 + temp04;
  uint64_t *a0 = t;
  uint64_t *a10 = t + (uint32_t)4U;
  uint64_t *b01 = t2;
  uint64_t *b11 = t2 + (uint32_t)4U;
  uint64_t *c01 = t1;
  uint64_t *c14 = t1 + (uint32_t)4U;
  uint64_t *r03 = c01;
  uint64_t *r13 = c01 + (uint32_t)1U;
  uint64_t *r23 = c01 + (uint32_t)2U;
  uint64_t *r33 = c01 + (uint32_t)3U;
  uint64_t cc03 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a0[0U], b01[0U], r03);
  uint64_t cc12 = Lib_IntTypes_Intrinsics_add_carry_u64(cc03, a0[1U], b01[1U], r13);
  uint64_t cc22 = Lib_IntTypes_Intrinsics_add_carry_u64(cc12, a0[2U], b01[2U], r23);
  uint64_t cc32 = Lib_IntTypes_Intrinsics_add_carry_u64(cc22, a0[3U], b01[3U], r33);
  uint64_t carry0 = cc32;
  uint64_t *r04 = c14;
  uint64_t *r14 = c14 + (uint32_t)1U;
  uint64_t *r24 = c14 + (uint32_t)2U;
  uint64_t *r34 = c14 + (uint32_t)3U;
  uint64_t cc04 = Lib_IntTypes_Intrinsics_add_carry_u64(carry0, a10[0U], b11[0U], r04);
  uint64_t cc13 = Lib_IntTypes_Intrinsics_add_carry_u64(cc04, a10[1U], b11[1U], r14);
  uint64_t cc23 = Lib_IntTypes_Intrinsics_add_carry_u64(cc13, a10[2U], b11[2U], r24);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc23, a10[3U], b11[3U], r34);
  uint64_t t12 = t1[1U];
  uint64_t t210 = t1[2U];
  uint64_t t30 = t1[3U];
  uint64_t t40 = t1[4U];
  uint64_t t50 = t1[5U];
  uint64_t t60 = t1[6U];
  uint64_t t70 = t1[7U];
  t1[0U] = t12;
  t1[1U] = t210;
  t1[2U] = t30;
  t1[3U] = t40;
  t1[4U] = t50;
  t1[5U] = t60;
  t1[6U] = t70;
  t1[7U] = (uint64_t)0U;
  uint64_t t110 = t1[0U];
  uint64_t temp7 = (uint64_t)0U;
  uint64_t f03 = (uint64_t)0xffffffffffffffffU;
  uint64_t f13 = (uint64_t)0xffffffffU;
  uint64_t f33 = (uint64_t)0xffffffff00000001U;
  uint64_t *o05 = t2;
  uint64_t *o15 = t2 + (uint32_t)1U;
  uint64_t *o25 = t2 + (uint32_t)2U;
  uint64_t *o35 = t2 + (uint32_t)3U;
  mul64(f03, t110, o05, &temp7);
  uint64_t h14 = temp7;
  mul64(f13, t110, o15, &temp7);
  uint64_t l14 = o15[0U];
  uint64_t c15 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l14, h14, o15);
  uint64_t h15 = temp7;
  temp7 = (uint64_t)0U;
  o25[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c15, (uint64_t)0U, h15, o25);
  uint64_t h41 = temp7;
  mul64(f33, t110, o35, &temp7);
  uint64_t l15 = o35[0U];
  uint64_t c38 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l15, h41, o35);
  uint64_t temp05 = temp7;
  t2[4U] = c38 + temp05;
  uint64_t *a00 = t1;
  uint64_t *a11 = t1 + (uint32_t)4U;
  uint64_t *b02 = t2;
  uint64_t *b12 = t2 + (uint32_t)4U;
  uint64_t *c02 = round;
  uint64_t *c16 = round + (uint32_t)4U;
  uint64_t *r05 = c02;
  uint64_t *r15 = c02 + (uint32_t)1U;
  uint64_t *r25 = c02 + (uint32_t)2U;
  uint64_t *r35 = c02 + (uint32_t)3U;
  uint64_t cc05 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a00[0U], b02[0U], r05);
  uint64_t cc14 = Lib_IntTypes_Intrinsics_add_carry_u64(cc05, a00[1U], b02[1U], r15);
  uint64_t cc24 = Lib_IntTypes_Intrinsics_add_carry_u64(cc14, a00[2U], b02[2U], r25);
  uint64_t cc33 = Lib_IntTypes_Intrinsics_add_carry_u64(cc24, a00[3U], b02[3U], r35);
  uint64_t carry00 = cc33;
  uint64_t *r06 = c16;
  uint64_t *r16 = c16 + (uint32_t)1U;
  uint64_t *r26 = c16 + (uint32_t)2U;
  uint64_t *r36 = c16 + (uint32_t)3U;
  uint64_t cc06 = Lib_IntTypes_Intrinsics_add_carry_u64(carry00, a11[0U], b12[0U], r06);
  uint64_t cc15 = Lib_IntTypes_Intrinsics_add_carry_u64(cc06, a11[1U], b12[1U], r16);
  uint64_t cc25 = Lib_IntTypes_Intrinsics_add_carry_u64(cc15, a11[2U], b12[2U], r26);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc25, a11[3U], b12[3U], r36);
  uint64_t t120 = round[1U];
  uint64_t t211 = round[2U];
  uint64_t t31 = round[3U];
  uint64_t t41 = round[4U];
  uint64_t t51 = round[5U];
  uint64_t t61 = round[6U];
  uint64_t t71 = round[7U];
  round[0U] = t120;
  round[1U] = t211;
  round[2U] = t31;
  round[3U] = t41;
  round[4U] = t51;
  round[5U] = t61;
  round[6U] = t71;
  round[7U] = (uint64_t)0U;
  uint64_t t111 = round[0U];
  uint64_t temp8 = (uint64_t)0U;
  uint64_t f04 = (uint64_t)0xffffffffffffffffU;
  uint64_t f14 = (uint64_t)0xffffffffU;
  uint64_t f34 = (uint64_t)0xffffffff00000001U;
  uint64_t *o06 = t2;
  uint64_t *o16 = t2 + (uint32_t)1U;
  uint64_t *o26 = t2 + (uint32_t)2U;
  uint64_t *o36 = t2 + (uint32_t)3U;
  mul64(f04, t111, o06, &temp8);
  uint64_t h16 = temp8;
  mul64(f14, t111, o16, &temp8);
  uint64_t l16 = o16[0U];
  uint64_t c17 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l16, h16, o16);
  uint64_t h17 = temp8;
  temp8 = (uint64_t)0U;
  o26[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c17, (uint64_t)0U, h17, o26);
  uint64_t h42 = temp8;
  mul64(f34, t111, o36, &temp8);
  uint64_t l17 = o36[0U];
  uint64_t c39 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l17, h42, o36);
  uint64_t temp06 = temp8;
  t2[4U] = c39 + temp06;
  uint64_t *a01 = round;
  uint64_t *a12 = round + (uint32_t)4U;
  uint64_t *b03 = t2;
  uint64_t *b13 = t2 + (uint32_t)4U;
  uint64_t *c03 = t1;
  uint64_t *c18 = t1 + (uint32_t)4U;
  uint64_t *r07 = c03;
  uint64_t *r17 = c03 + (uint32_t)1U;
  uint64_t *r27 = c03 + (uint32_t)2U;
  uint64_t *r37 = c03 + (uint32_t)3U;
  uint64_t cc07 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a01[0U], b03[0U], r07);
  uint64_t cc16 = Lib_IntTypes_Intrinsics_add_carry_u64(cc07, a01[1U], b03[1U], r17);
  uint64_t cc26 = Lib_IntTypes_Intrinsics_add_carry_u64(cc16, a01[2U], b03[2U], r27);
  uint64_t cc34 = Lib_IntTypes_Intrinsics_add_carry_u64(cc26, a01[3U], b03[3U], r37);
  uint64_t carry01 = cc34;
  uint64_t *r08 = c18;
  uint64_t *r18 = c18 + (uint32_t)1U;
  uint64_t *r28 = c18 + (uint32_t)2U;
  uint64_t *r38 = c18 + (uint32_t)3U;
  uint64_t cc08 = Lib_IntTypes_Intrinsics_add_carry_u64(carry01, a12[0U], b13[0U], r08);
  uint64_t cc17 = Lib_IntTypes_Intrinsics_add_carry_u64(cc08, a12[1U], b13[1U], r18);
  uint64_t cc27 = Lib_IntTypes_Intrinsics_add_carry_u64(cc17, a12[2U], b13[2U], r28);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc27, a12[3U], b13[3U], r38);
  uint64_t t121 = t1[1U];
  uint64_t t212 = t1[2U];
  uint64_t t32 = t1[3U];
  uint64_t t42 = t1[4U];
  uint64_t t52 = t1[5U];
  uint64_t t62 = t1[6U];
  uint64_t t72 = t1[7U];
  t1[0U] = t121;
  t1[1U] = t212;
  t1[2U] = t32;
  t1[3U] = t42;
  t1[4U] = t52;
  t1[5U] = t62;
  t1[6U] = t72;
  t1[7U] = (uint64_t)0U;
  uint64_t t112 = t1[0U];
  uint64_t temp = (uint64_t)0U;
  uint64_t f0 = (uint64_t)0xffffffffffffffffU;
  uint64_t f1 = (uint64_t)0xffffffffU;
  uint64_t f3 = (uint64_t)0xffffffff00000001U;
  uint64_t *o0 = t2;
  uint64_t *o1 = t2 + (uint32_t)1U;
  uint64_t *o2 = t2 + (uint32_t)2U;
  uint64_t *o3 = t2 + (uint32_t)3U;
  mul64(f0, t112, o0, &temp);
  uint64_t h18 = temp;
  mul64(f1, t112, o1, &temp);
  uint64_t l18 = o1[0U];
  uint64_t c19 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l18, h18, o1);
  uint64_t h = temp;
  temp = (uint64_t)0U;
  o2[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c19, (uint64_t)0U, h, o2);
  uint64_t h43 = temp;
  mul64(f3, t112, o3, &temp);
  uint64_t l = o3[0U];
  uint64_t c310 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h43, o3);
  uint64_t temp0 = temp;
  t2[4U] = c310 + temp0;
  uint64_t *a02 = t1;
  uint64_t *a1 = t1 + (uint32_t)4U;
  uint64_t *b0 = t2;
  uint64_t *b1 = t2 + (uint32_t)4U;
  uint64_t *c0 = round;
  uint64_t *c1 = round + (uint32_t)4U;
  uint64_t *r09 = c0;
  uint64_t *r19 = c0 + (uint32_t)1U;
  uint64_t *r29 = c0 + (uint32_t)2U;
  uint64_t *r39 = c0 + (uint32_t)3U;
  uint64_t cc09 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a02[0U], b0[0U], r09);
  uint64_t cc18 = Lib_IntTypes_Intrinsics_add_carry_u64(cc09, a02[1U], b0[1U], r19);
  uint64_t cc28 = Lib_IntTypes_Intrinsics_add_carry_u64(cc18, a02[2U], b0[2U], r29);
  uint64_t cc35 = Lib_IntTypes_Intrinsics_add_carry_u64(cc28, a02[3U], b0[3U], r39);
  uint64_t carry02 = cc35;
  uint64_t *r010 = c1;
  uint64_t *r110 = c1 + (uint32_t)1U;
  uint64_t *r210 = c1 + (uint32_t)2U;
  uint64_t *r310 = c1 + (uint32_t)3U;
  uint64_t cc0 = Lib_IntTypes_Intrinsics_add_carry_u64(carry02, a1[0U], b1[0U], r010);
  uint64_t cc19 = Lib_IntTypes_Intrinsics_add_carry_u64(cc0, a1[1U], b1[1U], r110);
  uint64_t cc29 = Lib_IntTypes_Intrinsics_add_carry_u64(cc19, a1[2U], b1[2U], r210);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc29, a1[3U], b1[3U], r310);
  uint64_t t122 = round[1U];
  uint64_t t21 = round[2U];
  uint64_t t3 = round[3U];
  uint64_t t4 = round[4U];
  uint64_t t5 = round[5U];
  uint64_t t6 = round[6U];
  uint64_t t7 = round[7U];
  round[0U] = t122;
  round[1U] = t21;
  round[2U] = t3;
  round[3U] = t4;
  round[4U] = t5;
  round[5U] = t6;
  round[6U] = t7;
  round[7U] = (uint64_t)0U;
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = round[4U];
  uint64_t *x_ = round;
  uint64_t *r0 = tempBuffer;
  uint64_t *r1 = tempBuffer + (uint32_t)1U;
  uint64_t *r2 = tempBuffer + (uint32_t)2U;
  uint64_t *r3 = tempBuffer + (uint32_t)3U;
  uint64_t
  cc =
    Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U,
      x_[0U],
      (uint64_t)0xffffffffffffffffU,
      r0);
  uint64_t cc110 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x_[1U], (uint64_t)0xffffffffU, r1);
  uint64_t cc210 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc110, x_[2U], (uint64_t)0U, r2);
  uint64_t
  cc36 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc210, x_[3U], (uint64_t)0xffffffff00000001U, r3);
  uint64_t c6 = cc36;
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c6, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(result, tempBuffer, x_, carry);
}

static inline void montgomery_square_buffer_dh_p256(uint64_t *a, uint64_t *result)
{
  uint64_t t[8U] = { 0U };
  uint64_t t1[8U] = { 0U };
  uint64_t t2[8U] = { 0U };
  uint64_t round[8U] = { 0U };
  uint64_t wb[17U] = { 0U };
  uint64_t *tb = wb;
  uint64_t *memory = wb + (uint32_t)5U;
  uint64_t *b00 = t;
  uint64_t f01 = a[0U];
  uint64_t f310 = a[3U];
  uint64_t *o30 = b00 + (uint32_t)3U;
  uint64_t *temp1 = tb;
  uint64_t f02 = a[0U];
  uint64_t f12 = a[1U];
  uint64_t f22 = a[2U];
  uint64_t *o01 = b00;
  uint64_t *o10 = b00 + (uint32_t)1U;
  uint64_t *o20 = b00 + (uint32_t)2U;
  mul64(f02, f02, o01, temp1);
  uint64_t h_00 = temp1[0U];
  mul64(f02, f12, o10, temp1);
  uint64_t l0 = o10[0U];
  memory[0U] = l0;
  memory[1U] = temp1[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h_00, o10);
  uint64_t h_10 = temp1[0U];
  mul64(f02, f22, o20, temp1);
  uint64_t l10 = o20[0U];
  memory[2U] = l10;
  memory[3U] = temp1[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l10, h_10, o20);
  uint64_t h_20 = temp1[0U];
  mul64(f01, f310, o30, temp1);
  uint64_t l3 = o30[0U];
  memory[4U] = l3;
  memory[5U] = temp1[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l3, h_20, o30);
  uint64_t temp00 = temp1[0U];
  uint64_t c00 = c3 + temp00;
  t[4U] = c00;
  uint64_t *b10 = t + (uint32_t)1U;
  uint64_t *temp2 = tb;
  uint64_t *tempBufferResult0 = tb + (uint32_t)1U;
  uint64_t f11 = a[1U];
  uint64_t f210 = a[2U];
  uint64_t f311 = a[3U];
  uint64_t *o00 = tempBufferResult0;
  uint64_t *o11 = tempBufferResult0 + (uint32_t)1U;
  uint64_t *o21 = tempBufferResult0 + (uint32_t)2U;
  uint64_t *o31 = tempBufferResult0 + (uint32_t)3U;
  o00[0U] = memory[0U];
  uint64_t h_01 = memory[1U];
  mul64(f11, f11, o11, temp2);
  uint64_t l4 = o11[0U];
  uint64_t c11 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l4, h_01, o11);
  uint64_t h_11 = temp2[0U];
  mul64(f11, f210, o21, temp2);
  uint64_t l11 = o21[0U];
  memory[6U] = l11;
  memory[7U] = temp2[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, l11, h_11, o21);
  uint64_t h_21 = temp2[0U];
  mul64(f11, f311, o31, temp2);
  uint64_t l20 = o31[0U];
  memory[8U] = l20;
  memory[9U] = temp2[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l20, h_21, o31);
  uint64_t h_30 = temp2[0U];
  uint64_t *r00 = b10;
  uint64_t *r10 = b10 + (uint32_t)1U;
  uint64_t *r20 = b10 + (uint32_t)2U;
  uint64_t *r30 = b10 + (uint32_t)3U;
  uint64_t
  cc00 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, tempBufferResult0[0U], b10[0U], r00);
  uint64_t
  cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc00, tempBufferResult0[1U], b10[1U], r10);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, tempBufferResult0[2U], b10[2U], r20);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, tempBufferResult0[3U], b10[3U], r30);
  uint64_t c4 = cc3;
  uint64_t c12 = c30 + h_30 + c4;
  t[5U] = c12;
  uint64_t *b2 = t + (uint32_t)2U;
  uint64_t *temp3 = tb;
  uint64_t *tempBufferResult1 = tb + (uint32_t)1U;
  uint64_t f21 = a[2U];
  uint64_t f312 = a[3U];
  uint64_t *o02 = tempBufferResult1;
  uint64_t *o12 = tempBufferResult1 + (uint32_t)1U;
  uint64_t *o22 = tempBufferResult1 + (uint32_t)2U;
  uint64_t *o32 = tempBufferResult1 + (uint32_t)3U;
  o02[0U] = memory[2U];
  uint64_t h_0 = memory[3U];
  o12[0U] = memory[6U];
  uint64_t l5 = o12[0U];
  uint64_t c110 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l5, h_0, o12);
  uint64_t h_1 = memory[7U];
  mul64(f21, f21, o22, temp3);
  uint64_t l12 = o22[0U];
  uint64_t c21 = Lib_IntTypes_Intrinsics_add_carry_u64(c110, l12, h_1, o22);
  uint64_t h_2 = temp3[0U];
  mul64(f21, f312, o32, temp3);
  uint64_t l21 = o32[0U];
  memory[10U] = l21;
  memory[11U] = temp3[0U];
  uint64_t c31 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l21, h_2, o32);
  uint64_t h_31 = temp3[0U];
  uint64_t *r01 = b2;
  uint64_t *r11 = b2 + (uint32_t)1U;
  uint64_t *r21 = b2 + (uint32_t)2U;
  uint64_t *r31 = b2 + (uint32_t)3U;
  uint64_t
  cc01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, tempBufferResult1[0U], b2[0U], r01);
  uint64_t
  cc10 = Lib_IntTypes_Intrinsics_add_carry_u64(cc01, tempBufferResult1[1U], b2[1U], r11);
  uint64_t
  cc20 = Lib_IntTypes_Intrinsics_add_carry_u64(cc10, tempBufferResult1[2U], b2[2U], r21);
  uint64_t
  cc30 = Lib_IntTypes_Intrinsics_add_carry_u64(cc20, tempBufferResult1[3U], b2[3U], r31);
  uint64_t c40 = cc30;
  uint64_t c22 = c31 + h_31 + c40;
  t[6U] = c22;
  uint64_t *b3 = t + (uint32_t)3U;
  uint64_t *temp4 = tb;
  uint64_t *tempBufferResult = tb + (uint32_t)1U;
  uint64_t f31 = a[3U];
  uint64_t *o03 = tempBufferResult;
  uint64_t *o13 = tempBufferResult + (uint32_t)1U;
  uint64_t *o23 = tempBufferResult + (uint32_t)2U;
  uint64_t *o33 = tempBufferResult + (uint32_t)3U;
  o03[0U] = memory[4U];
  uint64_t h0 = memory[5U];
  o13[0U] = memory[8U];
  uint64_t l6 = o13[0U];
  uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l6, h0, o13);
  uint64_t h4 = memory[9U];
  o23[0U] = memory[10U];
  uint64_t l1 = o23[0U];
  uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l1, h4, o23);
  uint64_t h5 = memory[11U];
  mul64(f31, f31, o33, temp4);
  uint64_t l2 = o33[0U];
  uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l2, h5, o33);
  uint64_t h_3 = temp4[0U];
  uint64_t *r02 = b3;
  uint64_t *r12 = b3 + (uint32_t)1U;
  uint64_t *r22 = b3 + (uint32_t)2U;
  uint64_t *r32 = b3 + (uint32_t)3U;
  uint64_t
  cc02 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, tempBufferResult[0U], b3[0U], r02);
  uint64_t cc11 = Lib_IntTypes_Intrinsics_add_carry_u64(cc02, tempBufferResult[1U], b3[1U], r12);
  uint64_t cc21 = Lib_IntTypes_Intrinsics_add_carry_u64(cc11, tempBufferResult[2U], b3[2U], r22);
  uint64_t cc31 = Lib_IntTypes_Intrinsics_add_carry_u64(cc21, tempBufferResult[3U], b3[3U], r32);
  uint64_t c41 = cc31;
  uint64_t c33 = c32 + h_3 + c41;
  t[7U] = c33;
  uint64_t t11 = t[0U];
  uint64_t temp5 = (uint64_t)0U;
  uint64_t f00 = (uint64_t)0xffffffffffffffffU;
  uint64_t f10 = (uint64_t)0xffffffffU;
  uint64_t f30 = (uint64_t)0xffffffff00000001U;
  uint64_t *o04 = t2;
  uint64_t *o14 = t2 + (uint32_t)1U;
  uint64_t *o24 = t2 + (uint32_t)2U;
  uint64_t *o34 = t2 + (uint32_t)3U;
  mul64(f00, t11, o04, &temp5);
  uint64_t h1 = temp5;
  mul64(f10, t11, o14, &temp5);
  uint64_t l7 = o14[0U];
  uint64_t c13 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l7, h1, o14);
  uint64_t h2 = temp5;
  temp5 = (uint64_t)0U;
  o24[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c13, (uint64_t)0U, h2, o24);
  uint64_t h40 = temp5;
  mul64(f30, t11, o34, &temp5);
  uint64_t l8 = o34[0U];
  uint64_t c34 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l8, h40, o34);
  uint64_t temp01 = temp5;
  t2[4U] = c34 + temp01;
  uint64_t *a0 = t;
  uint64_t *a10 = t + (uint32_t)4U;
  uint64_t *b01 = t2;
  uint64_t *b11 = t2 + (uint32_t)4U;
  uint64_t *c01 = t1;
  uint64_t *c14 = t1 + (uint32_t)4U;
  uint64_t *r03 = c01;
  uint64_t *r13 = c01 + (uint32_t)1U;
  uint64_t *r23 = c01 + (uint32_t)2U;
  uint64_t *r33 = c01 + (uint32_t)3U;
  uint64_t cc03 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a0[0U], b01[0U], r03);
  uint64_t cc12 = Lib_IntTypes_Intrinsics_add_carry_u64(cc03, a0[1U], b01[1U], r13);
  uint64_t cc22 = Lib_IntTypes_Intrinsics_add_carry_u64(cc12, a0[2U], b01[2U], r23);
  uint64_t cc32 = Lib_IntTypes_Intrinsics_add_carry_u64(cc22, a0[3U], b01[3U], r33);
  uint64_t carry0 = cc32;
  uint64_t *r04 = c14;
  uint64_t *r14 = c14 + (uint32_t)1U;
  uint64_t *r24 = c14 + (uint32_t)2U;
  uint64_t *r34 = c14 + (uint32_t)3U;
  uint64_t cc04 = Lib_IntTypes_Intrinsics_add_carry_u64(carry0, a10[0U], b11[0U], r04);
  uint64_t cc13 = Lib_IntTypes_Intrinsics_add_carry_u64(cc04, a10[1U], b11[1U], r14);
  uint64_t cc23 = Lib_IntTypes_Intrinsics_add_carry_u64(cc13, a10[2U], b11[2U], r24);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc23, a10[3U], b11[3U], r34);
  uint64_t t12 = t1[1U];
  uint64_t t210 = t1[2U];
  uint64_t t30 = t1[3U];
  uint64_t t40 = t1[4U];
  uint64_t t50 = t1[5U];
  uint64_t t60 = t1[6U];
  uint64_t t70 = t1[7U];
  t1[0U] = t12;
  t1[1U] = t210;
  t1[2U] = t30;
  t1[3U] = t40;
  t1[4U] = t50;
  t1[5U] = t60;
  t1[6U] = t70;
  t1[7U] = (uint64_t)0U;
  uint64_t t110 = t1[0U];
  uint64_t temp6 = (uint64_t)0U;
  uint64_t f03 = (uint64_t)0xffffffffffffffffU;
  uint64_t f13 = (uint64_t)0xffffffffU;
  uint64_t f32 = (uint64_t)0xffffffff00000001U;
  uint64_t *o05 = t2;
  uint64_t *o15 = t2 + (uint32_t)1U;
  uint64_t *o25 = t2 + (uint32_t)2U;
  uint64_t *o35 = t2 + (uint32_t)3U;
  mul64(f03, t110, o05, &temp6);
  uint64_t h3 = temp6;
  mul64(f13, t110, o15, &temp6);
  uint64_t l9 = o15[0U];
  uint64_t c15 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h3, o15);
  uint64_t h6 = temp6;
  temp6 = (uint64_t)0U;
  o25[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c15, (uint64_t)0U, h6, o25);
  uint64_t h41 = temp6;
  mul64(f32, t110, o35, &temp6);
  uint64_t l13 = o35[0U];
  uint64_t c35 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l13, h41, o35);
  uint64_t temp02 = temp6;
  t2[4U] = c35 + temp02;
  uint64_t *a00 = t1;
  uint64_t *a11 = t1 + (uint32_t)4U;
  uint64_t *b02 = t2;
  uint64_t *b12 = t2 + (uint32_t)4U;
  uint64_t *c02 = round;
  uint64_t *c16 = round + (uint32_t)4U;
  uint64_t *r05 = c02;
  uint64_t *r15 = c02 + (uint32_t)1U;
  uint64_t *r25 = c02 + (uint32_t)2U;
  uint64_t *r35 = c02 + (uint32_t)3U;
  uint64_t cc05 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a00[0U], b02[0U], r05);
  uint64_t cc14 = Lib_IntTypes_Intrinsics_add_carry_u64(cc05, a00[1U], b02[1U], r15);
  uint64_t cc24 = Lib_IntTypes_Intrinsics_add_carry_u64(cc14, a00[2U], b02[2U], r25);
  uint64_t cc33 = Lib_IntTypes_Intrinsics_add_carry_u64(cc24, a00[3U], b02[3U], r35);
  uint64_t carry00 = cc33;
  uint64_t *r06 = c16;
  uint64_t *r16 = c16 + (uint32_t)1U;
  uint64_t *r26 = c16 + (uint32_t)2U;
  uint64_t *r36 = c16 + (uint32_t)3U;
  uint64_t cc06 = Lib_IntTypes_Intrinsics_add_carry_u64(carry00, a11[0U], b12[0U], r06);
  uint64_t cc15 = Lib_IntTypes_Intrinsics_add_carry_u64(cc06, a11[1U], b12[1U], r16);
  uint64_t cc25 = Lib_IntTypes_Intrinsics_add_carry_u64(cc15, a11[2U], b12[2U], r26);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc25, a11[3U], b12[3U], r36);
  uint64_t t120 = round[1U];
  uint64_t t211 = round[2U];
  uint64_t t31 = round[3U];
  uint64_t t41 = round[4U];
  uint64_t t51 = round[5U];
  uint64_t t61 = round[6U];
  uint64_t t71 = round[7U];
  round[0U] = t120;
  round[1U] = t211;
  round[2U] = t31;
  round[3U] = t41;
  round[4U] = t51;
  round[5U] = t61;
  round[6U] = t71;
  round[7U] = (uint64_t)0U;
  uint64_t t111 = round[0U];
  uint64_t temp7 = (uint64_t)0U;
  uint64_t f04 = (uint64_t)0xffffffffffffffffU;
  uint64_t f14 = (uint64_t)0xffffffffU;
  uint64_t f33 = (uint64_t)0xffffffff00000001U;
  uint64_t *o06 = t2;
  uint64_t *o16 = t2 + (uint32_t)1U;
  uint64_t *o26 = t2 + (uint32_t)2U;
  uint64_t *o36 = t2 + (uint32_t)3U;
  mul64(f04, t111, o06, &temp7);
  uint64_t h7 = temp7;
  mul64(f14, t111, o16, &temp7);
  uint64_t l14 = o16[0U];
  uint64_t c17 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l14, h7, o16);
  uint64_t h8 = temp7;
  temp7 = (uint64_t)0U;
  o26[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c17, (uint64_t)0U, h8, o26);
  uint64_t h42 = temp7;
  mul64(f33, t111, o36, &temp7);
  uint64_t l15 = o36[0U];
  uint64_t c36 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l15, h42, o36);
  uint64_t temp03 = temp7;
  t2[4U] = c36 + temp03;
  uint64_t *a01 = round;
  uint64_t *a12 = round + (uint32_t)4U;
  uint64_t *b03 = t2;
  uint64_t *b13 = t2 + (uint32_t)4U;
  uint64_t *c03 = t1;
  uint64_t *c18 = t1 + (uint32_t)4U;
  uint64_t *r07 = c03;
  uint64_t *r17 = c03 + (uint32_t)1U;
  uint64_t *r27 = c03 + (uint32_t)2U;
  uint64_t *r37 = c03 + (uint32_t)3U;
  uint64_t cc07 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a01[0U], b03[0U], r07);
  uint64_t cc16 = Lib_IntTypes_Intrinsics_add_carry_u64(cc07, a01[1U], b03[1U], r17);
  uint64_t cc26 = Lib_IntTypes_Intrinsics_add_carry_u64(cc16, a01[2U], b03[2U], r27);
  uint64_t cc34 = Lib_IntTypes_Intrinsics_add_carry_u64(cc26, a01[3U], b03[3U], r37);
  uint64_t carry01 = cc34;
  uint64_t *r08 = c18;
  uint64_t *r18 = c18 + (uint32_t)1U;
  uint64_t *r28 = c18 + (uint32_t)2U;
  uint64_t *r38 = c18 + (uint32_t)3U;
  uint64_t cc08 = Lib_IntTypes_Intrinsics_add_carry_u64(carry01, a12[0U], b13[0U], r08);
  uint64_t cc17 = Lib_IntTypes_Intrinsics_add_carry_u64(cc08, a12[1U], b13[1U], r18);
  uint64_t cc27 = Lib_IntTypes_Intrinsics_add_carry_u64(cc17, a12[2U], b13[2U], r28);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc27, a12[3U], b13[3U], r38);
  uint64_t t121 = t1[1U];
  uint64_t t212 = t1[2U];
  uint64_t t32 = t1[3U];
  uint64_t t42 = t1[4U];
  uint64_t t52 = t1[5U];
  uint64_t t62 = t1[6U];
  uint64_t t72 = t1[7U];
  t1[0U] = t121;
  t1[1U] = t212;
  t1[2U] = t32;
  t1[3U] = t42;
  t1[4U] = t52;
  t1[5U] = t62;
  t1[6U] = t72;
  t1[7U] = (uint64_t)0U;
  uint64_t t112 = t1[0U];
  uint64_t temp = (uint64_t)0U;
  uint64_t f0 = (uint64_t)0xffffffffffffffffU;
  uint64_t f1 = (uint64_t)0xffffffffU;
  uint64_t f3 = (uint64_t)0xffffffff00000001U;
  uint64_t *o0 = t2;
  uint64_t *o1 = t2 + (uint32_t)1U;
  uint64_t *o2 = t2 + (uint32_t)2U;
  uint64_t *o3 = t2 + (uint32_t)3U;
  mul64(f0, t112, o0, &temp);
  uint64_t h9 = temp;
  mul64(f1, t112, o1, &temp);
  uint64_t l16 = o1[0U];
  uint64_t c19 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l16, h9, o1);
  uint64_t h = temp;
  temp = (uint64_t)0U;
  o2[0U] = (uint64_t)0U;
  Lib_IntTypes_Intrinsics_add_carry_u64_void(c19, (uint64_t)0U, h, o2);
  uint64_t h43 = temp;
  mul64(f3, t112, o3, &temp);
  uint64_t l = o3[0U];
  uint64_t c37 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h43, o3);
  uint64_t temp0 = temp;
  t2[4U] = c37 + temp0;
  uint64_t *a02 = t1;
  uint64_t *a1 = t1 + (uint32_t)4U;
  uint64_t *b0 = t2;
  uint64_t *b1 = t2 + (uint32_t)4U;
  uint64_t *c0 = round;
  uint64_t *c1 = round + (uint32_t)4U;
  uint64_t *r09 = c0;
  uint64_t *r19 = c0 + (uint32_t)1U;
  uint64_t *r29 = c0 + (uint32_t)2U;
  uint64_t *r39 = c0 + (uint32_t)3U;
  uint64_t cc09 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, a02[0U], b0[0U], r09);
  uint64_t cc18 = Lib_IntTypes_Intrinsics_add_carry_u64(cc09, a02[1U], b0[1U], r19);
  uint64_t cc28 = Lib_IntTypes_Intrinsics_add_carry_u64(cc18, a02[2U], b0[2U], r29);
  uint64_t cc35 = Lib_IntTypes_Intrinsics_add_carry_u64(cc28, a02[3U], b0[3U], r39);
  uint64_t carry02 = cc35;
  uint64_t *r010 = c1;
  uint64_t *r110 = c1 + (uint32_t)1U;
  uint64_t *r210 = c1 + (uint32_t)2U;
  uint64_t *r310 = c1 + (uint32_t)3U;
  uint64_t cc0 = Lib_IntTypes_Intrinsics_add_carry_u64(carry02, a1[0U], b1[0U], r010);
  uint64_t cc19 = Lib_IntTypes_Intrinsics_add_carry_u64(cc0, a1[1U], b1[1U], r110);
  uint64_t cc29 = Lib_IntTypes_Intrinsics_add_carry_u64(cc19, a1[2U], b1[2U], r210);
  Lib_IntTypes_Intrinsics_add_carry_u64_void(cc29, a1[3U], b1[3U], r310);
  uint64_t t122 = round[1U];
  uint64_t t21 = round[2U];
  uint64_t t3 = round[3U];
  uint64_t t4 = round[4U];
  uint64_t t5 = round[5U];
  uint64_t t6 = round[6U];
  uint64_t t7 = round[7U];
  round[0U] = t122;
  round[1U] = t21;
  round[2U] = t3;
  round[3U] = t4;
  round[4U] = t5;
  round[5U] = t6;
  round[6U] = t7;
  round[7U] = (uint64_t)0U;
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t cin = round[4U];
  uint64_t *x_ = round;
  uint64_t *r0 = tempBuffer;
  uint64_t *r1 = tempBuffer + (uint32_t)1U;
  uint64_t *r2 = tempBuffer + (uint32_t)2U;
  uint64_t *r3 = tempBuffer + (uint32_t)3U;
  uint64_t
  cc =
    Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U,
      x_[0U],
      (uint64_t)0xffffffffffffffffU,
      r0);
  uint64_t cc110 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x_[1U], (uint64_t)0xffffffffU, r1);
  uint64_t cc210 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc110, x_[2U], (uint64_t)0U, r2);
  uint64_t
  cc36 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc210, x_[3U], (uint64_t)0xffffffff00000001U, r3);
  uint64_t c = cc36;
  uint64_t
  carry = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, cin, (uint64_t)0U, &tempBufferForSubborrow);
  cmovznz4(result, tempBuffer, x_, carry);
}


static inline void fsquarePowN_dh_p256(uint32_t n, uint64_t *a)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
  {
    uint32_t len = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
    uint64_t t[(uint32_t)2U * len];
    memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
    uint32_t len1 = (uint32_t)4U;
    uint32_t resLen = len1 + len1;
    memset(t, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len1; i1++)
    {
      uint64_t *ab = a;
      uint64_t a_j = a[i1];
      uint64_t *res_j = t + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < i1 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
      for (uint32_t i = i1 / (uint32_t)4U * (uint32_t)4U; i < i1; i++)
      {
        uint64_t a_i = ab[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, a_j, c, res_i);
      }
      uint64_t r = c;
      t[i1 + i1] = r;
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
    for (uint32_t i1 = (uint32_t)0U; i1 < len10; i1++)
    {
      uint32_t len2 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
      uint64_t t2[(uint32_t)2U * len2];
      memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
      uint64_t t10 = t[0U];
      uint64_t temp = (uint64_t)0U;
      uint64_t f0 = (uint64_t)0xffffffffffffffffU;
      uint64_t f1 = (uint64_t)0xffffffffU;
      uint64_t f3 = (uint64_t)0xffffffff00000001U;
      uint64_t *o0 = t2;
      uint64_t *o1 = t2 + (uint32_t)1U;
      uint64_t *o2 = t2 + (uint32_t)2U;
      uint64_t *o3 = t2 + (uint32_t)3U;
      uint64_t *o4 = t2 + (uint32_t)4U;
      uint128_t res0 = (uint128_t)f0 * t10;
      uint64_t l00 = (uint64_t)res0;
      uint64_t h050 = (uint64_t)(res0 >> (uint32_t)64U);
      o0[0U] = l00;
      temp = h050;
      uint64_t h0 = temp;
      uint128_t res = (uint128_t)f1 * t10;
      uint64_t l01 = (uint64_t)res;
      uint64_t h051 = (uint64_t)(res >> (uint32_t)64U);
      o1[0U] = l01;
      temp = h051;
      uint64_t l = o1[0U];
      uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
      uint64_t h = temp;
      o2[0U] = h + c10;
      uint128_t res1 = (uint128_t)f3 * t10;
      uint64_t l0 = (uint64_t)res1;
      uint64_t h05 = (uint64_t)(res1 >> (uint32_t)64U);
      o3[0U] = l0;
      o4[0U] = h05;
      uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len30 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
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
      for (uint32_t i = len30 / (uint32_t)4U * (uint32_t)4U; i < len30; i++)
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
    uint32_t len40 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len40 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
    }
    for (uint32_t i = len40 / (uint32_t)4U * (uint32_t)4U; i < len40; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
    uint64_t r = c;
    uint64_t carry0 = r;
    uint64_t
    carry =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    uint64_t mask = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
    uint32_t len4 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len4; i++)
    {
      uint64_t x_i = tempBuffer[i];
      uint64_t y_i = x_[i];
      uint64_t r_i = (y_i & mask) | (x_i & ~mask);
      a[i] = r_i;
    }
  }
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
  fsquarePowN_dh_p256((uint32_t)3U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t6, t7);
  montgomery_square_buffer_dh_p256(t7, t0);
  montgomery_square_buffer_dh_p256(t0, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t2, t1);
  montgomery_square_buffer_dh_p256(t1, t0);
  fsquarePowN_dh_p256((uint32_t)9U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t1, t3);
  montgomery_square_buffer_dh_p256(t3, t0);
  fsquarePowN_dh_p256((uint32_t)9U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t1, t4);
  montgomery_square_buffer_dh_p256(t4, t0);
  montgomery_square_buffer_dh_p256(t0, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t2, t5);
  montgomery_square_buffer_dh_p256(t5, t0);
  fsquarePowN_dh_p256((uint32_t)31U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t, t0);
  fsquarePowN_dh_p256((uint32_t)128U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t5, t0);
  fsquarePowN_dh_p256((uint32_t)32U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t5, t0);
  fsquarePowN_dh_p256((uint32_t)30U, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t4, t0);
  fsquarePowN_dh_p256((uint32_t)2U, t0);
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
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t x_i = p_x0[i];
    uint64_t out_i = x3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    x3_out[i] = r_i;
  }
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t x_i = p_y0[i];
    uint64_t out_i = y3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    y3_out[i] = r_i;
  }
  uint32_t len3 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len3; i++)
  {
    uint64_t x_i = p_z0[i];
    uint64_t out_i = z3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    z3_out[i] = r_i;
  }
  uint64_t *z0 = q + (uint32_t)8U;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
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
  uint32_t len = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t x_i = p_x[i];
    uint64_t out_i = x3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    x3_out[i] = r_i;
  }
  uint32_t len5 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len5; i++)
  {
    uint64_t x_i = p_y[i];
    uint64_t out_i = y3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    y3_out[i] = r_i;
  }
  uint32_t len6 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len6; i++)
  {
    uint64_t x_i = p_z[i];
    uint64_t out_i = z3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    z3_out[i] = r_i;
  }
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

static void norm_p256(uint64_t *p, uint64_t *resultPoint, uint64_t *tempBuffer)
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
  montgomery_multiplication_buffer_by_one_dh_p256(z2f, resultX);
  montgomery_multiplication_buffer_by_one_dh_p256(z3f, resultY);
  resultZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    resultZ[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    uint64_t x_i = zeroBuffer[i];
    uint64_t out_i = resultZ[i];
    uint64_t r_i = out_i ^ (bit & (out_i ^ x_i));
    resultZ[i] = r_i;
  }
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
  uint32_t len10 = (uint32_t)4U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len10;
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
  uint32_t len11 = (uint32_t)4U;
  uint32_t start = len11 * (uint32_t)2U;
  uint64_t *zCoordinate = resultBuffer + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len21 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t r0 = r;
  uint32_t len1 = (uint32_t)4U;
  uint32_t scalarLen = (uint32_t)32U;
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + len1;
  uint8_t *resultX = result;
  uint8_t *resultY = result + scalarLen;
  uint32_t len2 = (uint32_t)4U;
  uint32_t lenByTwo = len2 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = resultBufferX[i];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i] = right;
    resultBufferX[lenRight] = left;
  }
  uint32_t len22 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len22; i++)
  {
    store64_be(resultX + i * (uint32_t)8U, resultBufferX[i]);
  }
  uint32_t len23 = (uint32_t)4U;
  uint32_t lenByTwo0 = len23 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = resultBufferY[i];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i] = right;
    resultBufferY[lenRight] = left;
  }
  uint32_t len24 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len24; i++)
  {
    store64_be(resultY + i * (uint32_t)8U, resultBufferY[i]);
  }
  bool flag = r0 == (uint64_t)0U;
  return (uint64_t)flag;
}

