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

static inline uint64_t
mul_carry_add_u64_st(uint64_t c_in, uint64_t a, uint64_t b, uint64_t *out)
{
  uint128_t uu____0 = (uint128_t)out[0U];
  uint128_t res = (uint128_t)a * b + (uint128_t)c_in + uu____0;
  out[0U] = (uint64_t)res;
  return (uint64_t)(res >> (uint32_t)64U);
}

static inline void felem_add_p256(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, out + i);
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
  uint32_t k = len10 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = out[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer + (uint32_t)4U * i);
    uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t10,
        t21,
        tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t11,
        t22,
        tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t12,
        t2,
        tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len10; i++)
  {
    uint64_t t1 = out[i];
    uint64_t t2 = p[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer + i);
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
  uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, out + i);
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
    uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len30; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
  uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer + (uint32_t)4U * i);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t10,
        t21,
        tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t11,
        t22,
        tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t12,
        t2,
        tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len40; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t2 = p[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer + i);
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
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = t + i0;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      c = mul_carry_add_u64_st(c, a[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
      c =
        mul_carry_add_u64_st(c,
          a[(uint32_t)4U * i + (uint32_t)1U],
          uu____0,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c =
        mul_carry_add_u64_st(c,
          a[(uint32_t)4U * i + (uint32_t)2U],
          uu____0,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c =
        mul_carry_add_u64_st(c,
          a[(uint32_t)4U * i + (uint32_t)3U],
          uu____0,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len1; i++)
    {
      c = mul_carry_add_u64_st(c, a[i], uu____0, res_ + i);
    }
    uint64_t r = c;
    t[len1 + i0] = r;
  }
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
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
    uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len30; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
  uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer + (uint32_t)4U * i);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t10,
        t21,
        tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t11,
        t22,
        tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t12,
        t2,
        tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len40; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t2 = p[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer + i);
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
    uint64_t *uu____0 = a;
    uint64_t uu____1 = a[i0];
    uint64_t *res_ = t + i0;
    uint64_t c = (uint64_t)0U;
    uint32_t k = i0 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      c = mul_carry_add_u64_st(c, uu____0[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
      c =
        mul_carry_add_u64_st(c,
          uu____0[(uint32_t)4U * i + (uint32_t)1U],
          uu____1,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c =
        mul_carry_add_u64_st(c,
          uu____0[(uint32_t)4U * i + (uint32_t)2U],
          uu____1,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c =
        mul_carry_add_u64_st(c,
          uu____0[(uint32_t)4U * i + (uint32_t)3U],
          uu____1,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < i0; i++)
    {
      c = mul_carry_add_u64_st(c, uu____0[i], uu____1, res_ + i);
    }
    uint64_t r = c;
    t[i0 + i0] = r;
  }
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = t[(uint32_t)4U * i];
    uint64_t t20 = t[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, t + (uint32_t)4U * i);
    uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t[(uint32_t)4U * i + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, t + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t[(uint32_t)4U * i + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, t + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < resLen; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = t[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, t + i);
  }
  uint64_t uu____2 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t tmp[resLen];
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t a2 = (uint128_t)a[i] * a[i];
    tmp[(uint32_t)2U * i] = (uint64_t)a2;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
  }
  uint64_t c1 = (uint64_t)0U;
  uint32_t k1 = resLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = t[(uint32_t)4U * i];
    uint64_t t20 = tmp[(uint32_t)4U * i];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, t + (uint32_t)4U * i);
    uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, t + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, t + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k1; i < resLen; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = tmp[i];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t + i);
  }
  uint64_t uu____3 = c1;
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
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
    uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
    uint64_t h = temp;
    o2[0U] = h + c10;
    uint128_t res1 = (uint128_t)f3 * t10;
    uint64_t l0 = (uint64_t)res1;
    uint64_t h04 = (uint64_t)(res1 >> (uint32_t)64U);
    o3[0U] = l0;
    o4[0U] = h04;
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len30; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
  uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer + (uint32_t)4U * i);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t10,
        t21,
        tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t11,
        t22,
        tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t12,
        t2,
        tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len40; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t2 = p[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer + i);
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
      uint64_t *uu____0 = a;
      uint64_t uu____1 = a[i1];
      uint64_t *res_ = t + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = i1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, uu____0[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i + (uint32_t)1U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i + (uint32_t)2U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i + (uint32_t)3U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i1; i++)
      {
        c = mul_carry_add_u64_st(c, uu____0[i], uu____1, res_ + i);
      }
      uint64_t r = c;
      t[i1 + i1] = r;
    }
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t20 = t[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, t + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = t[(uint32_t)4U * i + (uint32_t)1U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, t + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = t[(uint32_t)4U * i + (uint32_t)2U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, t + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = t[(uint32_t)4U * i + (uint32_t)3U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < resLen; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t2 = t[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, t + i);
    }
    uint64_t uu____2 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
    uint64_t tmp[resLen];
    memset(tmp, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint128_t a2 = (uint128_t)a[i] * a[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c1 = (uint64_t)0U;
    uint32_t k1 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t20 = tmp[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, t + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, t + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, t + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < resLen; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t2 = tmp[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t + i);
    }
    uint64_t uu____3 = c1;
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
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t11,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t12,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
    uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer + (uint32_t)4U * i);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t10,
          t21,
          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t11,
          t22,
          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t12,
          t2,
          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len40; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t2 = p[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer + i);
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

