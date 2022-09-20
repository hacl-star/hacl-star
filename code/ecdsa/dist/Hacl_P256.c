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

#include "internal/Hacl_Spec.h"
#include "internal/Hacl_Krmllib.h"

static inline void mul64(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static inline void copy_conditional_p256_l(uint64_t *out, uint64_t *x, uint64_t mask)
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

static inline void copy_conditional_p384_l(uint64_t *out, uint64_t *x, uint64_t mask)
{
  uint32_t len = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t x_i = x[i];
    uint64_t out_i = out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    out[i] = r_i;
  }
}

static inline void copy_conditional_p256_c(uint64_t *out, const uint64_t *x, uint64_t mask)
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

static inline void copy_conditional_p384_c(uint64_t *out, const uint64_t *x, uint64_t mask)
{
  uint32_t len = (uint32_t)6U;
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
    r[i] = (y_i & mask) | (x_i & ~mask);
  }
}

static inline void cmovznz4_p384(uint64_t cin, uint64_t *x, uint64_t *y, uint64_t *r)
{
  uint64_t mask = ~FStar_UInt64_eq_mask(cin, (uint64_t)0U);
  uint32_t len = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t x_i = x[i];
    uint64_t y_i = y[i];
    r[i] = (y_i & mask) | (x_i & ~mask);
  }
}

static inline bool cmp_felem_felem_bool_p256(uint64_t *a, uint64_t *b)
{
  uint64_t tmp1 = (uint64_t)0U;
  tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len0 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len0; i++)
  {
    uint64_t a_i = a[i];
    uint64_t b_i = b[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t r = ~tmp1;
  uint64_t tmp = (uint64_t)0U;
  tmp = (uint64_t)18446744073709551615U;
  uint32_t len = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t a_i = a[i];
    uint64_t b_i = b[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t uu____0 = tmp;
  return r == (uint64_t)0U;
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
  for (uint32_t i = (uint32_t)0U; i < aLen / (uint32_t)4U; i++)
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

static const
uint8_t
sqPower_buffer_p256[32U] =
  {
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)64U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)64U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)192U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)63U
  };

static const
uint8_t
sqPower_buffer_p384[48U] =
  {
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)64U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)192U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)191U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)63U
  };

static inline void felem_add_p256(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U; i++)
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
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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

static inline void felem_add_p384(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)6U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U; i++)
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
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len1 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, out, out);
}

static inline void felem_double_p256(uint64_t *arg1, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U; i++)
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
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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

static inline void felem_double_p384(uint64_t *arg1, uint64_t *out)
{
  uint32_t len0 = (uint32_t)6U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U; i++)
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
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len1 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, out, out);
}

static inline void felem_sub_p256(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U; i++)
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

static inline void felem_sub_p384(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U; i++)
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
  uint64_t b1[6U] = { 0U };
  uint64_t t3 = (uint64_t)0U - t;
  uint64_t t2 = t3 - t;
  uint64_t t1 = t3 << (uint32_t)32U;
  uint64_t t0 = ((uint64_t)0U - t) >> (uint32_t)32U;
  b1[0U] = t0;
  b1[1U] = t1;
  b1[2U] = t2;
  b1[3U] = t3;
  b1[4U] = t3;
  b1[5U] = t3;
  uint64_t c0 = (uint64_t)0U;
  {
    uint64_t t11 = out[(uint32_t)4U * (uint32_t)0U];
    uint64_t t210 = b1[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = out + (uint32_t)4U * (uint32_t)0U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t210, res_i0);
    uint64_t t110 = out[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t t211 = b1[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t110, t211, res_i1);
    uint64_t t111 = out[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t t212 = b1[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t111, t212, res_i2);
    uint64_t t112 = out[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t t21 = b1[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t112, t21, res_i);
  }
  {
    uint64_t t11 = out[4U];
    uint64_t t21 = b1[4U];
    uint64_t *res_i = out + (uint32_t)4U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t21, res_i);
  }
  {
    uint64_t t11 = out[5U];
    uint64_t t21 = b1[5U];
    uint64_t *res_i = out + (uint32_t)5U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t21, res_i);
  }
  uint64_t r = c0;
  uint64_t r0 = r;
}

static void felem_sub_zero(Spec_ECC_Curves_curve c, uint64_t *arg2, uint64_t *out)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    out[i] = (uint64_t)0U;
  }
  uint32_t len0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len0 = (uint32_t)6U;
        break;
      }
    default:
      {
        len0 = (uint32_t)4U;
      }
  }
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = out[(uint32_t)4U * i];
    uint64_t t20 = arg2[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg2[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg2[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg2[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  for (uint32_t i = len0 / (uint32_t)4U * (uint32_t)4U; i < len0; i++)
  {
    uint64_t t1 = out[i];
    uint64_t t2 = arg2[i];
    uint64_t *res_i = out + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t t = c1;
  uint64_t r;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
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
        r = cc3;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t b[6U] = { 0U };
        uint64_t t3 = (uint64_t)0U - t;
        uint64_t t2 = t3 - t;
        uint64_t t1 = t3 << (uint32_t)32U;
        uint64_t t0 = ((uint64_t)0U - t) >> (uint32_t)32U;
        b[0U] = t0;
        b[1U] = t1;
        b[2U] = t2;
        b[3U] = t3;
        b[4U] = t3;
        b[5U] = t3;
        uint64_t c10 = (uint64_t)0U;
        {
          uint64_t t11 = out[(uint32_t)4U * (uint32_t)0U];
          uint64_t t210 = b[(uint32_t)4U * (uint32_t)0U];
          uint64_t *res_i0 = out + (uint32_t)4U * (uint32_t)0U;
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t11, t210, res_i0);
          uint64_t t110 = out[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
          uint64_t t211 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
          uint64_t *res_i1 = out + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t110, t211, res_i1);
          uint64_t t111 = out[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t t212 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t *res_i2 = out + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t111, t212, res_i2);
          uint64_t t112 = out[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t *res_i = out + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t112, t21, res_i);
        }
        {
          uint64_t t11 = out[4U];
          uint64_t t21 = b[4U];
          uint64_t *res_i = out + (uint32_t)4U;
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t11, t21, res_i);
        }
        {
          uint64_t t11 = out[5U];
          uint64_t t21 = b[5U];
          uint64_t *res_i = out + (uint32_t)5U;
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t11, t21, res_i);
        }
        uint64_t r0 = c10;
        r = r0;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void mul_atomic(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static inline void reduction_prime_2prime_order_p256(uint64_t *x, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t
  p[4U] =
    {
      (uint64_t)17562291160714782033U,
      (uint64_t)13611842547513532036U,
      (uint64_t)18446744073709551615U,
      (uint64_t)18446744069414584320U
    };
  uint32_t len1 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = x[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = x[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r = c;
  uint64_t r0 = r;
  cmovznz4_p256(r0, tempBuffer, x, result);
}

static inline void reduction_prime_2prime_order_p384(uint64_t *x, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t
  p[6U] =
    {
      (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
      (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
      (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
    };
  uint32_t len1 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = x[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = x[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r = c;
  uint64_t r0 = r;
  cmovznz4_p384(r0, tempBuffer, x, result);
}

static inline void felem_add_ecdsa_P256(uint64_t *arg1, uint64_t *arg2, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg2[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg2[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg2[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg2[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len0 / (uint32_t)4U * (uint32_t)4U; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg2[i];
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
      (uint64_t)17562291160714782033U,
      (uint64_t)13611842547513532036U,
      (uint64_t)18446744073709551615U,
      (uint64_t)18446744069414584320U
    };
  uint32_t len1 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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

static inline uint64_t mod_inv_uint64(uint64_t n0)
{
  uint64_t alpha = (uint64_t)9223372036854775808U;
  uint64_t beta = n0;
  uint64_t ub = (uint64_t)0U;
  uint64_t vb = (uint64_t)0U;
  ub = (uint64_t)1U;
  vb = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t us = ub;
    uint64_t vs = vb;
    uint64_t u_is_odd = (uint64_t)0U - (us & (uint64_t)1U);
    uint64_t beta_if_u_is_odd = beta & u_is_odd;
    ub = ((us ^ beta_if_u_is_odd) >> (uint32_t)1U) + (us & beta_if_u_is_odd);
    uint64_t alpha_if_u_is_odd = alpha & u_is_odd;
    vb = (vs >> (uint32_t)1U) + alpha_if_u_is_odd;
  }
  return vb;
}

static inline void
montgomery_multiplication_buffer_dh_p256(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  memset(t, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
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
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
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
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
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
  uint32_t len20 = (uint32_t)4U;
  uint64_t cin = t[len20];
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
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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

static inline void
montgomery_multiplication_buffer_dh_p384(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  memset(t, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  uint32_t len10 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)6U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len31 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
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
    uint32_t len3 = (uint32_t)11U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len20 = (uint32_t)6U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len4 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, x_, result);
}

static inline void
montgomery_multiplication_buffer_dsa_p256(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  memset(t, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = mod_inv_uint64((uint64_t)17562291160714782033U);
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len31 = (uint32_t)4U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
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
  uint32_t len20 = (uint32_t)4U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)17562291160714782033U,
      (uint64_t)13611842547513532036U,
      (uint64_t)18446744073709551615U,
      (uint64_t)18446744069414584320U
    };
  uint32_t len4 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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

static inline void
montgomery_multiplication_buffer_dsa_p384(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  memset(t, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  uint32_t len10 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = mod_inv_uint64((uint64_t)17072048233947408755U);
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)6U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p[6U] =
      {
        (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
        (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
        (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
      };
    uint32_t len31 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
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
    uint32_t len3 = (uint32_t)11U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len20 = (uint32_t)6U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
      (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
      (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
    };
  uint32_t len4 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, x_, result);
}

static inline void montgomery_square_buffer_dh_p256(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  memset(t, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
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
  uint64_t c0 = bn_add_eq_len_u64(len1 + len1, t, t, t);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t res = (uint128_t)a[i] * a[i];
    uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
    uint64_t lo = (uint64_t)res;
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = bn_add_eq_len_u64(len1 + len1, t, tmp, t);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
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
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
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
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
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
  uint32_t len20 = (uint32_t)4U;
  uint64_t cin = t[len20];
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
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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

static inline void montgomery_square_buffer_dh_p384(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  memset(t, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = t + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
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
  uint64_t c0 = bn_add_eq_len_u64(len1 + len1, t, t, t);
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
  uint64_t tmp[len1 + len1];
  memset(tmp, 0U, (len1 + len1) * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t res = (uint128_t)a[i] * a[i];
    uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
    uint64_t lo = (uint64_t)res;
    tmp[(uint32_t)2U * i] = lo;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = bn_add_eq_len_u64(len1 + len1, t, tmp, t);
  uint32_t len10 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)6U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len31 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
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
    uint32_t len3 = (uint32_t)11U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len20 = (uint32_t)6U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len4 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, x_, result);
}

static inline void
montgomery_ladder_power_p256_dh(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  p[0U] = (uint64_t)1U;
  p[1U] = (uint64_t)18446744069414584320U;
  p[2U] = (uint64_t)18446744073709551615U;
  p[3U] = (uint64_t)4294967294U;
  uint32_t scalarLen = (uint32_t)4U * (uint32_t)8U * (uint32_t)8U;
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = (uint32_t)4U * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - i0;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len10 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len10; i++)
    {
      uint64_t dummy = mask & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
    uint32_t len11 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len11);
    uint64_t t[(uint32_t)2U * len11];
    memset(t, 0U, (uint32_t)2U * len11 * sizeof (uint64_t));
    uint32_t len20 = (uint32_t)4U;
    memset(t, 0U, (len20 + len20) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len20; i1++)
    {
      uint64_t bj = a[i1];
      uint64_t *res_j = t + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len20 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len20 / (uint32_t)4U * (uint32_t)4U; i < len20; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      t[len20 + i1] = r;
    }
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len21);
    uint64_t t2[(uint32_t)2U * len21];
    memset(t2, 0U, (uint32_t)2U * len21 * sizeof (uint64_t));
    uint32_t len30 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len30; i1++)
    {
      uint64_t t10 = t[0U];
      uint32_t len40 = (uint32_t)4U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        t2[i] = (uint64_t)0U;
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
      uint32_t len41 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len41 / (uint32_t)4U; i++)
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
      for (uint32_t i = len41 / (uint32_t)4U * (uint32_t)4U; i < len41; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        uint64_t *res_i = t2 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t[i] = elem;
      }
      t[len4] = carry;
    }
    uint32_t len31 = (uint32_t)4U;
    uint64_t cin = t[len31];
    uint64_t *x_0 = t;
    uint32_t len40 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len40);
    uint64_t tempBuffer[len40];
    memset(tempBuffer, 0U, len40 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow0 = (uint64_t)0U;
    uint64_t
    p10[4U] =
      {
        (uint64_t)0xffffffffffffffffU,
        (uint64_t)0xffffffffU,
        (uint64_t)0U,
        (uint64_t)0xffffffff00000001U
      };
    uint32_t len50 = (uint32_t)4U;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len50 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_0[(uint32_t)4U * i];
      uint64_t t210 = p10[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t210, res_i0);
      uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p10[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t211, res_i1);
      uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p10[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t212, res_i2);
      uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t21, res_i);
    }
    for (uint32_t i = len50 / (uint32_t)4U * (uint32_t)4U; i < len50; i++)
    {
      uint64_t t1 = x_0[i];
      uint64_t t21 = p10[i];
      uint64_t *res_i = tempBuffer + i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t21, res_i);
    }
    uint64_t r = c1;
    uint64_t carry0 = r;
    uint64_t
    carry =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow0);
    cmovznz4_p256(carry, tempBuffer, x_0, a);
    uint32_t len12 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len12);
    uint64_t t0[(uint32_t)2U * len12];
    memset(t0, 0U, (uint32_t)2U * len12 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)4U;
    memset(t0, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *ab = p;
      uint64_t a_j = p[i1];
      uint64_t *res_j = t0 + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < i1 / (uint32_t)4U; i++)
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
      uint64_t r0 = c;
      t0[i1 + i1] = r0;
    }
    uint64_t c0 = bn_add_eq_len_u64(len2 + len2, t0, t0, t0);
    KRML_CHECK_SIZE(sizeof (uint64_t), len2 + len2);
    uint64_t tmp[len2 + len2];
    memset(tmp, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t res = (uint128_t)p[i] * p[i];
      uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
      uint64_t lo = (uint64_t)res;
      tmp[(uint32_t)2U * i] = lo;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
    }
    uint64_t c10 = bn_add_eq_len_u64(len2 + len2, t0, tmp, t0);
    uint32_t len22 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len22);
    uint64_t t20[(uint32_t)2U * len22];
    memset(t20, 0U, (uint32_t)2U * len22 * sizeof (uint64_t));
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len3; i1++)
    {
      uint64_t t10 = t0[0U];
      uint32_t len41 = (uint32_t)4U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len41; i++)
      {
        t20[i] = (uint64_t)0U;
      }
      uint64_t temp = (uint64_t)0U;
      uint64_t f0 = (uint64_t)0xffffffffffffffffU;
      uint64_t f1 = (uint64_t)0xffffffffU;
      uint64_t f3 = (uint64_t)0xffffffff00000001U;
      uint64_t *o0 = t20;
      uint64_t *o1 = t20 + (uint32_t)1U;
      uint64_t *o2 = t20 + (uint32_t)2U;
      uint64_t *o3 = t20 + (uint32_t)3U;
      uint64_t *o4 = t20 + (uint32_t)4U;
      mul64(f0, t10, o0, &temp);
      uint64_t h0 = temp;
      mul64(f1, t10, o1, &temp);
      uint64_t l = o1[0U];
      uint64_t c11 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
      uint64_t h = temp;
      o2[0U] = h + c11;
      mul64(f3, t10, o3, o4);
      uint32_t len42 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t20[(uint32_t)4U * i];
        uint64_t *res_i0 = t20 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t20[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = t20 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t20[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = t20 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t20[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = t20 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
      }
      for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t20[i];
        uint64_t *res_i = t20 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry1 = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t20[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry1;
    }
    uint32_t len32 = (uint32_t)4U;
    uint64_t cin0 = t0[len32];
    uint64_t *x_ = t0;
    uint32_t len4 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len4);
    uint64_t tempBuffer0[len4];
    memset(tempBuffer0, 0U, len4 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow = (uint64_t)0U;
    uint64_t
    p1[4U] =
      {
        (uint64_t)0xffffffffffffffffU,
        (uint64_t)0xffffffffU,
        (uint64_t)0U,
        (uint64_t)0xffffffff00000001U
      };
    uint32_t len5 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len5 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t210 = p1[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer0 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
    }
    for (uint32_t i = len5 / (uint32_t)4U * (uint32_t)4U; i < len5; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t21 = p1[i];
      uint64_t *res_i = tempBuffer0 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
    }
    uint64_t r0 = c;
    uint64_t carry00 = r0;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    cmovznz4_p256(carry1, tempBuffer0, x_, p);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask0 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)4U * sizeof (uint64_t));
}

static inline void
montgomery_ladder_power_p384_dh(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  p[0U] = (uint64_t)18446744069414584321U;
  p[1U] = (uint64_t)4294967295U;
  p[2U] = (uint64_t)1U;
  p[3U] = (uint64_t)0U;
  p[4U] = (uint64_t)0U;
  p[5U] = (uint64_t)0U;
  uint32_t scalarLen = (uint32_t)6U * (uint32_t)8U * (uint32_t)8U;
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = (uint32_t)6U * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - i0;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len10 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len10; i++)
    {
      uint64_t dummy = mask & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
    uint32_t len11 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len11);
    uint64_t t[(uint32_t)2U * len11];
    memset(t, 0U, (uint32_t)2U * len11 * sizeof (uint64_t));
    uint32_t len20 = (uint32_t)6U;
    memset(t, 0U, (len20 + len20) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len20; i1++)
    {
      uint64_t bj = a[i1];
      uint64_t *res_j = t + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len20 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len20 / (uint32_t)4U * (uint32_t)4U; i < len20; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      t[len20 + i1] = r;
    }
    uint32_t len21 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len21);
    uint64_t t2[(uint32_t)2U * len21];
    memset(t2, 0U, (uint32_t)2U * len21 * sizeof (uint64_t));
    uint32_t len30 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len30; i1++)
    {
      uint64_t k0 = (uint64_t)4294967297U;
      uint64_t t10 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t10, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t len40 = (uint32_t)6U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        t2[i] = (uint64_t)0U;
      }
      uint64_t
      p1[6U] =
        {
          (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
          (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffffffffffU
        };
      uint32_t len41 = (uint32_t)6U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      memset(partResult, 0U, (len41 + (uint32_t)1U) * sizeof (uint64_t));
      {
        uint64_t bj = (&bBuffer)[0U];
        uint64_t *res_j = partResult;
        uint64_t c = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len41 / (uint32_t)4U; i++)
        {
          uint64_t a_i = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i0);
          uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
          c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
          uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
          c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
          uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
          c = mul_wide_add2_u64(a_i2, bj, c, res_i);
        }
        for (uint32_t i = len41 / (uint32_t)4U * (uint32_t)4U; i < len41; i++)
        {
          uint64_t a_i = p1[i];
          uint64_t *res_i = res_j + i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i);
        }
        uint64_t r = c;
        partResult[len41 + (uint32_t)0U] = r;
      }
      uint32_t len42 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
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
      for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        uint64_t *res_i = t2 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry = c;
      uint32_t len4 = (uint32_t)11U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t[i] = elem;
      }
      t[len4] = carry;
    }
    uint32_t len31 = (uint32_t)6U;
    uint64_t cin = t[len31];
    uint64_t *x_0 = t;
    uint32_t len40 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len40);
    uint64_t tempBuffer[len40];
    memset(tempBuffer, 0U, len40 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow0 = (uint64_t)0U;
    uint64_t
    p10[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len50 = (uint32_t)6U;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len50 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_0[(uint32_t)4U * i];
      uint64_t t210 = p10[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t210, res_i0);
      uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p10[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t211, res_i1);
      uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p10[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t212, res_i2);
      uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t21, res_i);
    }
    for (uint32_t i = len50 / (uint32_t)4U * (uint32_t)4U; i < len50; i++)
    {
      uint64_t t1 = x_0[i];
      uint64_t t21 = p10[i];
      uint64_t *res_i = tempBuffer + i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t21, res_i);
    }
    uint64_t r = c1;
    uint64_t carry0 = r;
    uint64_t
    carry =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow0);
    cmovznz4_p384(carry, tempBuffer, x_0, a);
    uint32_t len12 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len12);
    uint64_t t0[(uint32_t)2U * len12];
    memset(t0, 0U, (uint32_t)2U * len12 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)6U;
    memset(t0, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *ab = p;
      uint64_t a_j = p[i1];
      uint64_t *res_j = t0 + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < i1 / (uint32_t)4U; i++)
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
      uint64_t r0 = c;
      t0[i1 + i1] = r0;
    }
    uint64_t c0 = bn_add_eq_len_u64(len2 + len2, t0, t0, t0);
    KRML_CHECK_SIZE(sizeof (uint64_t), len2 + len2);
    uint64_t tmp[len2 + len2];
    memset(tmp, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t res = (uint128_t)p[i] * p[i];
      uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
      uint64_t lo = (uint64_t)res;
      tmp[(uint32_t)2U * i] = lo;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
    }
    uint64_t c10 = bn_add_eq_len_u64(len2 + len2, t0, tmp, t0);
    uint32_t len22 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len22);
    uint64_t t20[(uint32_t)2U * len22];
    memset(t20, 0U, (uint32_t)2U * len22 * sizeof (uint64_t));
    uint32_t len3 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len3; i1++)
    {
      uint64_t k0 = (uint64_t)4294967297U;
      uint64_t t10 = t0[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t10, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t len41 = (uint32_t)6U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len41; i++)
      {
        t20[i] = (uint64_t)0U;
      }
      uint64_t
      p1[6U] =
        {
          (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
          (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffffffffffU
        };
      uint32_t len42 = (uint32_t)6U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t20;
      memset(partResult, 0U, (len42 + (uint32_t)1U) * sizeof (uint64_t));
      {
        uint64_t bj = (&bBuffer)[0U];
        uint64_t *res_j = partResult;
        uint64_t c = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
        {
          uint64_t a_i = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i0);
          uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
          c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
          uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
          c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
          uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
          c = mul_wide_add2_u64(a_i2, bj, c, res_i);
        }
        for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
        {
          uint64_t a_i = p1[i];
          uint64_t *res_i = res_j + i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i);
        }
        uint64_t r0 = c;
        partResult[len42 + (uint32_t)0U] = r0;
      }
      uint32_t len43 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len43 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t20[(uint32_t)4U * i];
        uint64_t *res_i0 = t20 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t20[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = t20 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t20[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = t20 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t20[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = t20 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
      }
      for (uint32_t i = len43 / (uint32_t)4U * (uint32_t)4U; i < len43; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t20[i];
        uint64_t *res_i = t20 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry1 = c;
      uint32_t len4 = (uint32_t)11U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t20[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry1;
    }
    uint32_t len32 = (uint32_t)6U;
    uint64_t cin0 = t0[len32];
    uint64_t *x_ = t0;
    uint32_t len4 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len4);
    uint64_t tempBuffer0[len4];
    memset(tempBuffer0, 0U, len4 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow = (uint64_t)0U;
    uint64_t
    p1[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len5 = (uint32_t)6U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len5 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t210 = p1[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer0 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
    }
    for (uint32_t i = len5 / (uint32_t)4U * (uint32_t)4U; i < len5; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t21 = p1[i];
      uint64_t *res_i = tempBuffer0 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
    }
    uint64_t r0 = c;
    uint64_t carry00 = r0;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    cmovznz4_p384(carry1, tempBuffer0, x_, p);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask0 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)6U * sizeof (uint64_t));
}

static inline void
montgomery_ladder_power_p256_dsa(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  p[0U] = (uint64_t)884452912994769583U;
  p[1U] = (uint64_t)4834901526196019579U;
  p[2U] = (uint64_t)0U;
  p[3U] = (uint64_t)4294967295U;
  uint32_t scalarLen = (uint32_t)4U * (uint32_t)8U * (uint32_t)8U;
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = (uint32_t)4U * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - i0;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len10 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len10; i++)
    {
      uint64_t dummy = mask & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
    uint32_t len11 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len11);
    uint64_t t[(uint32_t)2U * len11];
    memset(t, 0U, (uint32_t)2U * len11 * sizeof (uint64_t));
    uint32_t len20 = (uint32_t)4U;
    memset(t, 0U, (len20 + len20) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len20; i1++)
    {
      uint64_t bj = a[i1];
      uint64_t *res_j = t + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len20 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len20 / (uint32_t)4U * (uint32_t)4U; i < len20; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      t[len20 + i1] = r;
    }
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len21);
    uint64_t t2[(uint32_t)2U * len21];
    memset(t2, 0U, (uint32_t)2U * len21 * sizeof (uint64_t));
    uint32_t len30 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len30; i1++)
    {
      uint64_t k0 = mod_inv_uint64((uint64_t)17562291160714782033U);
      uint64_t t10 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t10, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t len40 = (uint32_t)4U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        t2[i] = (uint64_t)0U;
      }
      uint64_t
      p1[4U] =
        {
          (uint64_t)17562291160714782033U,
          (uint64_t)13611842547513532036U,
          (uint64_t)18446744073709551615U,
          (uint64_t)18446744069414584320U
        };
      uint32_t len41 = (uint32_t)4U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      memset(partResult, 0U, (len41 + (uint32_t)1U) * sizeof (uint64_t));
      {
        uint64_t bj = (&bBuffer)[0U];
        uint64_t *res_j = partResult;
        uint64_t c = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len41 / (uint32_t)4U; i++)
        {
          uint64_t a_i = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i0);
          uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
          c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
          uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
          c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
          uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
          c = mul_wide_add2_u64(a_i2, bj, c, res_i);
        }
        for (uint32_t i = len41 / (uint32_t)4U * (uint32_t)4U; i < len41; i++)
        {
          uint64_t a_i = p1[i];
          uint64_t *res_i = res_j + i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i);
        }
        uint64_t r = c;
        partResult[len41 + (uint32_t)0U] = r;
      }
      uint32_t len42 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
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
      for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        uint64_t *res_i = t2 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t[i] = elem;
      }
      t[len4] = carry;
    }
    uint32_t len31 = (uint32_t)4U;
    uint64_t cin = t[len31];
    uint64_t *x_0 = t;
    uint32_t len40 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len40);
    uint64_t tempBuffer[len40];
    memset(tempBuffer, 0U, len40 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow0 = (uint64_t)0U;
    uint64_t
    p10[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len50 = (uint32_t)4U;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len50 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_0[(uint32_t)4U * i];
      uint64_t t210 = p10[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t210, res_i0);
      uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p10[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t211, res_i1);
      uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p10[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t212, res_i2);
      uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t21, res_i);
    }
    for (uint32_t i = len50 / (uint32_t)4U * (uint32_t)4U; i < len50; i++)
    {
      uint64_t t1 = x_0[i];
      uint64_t t21 = p10[i];
      uint64_t *res_i = tempBuffer + i;
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t21, res_i);
    }
    uint64_t r = c1;
    uint64_t carry0 = r;
    uint64_t
    carry =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow0);
    cmovznz4_p256(carry, tempBuffer, x_0, a);
    uint32_t len12 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len12);
    uint64_t t0[(uint32_t)2U * len12];
    memset(t0, 0U, (uint32_t)2U * len12 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)4U;
    memset(t0, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *ab = p;
      uint64_t a_j = p[i1];
      uint64_t *res_j = t0 + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < i1 / (uint32_t)4U; i++)
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
      uint64_t r0 = c;
      t0[i1 + i1] = r0;
    }
    uint64_t c0 = bn_add_eq_len_u64(len2 + len2, t0, t0, t0);
    KRML_CHECK_SIZE(sizeof (uint64_t), len2 + len2);
    uint64_t tmp[len2 + len2];
    memset(tmp, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t res = (uint128_t)p[i] * p[i];
      uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
      uint64_t lo = (uint64_t)res;
      tmp[(uint32_t)2U * i] = lo;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
    }
    uint64_t c10 = bn_add_eq_len_u64(len2 + len2, t0, tmp, t0);
    uint32_t len22 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len22);
    uint64_t t20[(uint32_t)2U * len22];
    memset(t20, 0U, (uint32_t)2U * len22 * sizeof (uint64_t));
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len3; i1++)
    {
      uint64_t k0 = mod_inv_uint64((uint64_t)17562291160714782033U);
      uint64_t t10 = t0[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t10, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t len41 = (uint32_t)4U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len41; i++)
      {
        t20[i] = (uint64_t)0U;
      }
      uint64_t
      p1[4U] =
        {
          (uint64_t)17562291160714782033U,
          (uint64_t)13611842547513532036U,
          (uint64_t)18446744073709551615U,
          (uint64_t)18446744069414584320U
        };
      uint32_t len42 = (uint32_t)4U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t20;
      memset(partResult, 0U, (len42 + (uint32_t)1U) * sizeof (uint64_t));
      {
        uint64_t bj = (&bBuffer)[0U];
        uint64_t *res_j = partResult;
        uint64_t c = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
        {
          uint64_t a_i = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i0);
          uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
          c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
          uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
          c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
          uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
          c = mul_wide_add2_u64(a_i2, bj, c, res_i);
        }
        for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
        {
          uint64_t a_i = p1[i];
          uint64_t *res_i = res_j + i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i);
        }
        uint64_t r0 = c;
        partResult[len42 + (uint32_t)0U] = r0;
      }
      uint32_t len43 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len43 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t20[(uint32_t)4U * i];
        uint64_t *res_i0 = t20 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t20[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = t20 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t20[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = t20 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t20[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = t20 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
      }
      for (uint32_t i = len43 / (uint32_t)4U * (uint32_t)4U; i < len43; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t20[i];
        uint64_t *res_i = t20 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry1 = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t20[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry1;
    }
    uint32_t len32 = (uint32_t)4U;
    uint64_t cin0 = t0[len32];
    uint64_t *x_ = t0;
    uint32_t len4 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len4);
    uint64_t tempBuffer0[len4];
    memset(tempBuffer0, 0U, len4 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow = (uint64_t)0U;
    uint64_t
    p1[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len5 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len5 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t210 = p1[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer0 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
    }
    for (uint32_t i = len5 / (uint32_t)4U * (uint32_t)4U; i < len5; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t21 = p1[i];
      uint64_t *res_i = tempBuffer0 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
    }
    uint64_t r0 = c;
    uint64_t carry00 = r0;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    cmovznz4_p256(carry1, tempBuffer0, x_, p);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask0 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)4U * sizeof (uint64_t));
}

static inline void
montgomery_ladder_power_p384_dsa(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  uint32_t len10 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    p[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t tempBuffer[len11];
  memset(tempBuffer, 0U, len11 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow0 = (uint64_t)0U;
  uint64_t
  p10[6U] =
    {
      (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
      (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
      (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
    };
  uint32_t len20 = (uint32_t)6U;
  uint64_t c1 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len20 / (uint32_t)4U; i++)
  {
    uint64_t t1 = p[(uint32_t)4U * i];
    uint64_t t20 = p10[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p10[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p10[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  for (uint32_t i = len20 / (uint32_t)4U * (uint32_t)4U; i < len20; i++)
  {
    uint64_t t1 = p[i];
    uint64_t t2 = p10[i];
    uint64_t *res_i = tempBuffer + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t r = c1;
  uint64_t carry0 = r;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      (uint64_t)1U,
      (uint64_t)0U,
      &tempBufferForSubborrow0);
  cmovznz4_p384(carry, tempBuffer, p, p);
  uint32_t scalarLen = (uint32_t)6U * (uint32_t)8U * (uint32_t)8U;
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = (uint32_t)6U * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - i0;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len12 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len12; i++)
    {
      uint64_t dummy = mask & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
    uint32_t len13 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len13);
    uint64_t t[(uint32_t)2U * len13];
    memset(t, 0U, (uint32_t)2U * len13 * sizeof (uint64_t));
    uint32_t len21 = (uint32_t)6U;
    memset(t, 0U, (len21 + len21) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len21; i1++)
    {
      uint64_t bj = a[i1];
      uint64_t *res_j = t + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len21 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len21 / (uint32_t)4U * (uint32_t)4U; i < len21; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r0 = c;
      t[len21 + i1] = r0;
    }
    uint32_t len22 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len22);
    uint64_t t2[(uint32_t)2U * len22];
    memset(t2, 0U, (uint32_t)2U * len22 * sizeof (uint64_t));
    uint32_t len30 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len30; i1++)
    {
      uint64_t k0 = mod_inv_uint64((uint64_t)17072048233947408755U);
      uint64_t t10 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t10, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t len40 = (uint32_t)6U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        t2[i] = (uint64_t)0U;
      }
      uint64_t
      p1[6U] =
        {
          (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
          (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
          (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
        };
      uint32_t len41 = (uint32_t)6U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      memset(partResult, 0U, (len41 + (uint32_t)1U) * sizeof (uint64_t));
      {
        uint64_t bj = (&bBuffer)[0U];
        uint64_t *res_j = partResult;
        uint64_t c = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len41 / (uint32_t)4U; i++)
        {
          uint64_t a_i = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i0);
          uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
          c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
          uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
          c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
          uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
          c = mul_wide_add2_u64(a_i2, bj, c, res_i);
        }
        for (uint32_t i = len41 / (uint32_t)4U * (uint32_t)4U; i < len41; i++)
        {
          uint64_t a_i = p1[i];
          uint64_t *res_i = res_j + i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i);
        }
        uint64_t r0 = c;
        partResult[len41 + (uint32_t)0U] = r0;
      }
      uint32_t len42 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
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
      for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        uint64_t *res_i = t2 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry1 = c;
      uint32_t len4 = (uint32_t)11U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t[i] = elem;
      }
      t[len4] = carry1;
    }
    uint32_t len31 = (uint32_t)6U;
    uint64_t cin = t[len31];
    uint64_t *x_0 = t;
    uint32_t len40 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len40);
    uint64_t tempBuffer0[len40];
    memset(tempBuffer0, 0U, len40 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow1 = (uint64_t)0U;
    uint64_t
    p11[6U] =
      {
        (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
        (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
        (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
      };
    uint32_t len50 = (uint32_t)6U;
    uint64_t c2 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len50 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_0[(uint32_t)4U * i];
      uint64_t t210 = p11[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer0 + (uint32_t)4U * i;
      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t1, t210, res_i0);
      uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)1U;
      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t10, t211, res_i1);
      uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer0 + (uint32_t)4U * i + (uint32_t)2U;
      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t11, t212, res_i2);
      uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer0 + (uint32_t)4U * i + (uint32_t)3U;
      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t12, t21, res_i);
    }
    for (uint32_t i = len50 / (uint32_t)4U * (uint32_t)4U; i < len50; i++)
    {
      uint64_t t1 = x_0[i];
      uint64_t t21 = p11[i];
      uint64_t *res_i = tempBuffer0 + i;
      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t1, t21, res_i);
    }
    uint64_t r0 = c2;
    uint64_t carry00 = r0;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow1);
    cmovznz4_p384(carry1, tempBuffer0, x_0, a);
    uint32_t len14 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len14);
    uint64_t t0[(uint32_t)2U * len14];
    memset(t0, 0U, (uint32_t)2U * len14 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)6U;
    memset(t0, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *ab = p;
      uint64_t a_j = p[i1];
      uint64_t *res_j = t0 + i1;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < i1 / (uint32_t)4U; i++)
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
      uint64_t r1 = c;
      t0[i1 + i1] = r1;
    }
    uint64_t c0 = bn_add_eq_len_u64(len2 + len2, t0, t0, t0);
    KRML_CHECK_SIZE(sizeof (uint64_t), len2 + len2);
    uint64_t tmp[len2 + len2];
    memset(tmp, 0U, (len2 + len2) * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t res = (uint128_t)p[i] * p[i];
      uint64_t hi = (uint64_t)(res >> (uint32_t)64U);
      uint64_t lo = (uint64_t)res;
      tmp[(uint32_t)2U * i] = lo;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
    }
    uint64_t c10 = bn_add_eq_len_u64(len2 + len2, t0, tmp, t0);
    uint32_t len23 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len23);
    uint64_t t20[(uint32_t)2U * len23];
    memset(t20, 0U, (uint32_t)2U * len23 * sizeof (uint64_t));
    uint32_t len3 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len3; i1++)
    {
      uint64_t k0 = mod_inv_uint64((uint64_t)17072048233947408755U);
      uint64_t t10 = t0[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t10, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t len41 = (uint32_t)6U * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len41; i++)
      {
        t20[i] = (uint64_t)0U;
      }
      uint64_t
      p1[6U] =
        {
          (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
          (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
          (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
        };
      uint32_t len42 = (uint32_t)6U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t20;
      memset(partResult, 0U, (len42 + (uint32_t)1U) * sizeof (uint64_t));
      {
        uint64_t bj = (&bBuffer)[0U];
        uint64_t *res_j = partResult;
        uint64_t c = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len42 / (uint32_t)4U; i++)
        {
          uint64_t a_i = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i0);
          uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
          c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
          uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
          c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
          uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
          c = mul_wide_add2_u64(a_i2, bj, c, res_i);
        }
        for (uint32_t i = len42 / (uint32_t)4U * (uint32_t)4U; i < len42; i++)
        {
          uint64_t a_i = p1[i];
          uint64_t *res_i = res_j + i;
          c = mul_wide_add2_u64(a_i, bj, c, res_i);
        }
        uint64_t r1 = c;
        partResult[len42 + (uint32_t)0U] = r1;
      }
      uint32_t len43 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len43 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t20[(uint32_t)4U * i];
        uint64_t *res_i0 = t20 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t20[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = t20 + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t20[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = t20 + (uint32_t)4U * i + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t212, res_i2);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t20[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = t20 + (uint32_t)4U * i + (uint32_t)3U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, res_i);
      }
      for (uint32_t i = len43 / (uint32_t)4U * (uint32_t)4U; i < len43; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t20[i];
        uint64_t *res_i = t20 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
      }
      uint64_t carry2 = c;
      uint32_t len4 = (uint32_t)11U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t20[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry2;
    }
    uint32_t len32 = (uint32_t)6U;
    uint64_t cin0 = t0[len32];
    uint64_t *x_ = t0;
    uint32_t len4 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len4);
    uint64_t tempBuffer1[len4];
    memset(tempBuffer1, 0U, len4 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow = (uint64_t)0U;
    uint64_t
    p1[6U] =
      {
        (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
        (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
        (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
      };
    uint32_t len5 = (uint32_t)6U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len5 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t210 = p1[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t21, res_i);
    }
    for (uint32_t i = len5 / (uint32_t)4U * (uint32_t)4U; i < len5; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t21 = p1[i];
      uint64_t *res_i = tempBuffer1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
    }
    uint64_t r1 = c;
    uint64_t carry01 = r1;
    uint64_t
    carry2 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry01,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    cmovznz4_p384(carry2, tempBuffer1, x_, p);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask0 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)6U * sizeof (uint64_t));
}

static inline void exponent_p384(uint64_t *t, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)6U;
  uint64_t *t2 = tempBuffer + (uint32_t)12U;
  uint64_t *t3 = tempBuffer + (uint32_t)18U;
  uint64_t *t4 = tempBuffer + (uint32_t)24U;
  uint64_t *t5 = tempBuffer + (uint32_t)30U;
  montgomery_square_buffer_dh_p384(t, t0);
  montgomery_multiplication_buffer_dh_p384(t, t0, t0);
  montgomery_square_buffer_dh_p384(t0, t0);
  montgomery_multiplication_buffer_dh_p384(t, t0, t0);
  montgomery_square_buffer_dh_p384(t0, t1);
  {
    montgomery_square_buffer_dh_p384(t1, t1);
  }
  {
    montgomery_square_buffer_dh_p384(t1, t1);
  }
  montgomery_multiplication_buffer_dh_p384(t0, t1, t1);
  montgomery_square_buffer_dh_p384(t1, t2);
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  montgomery_multiplication_buffer_dh_p384(t2, t1, t2);
  montgomery_square_buffer_dh_p384(t2, t3);
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  {
    montgomery_square_buffer_dh_p384(t3, t3);
  }
  montgomery_multiplication_buffer_dh_p384(t2, t3, t2);
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  {
    montgomery_square_buffer_dh_p384(t2, t2);
  }
  montgomery_multiplication_buffer_dh_p384(t2, t1, t1);
  montgomery_square_buffer_dh_p384(t1, t2);
  montgomery_multiplication_buffer_dh_p384(t2, t, t2);
  montgomery_square_buffer_dh_p384(t2, t3);
  montgomery_multiplication_buffer_dh_p384(t, t3, t3);
  montgomery_square_buffer_dh_p384(t3, t4);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)30U; i++)
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t2, t4);
  montgomery_square_buffer_dh_p384(t4, t5);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)62U; i++)
  {
    montgomery_square_buffer_dh_p384(t5, t5);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t5, t4);
  montgomery_square_buffer_dh_p384(t4, t5);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)125U; i++)
  {
    montgomery_square_buffer_dh_p384(t5, t5);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t5, t4);
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t0, t4);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)33U; i++)
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t3, t4);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)94U; i++)
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t1, t4);
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  {
    montgomery_square_buffer_dh_p384(t4, t4);
  }
  montgomery_multiplication_buffer_dh_p384(t4, t, result);
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
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t6, t7);
  montgomery_square_buffer_dh_p256(t7, t0);
  montgomery_square_buffer_dh_p256(t0, t0);
  montgomery_multiplication_buffer_dh_p256(t0, t2, t1);
  montgomery_square_buffer_dh_p256(t1, t0);
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t1, t3);
  montgomery_square_buffer_dh_p256(t3, t0);
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
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
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  {
    montgomery_square_buffer_dh_p256(t0, t0);
  }
  montgomery_multiplication_buffer_dh_p256(t0, t, result);
}

static inline void square_root(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
{
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), sw0);
  uint64_t temp[sw0];
  memset(temp, 0U, sw0 * sizeof (uint64_t));
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        const uint8_t *sw;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              sw = sqPower_buffer_p256;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              sw = sqPower_buffer_p384;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        montgomery_ladder_power_p256_dh(a, sw, temp);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        const uint8_t *sw;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              sw = sqPower_buffer_p256;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              sw = sqPower_buffer_p384;
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        montgomery_ladder_power_p384_dh(a, sw, temp);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  memcpy(result, temp, sw * sizeof (uint64_t));
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
  uint64_t *temp = t12;
  uint64_t *u1 = t12 + (uint32_t)16U;
  uint64_t *u2 = t12 + (uint32_t)20U;
  uint64_t *s11 = t12 + (uint32_t)24U;
  uint64_t *s2 = t12 + (uint32_t)28U;
  uint64_t *h = t12 + (uint32_t)32U;
  uint64_t *r0 = t12 + (uint32_t)36U;
  uint64_t *uh0 = t12 + (uint32_t)40U;
  uint64_t *hCube0 = t12 + (uint32_t)44U;
  felem_sub_p256(u2, u1, h);
  felem_sub_p256(s2, s11, r0);
  montgomery_square_buffer_dh_p256(h, temp);
  montgomery_multiplication_buffer_dh_p256(temp, u1, uh0);
  montgomery_multiplication_buffer_dh_p256(temp, h, hCube0);
  uint64_t *h0 = t12 + (uint32_t)32U;
  uint64_t *r = t12 + (uint32_t)36U;
  uint64_t *uh = t12 + (uint32_t)40U;
  uint64_t *hCube = t12 + (uint32_t)44U;
  uint64_t *s1 = t12 + (uint32_t)24U;
  uint64_t *x3 = t5;
  uint64_t *rSquare = t5 + (uint32_t)4U;
  uint64_t *rH = t5 + (uint32_t)8U;
  uint64_t *twoUh = t5 + (uint32_t)12U;
  montgomery_square_buffer_dh_p256(r, rSquare);
  felem_sub_p256(rSquare, hCube, rH);
  felem_add_p256(uh, uh, twoUh);
  felem_sub_p256(rH, twoUh, x3);
  uint64_t *x30 = t5;
  uint64_t *y3 = t5 + (uint32_t)4U;
  uint64_t *s1hCube = t5 + (uint32_t)8U;
  uint64_t *u1hx3 = t5 + (uint32_t)12U;
  uint64_t *ru1hx3 = t5 + (uint32_t)16U;
  montgomery_multiplication_buffer_dh_p256(s1, hCube, s1hCube);
  felem_sub_p256(uh, x30, u1hx3);
  montgomery_multiplication_buffer_dh_p256(u1hx3, r, ru1hx3);
  felem_sub_p256(ru1hx3, s1hCube, y3);
  uint64_t *z1 = p + (uint32_t)8U;
  uint64_t *z2 = q + (uint32_t)8U;
  uint64_t *z3 = t5 + (uint32_t)8U;
  uint64_t *z1z2 = t5 + (uint32_t)12U;
  montgomery_multiplication_buffer_dh_p256(z1, z2, z1z2);
  montgomery_multiplication_buffer_dh_p256(z1z2, h0, z3);
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
  copy_conditional_p256_l(x3_out, p_x0, mask);
  copy_conditional_p256_l(y3_out, p_y0, mask);
  copy_conditional_p256_l(z3_out, p_z0, mask);
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
  copy_conditional_p256_l(x3_out, p_x, mask0);
  copy_conditional_p256_l(y3_out, p_y, mask0);
  copy_conditional_p256_l(z3_out, p_z, mask0);
  memcpy(result, x3_out, (uint32_t)4U * sizeof (uint64_t));
  memcpy(result + (uint32_t)4U, y3_out, (uint32_t)4U * sizeof (uint64_t));
  memcpy(result + (uint32_t)8U, z3_out, (uint32_t)4U * sizeof (uint64_t));
}

static inline void
point_add_p384(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t12 = tempBuffer;
  uint64_t *t5 = tempBuffer + (uint32_t)72U;
  uint64_t *t4 = t12;
  uint64_t *u10 = t12 + (uint32_t)24U;
  uint64_t *u20 = t12 + (uint32_t)30U;
  uint64_t *s10 = t12 + (uint32_t)36U;
  uint64_t *s20 = t12 + (uint32_t)42U;
  uint64_t *pX = p;
  uint64_t *pY = p + (uint32_t)6U;
  uint64_t *pZ = p + (uint32_t)12U;
  uint64_t *qX = q;
  uint64_t *qY = q + (uint32_t)6U;
  uint64_t *qZ = q + (uint32_t)12U;
  uint64_t *z2Square = t4;
  uint64_t *z1Square = t4 + (uint32_t)6U;
  uint64_t *z2Cube = t4 + (uint32_t)12U;
  uint64_t *z1Cube = t4 + (uint32_t)18U;
  montgomery_square_buffer_dh_p384(qZ, z2Square);
  montgomery_square_buffer_dh_p384(pZ, z1Square);
  montgomery_multiplication_buffer_dh_p384(z2Square, qZ, z2Cube);
  montgomery_multiplication_buffer_dh_p384(z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer_dh_p384(z2Square, pX, u10);
  montgomery_multiplication_buffer_dh_p384(z1Square, qX, u20);
  montgomery_multiplication_buffer_dh_p384(z2Cube, pY, s10);
  montgomery_multiplication_buffer_dh_p384(z1Cube, qY, s20);
  uint64_t *temp = t12;
  uint64_t *u1 = t12 + (uint32_t)24U;
  uint64_t *u2 = t12 + (uint32_t)30U;
  uint64_t *s11 = t12 + (uint32_t)36U;
  uint64_t *s2 = t12 + (uint32_t)42U;
  uint64_t *h = t12 + (uint32_t)48U;
  uint64_t *r0 = t12 + (uint32_t)54U;
  uint64_t *uh0 = t12 + (uint32_t)60U;
  uint64_t *hCube0 = t12 + (uint32_t)66U;
  felem_sub_p384(u2, u1, h);
  felem_sub_p384(s2, s11, r0);
  montgomery_square_buffer_dh_p384(h, temp);
  montgomery_multiplication_buffer_dh_p384(temp, u1, uh0);
  montgomery_multiplication_buffer_dh_p384(temp, h, hCube0);
  uint64_t *h0 = t12 + (uint32_t)48U;
  uint64_t *r = t12 + (uint32_t)54U;
  uint64_t *uh = t12 + (uint32_t)60U;
  uint64_t *hCube = t12 + (uint32_t)66U;
  uint64_t *s1 = t12 + (uint32_t)36U;
  uint64_t *x3 = t5;
  uint64_t *rSquare = t5 + (uint32_t)6U;
  uint64_t *rH = t5 + (uint32_t)12U;
  uint64_t *twoUh = t5 + (uint32_t)18U;
  montgomery_square_buffer_dh_p384(r, rSquare);
  felem_sub_p384(rSquare, hCube, rH);
  felem_add_p384(uh, uh, twoUh);
  felem_sub_p384(rH, twoUh, x3);
  uint64_t *x30 = t5;
  uint64_t *y3 = t5 + (uint32_t)6U;
  uint64_t *s1hCube = t5 + (uint32_t)12U;
  uint64_t *u1hx3 = t5 + (uint32_t)18U;
  uint64_t *ru1hx3 = t5 + (uint32_t)24U;
  montgomery_multiplication_buffer_dh_p384(s1, hCube, s1hCube);
  felem_sub_p384(uh, x30, u1hx3);
  montgomery_multiplication_buffer_dh_p384(u1hx3, r, ru1hx3);
  felem_sub_p384(ru1hx3, s1hCube, y3);
  uint64_t *z1 = p + (uint32_t)12U;
  uint64_t *z2 = q + (uint32_t)12U;
  uint64_t *z3 = t5 + (uint32_t)12U;
  uint64_t *z1z2 = t5 + (uint32_t)18U;
  montgomery_multiplication_buffer_dh_p384(z1, z2, z1z2);
  montgomery_multiplication_buffer_dh_p384(z1z2, h0, z3);
  uint64_t *x3_out = t5;
  uint64_t *y3_out = t5 + (uint32_t)6U;
  uint64_t *z3_out = t5 + (uint32_t)12U;
  uint64_t *z = p + (uint32_t)12U;
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len0 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len0; i++)
  {
    uint64_t a_i = z[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t mask = tmp1;
  uint64_t *p_x0 = q;
  uint64_t *p_y0 = q + (uint32_t)6U;
  uint64_t *p_z0 = q + (uint32_t)12U;
  copy_conditional_p384_l(x3_out, p_x0, mask);
  copy_conditional_p384_l(y3_out, p_y0, mask);
  copy_conditional_p384_l(z3_out, p_z0, mask);
  uint64_t *z0 = q + (uint32_t)12U;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t a_i = z0[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t mask0 = tmp;
  uint64_t *p_x = p;
  uint64_t *p_y = p + (uint32_t)6U;
  uint64_t *p_z = p + (uint32_t)12U;
  copy_conditional_p384_l(x3_out, p_x, mask0);
  copy_conditional_p384_l(y3_out, p_y, mask0);
  copy_conditional_p384_l(z3_out, p_z, mask0);
  memcpy(result, x3_out, (uint32_t)6U * sizeof (uint64_t));
  memcpy(result + (uint32_t)6U, y3_out, (uint32_t)6U * sizeof (uint64_t));
  memcpy(result + (uint32_t)12U, z3_out, (uint32_t)6U * sizeof (uint64_t));
}

static inline void toUint64ChangeEndian_p256(uint8_t *i, uint64_t *o)
{
  uint32_t len = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t *os = o;
    uint8_t *bj = i + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
  }
  uint32_t len1 = (uint32_t)4U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i0;
    uint64_t left = o[i0];
    uint64_t right = o[lenRight];
    o[i0] = right;
    o[lenRight] = left;
  }
}

static inline void toUint64ChangeEndian_p384(uint8_t *i, uint64_t *o)
{
  uint32_t len = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t *os = o;
    uint8_t *bj = i + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
  }
  uint32_t len1 = (uint32_t)6U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i0;
    uint64_t left = o[i0];
    uint64_t right = o[lenRight];
    o[i0] = right;
    o[lenRight] = left;
  }
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

static inline void point_double_p384(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)6U;
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
  uint32_t coordinateLen = (uint32_t)6U;
  uint64_t *pX1 = p;
  uint64_t *pY1 = p + coordinateLen;
  uint64_t *pZ1 = p + (uint32_t)2U * coordinateLen;
  uint64_t *a0 = tmp;
  uint64_t *a1 = tmp + coordinateLen;
  uint64_t *alpha0 = tmp + (uint32_t)2U * coordinateLen;
  montgomery_square_buffer_dh_p384(pZ1, delta);
  montgomery_square_buffer_dh_p384(pY1, gamma);
  montgomery_multiplication_buffer_dh_p384(pX1, gamma, beta);
  felem_sub_p384(pX1, delta, a0);
  felem_add_p384(pX1, delta, a1);
  montgomery_multiplication_buffer_dh_p384(a0, a1, alpha0);
  felem_add_p384(alpha0, alpha0, alpha);
  felem_add_p384(alpha0, alpha, alpha);
  montgomery_square_buffer_dh_p384(alpha, x3);
  felem_add_p384(beta, beta, fourBeta);
  felem_add_p384(fourBeta, fourBeta, fourBeta);
  felem_add_p384(fourBeta, fourBeta, eightBeta);
  felem_sub_p384(x3, eightBeta, x3);
  felem_add_p384(pY, pZ, z3);
  montgomery_square_buffer_dh_p384(z3, z3);
  felem_sub_p384(z3, gamma, z3);
  felem_sub_p384(z3, delta, z3);
  felem_sub_p384(fourBeta, x3, y3);
  montgomery_multiplication_buffer_dh_p384(alpha, y3, y3);
  montgomery_square_buffer_dh_p384(gamma, gamma);
  felem_add_p384(gamma, gamma, eightGamma);
  felem_add_p384(eightGamma, eightGamma, eightGamma);
  felem_add_p384(eightGamma, eightGamma, eightGamma);
  felem_sub_p384(y3, eightGamma, y3);
}

static void montgomery_multiplication_buffer_by_one_mixed_p256(uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  t_low[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    t_low[i] = (uint64_t)0U;
  }
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
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
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
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
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
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
  uint32_t len20 = (uint32_t)4U;
  uint64_t cin = t[len20];
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
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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

static void montgomery_multiplication_buffer_by_one_mixed_p384(uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  t_low[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    t_low[i] = (uint64_t)0U;
  }
  uint32_t len10 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
  uint64_t t2[(uint32_t)2U * len10];
  memset(t2, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)6U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len31 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
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
    uint32_t len3 = (uint32_t)11U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len20 = (uint32_t)6U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len4 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, x_, result);
}

static void
copy_point_conditional(
  Spec_ECC_Curves_curve c,
  uint64_t *x3_out,
  uint64_t *y3_out,
  uint64_t *z3_out,
  uint64_t *p,
  uint64_t *maskPoint,
  uint64_t *temp
)
{
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  uint64_t *z = maskPoint + (uint32_t)2U * sw0;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len0 = (uint32_t)6U;
        break;
      }
    default:
      {
        len0 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len0; i++)
  {
    uint64_t a_i = z[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t mask = tmp;
  uint64_t *p_x = p;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint64_t *p_y = p + sw;
  temp[0U] = (uint64_t)1U;
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)1U; i < len; i++)
  {
    temp[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(x3_out, p_x, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(x3_out, p_x, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(y3_out, p_y, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(y3_out, p_y, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(z3_out, temp, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(z3_out, temp, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
copy_point_conditional1(
  Spec_ECC_Curves_curve c,
  uint64_t *x3_out,
  uint64_t *y3_out,
  uint64_t *z3_out,
  uint64_t *p,
  uint64_t *q
)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint64_t *x = q;
  uint64_t *y = q + len;
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len10;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len10 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len10 = (uint32_t)6U;
        break;
      }
    default:
      {
        len10 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    uint64_t a_i = x[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t xZero = tmp1;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len1 = (uint32_t)6U;
        break;
      }
    default:
      {
        len1 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t a_i = y[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t yZero = tmp;
  uint64_t mask = xZero & yZero;
  uint64_t *p_x = p;
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  uint64_t *p_y = p + sw0;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint64_t *p_z = p + (uint32_t)2U * sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(x3_out, p_x, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(x3_out, p_x, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(y3_out, p_y, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(y3_out, p_y, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(z3_out, p_z, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(z3_out, p_z, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
_point_add_if_second_branch_impl(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  uint64_t *q,
  uint64_t *x3hCube,
  uint64_t *t5
)
{
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  uint64_t *h = x3hCube + (uint32_t)8U * sw0;
  uint32_t sw1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw1 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw1 = (uint32_t)4U;
      }
  }
  uint64_t *r = x3hCube + (uint32_t)9U * sw1;
  uint32_t sw2;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw2 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw2 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw2 = (uint32_t)4U;
      }
  }
  uint64_t *uh = x3hCube + (uint32_t)10U * sw2;
  uint32_t sw3;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw3 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw3 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw3 = (uint32_t)4U;
      }
  }
  uint64_t *hCube = x3hCube + (uint32_t)11U * sw3;
  uint32_t sw4;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw4 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw4 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw4 = (uint32_t)4U;
      }
  }
  uint64_t *u1 = x3hCube + (uint32_t)4U * sw4;
  uint32_t sw5;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw5 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw5 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw5 = (uint32_t)4U;
      }
  }
  uint64_t *u2 = x3hCube + (uint32_t)5U * sw5;
  uint32_t sw6;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw6 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw6 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw6 = (uint32_t)4U;
      }
  }
  uint64_t *s1 = x3hCube + (uint32_t)6U * sw6;
  uint32_t sw7;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw7 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw7 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw7 = (uint32_t)4U;
      }
  }
  uint64_t *s2 = x3hCube + (uint32_t)7U * sw7;
  uint64_t *x3 = t5;
  uint32_t sw8;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw8 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw8 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw8 = (uint32_t)4U;
      }
  }
  uint64_t *rSquare = t5 + sw8;
  uint32_t sw9;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw9 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw9 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw9 = (uint32_t)4U;
      }
  }
  uint64_t *rH = t5 + (uint32_t)2U * sw9;
  uint32_t sw10;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw10 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw10 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw10 = (uint32_t)4U;
      }
  }
  uint64_t *twoUh = t5 + (uint32_t)3U * sw10;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_square_buffer_dh_p256(r, rSquare);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_square_buffer_dh_p384(r, rSquare);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_sub_p256(rSquare, hCube, rH);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_sub_p384(rSquare, hCube, rH);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_add_p256(uh, uh, twoUh);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_add_p384(uh, uh, twoUh);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_sub_p256(rH, twoUh, x3);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_sub_p384(rH, twoUh, x3);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t *x30 = t5;
  uint32_t sw11;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw11 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw11 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw11 = (uint32_t)4U;
      }
  }
  uint64_t *y3 = t5 + sw11;
  uint32_t sw12;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw12 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw12 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw12 = (uint32_t)4U;
      }
  }
  uint64_t *s1hCube = t5 + (uint32_t)2U * sw12;
  uint32_t sw13;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw13 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw13 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw13 = (uint32_t)4U;
      }
  }
  uint64_t *u1hx3 = t5 + (uint32_t)3U * sw13;
  uint32_t sw14;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw14 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw14 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw14 = (uint32_t)4U;
      }
  }
  uint64_t *ru1hx3 = t5 + (uint32_t)4U * sw14;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(s1, hCube, s1hCube);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(s1, hCube, s1hCube);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_sub_p256(uh, x30, u1hx3);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_sub_p384(uh, x30, u1hx3);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(u1hx3, r, ru1hx3);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(u1hx3, r, ru1hx3);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_sub_p256(ru1hx3, s1hCube, y3);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_sub_p384(ru1hx3, s1hCube, y3);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sw15;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw15 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw15 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw15 = (uint32_t)4U;
      }
  }
  uint64_t *z1 = p + (uint32_t)2U * sw15;
  uint32_t sw16;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw16 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw16 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw16 = (uint32_t)4U;
      }
  }
  uint64_t *z3 = t5 + (uint32_t)2U * sw16;
  uint32_t sw17;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw17 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw17 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw17 = (uint32_t)4U;
      }
  }
  uint64_t *z1z2 = t5 + (uint32_t)3U * sw17;
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, z1, len * sizeof (uint64_t));
  uint32_t len1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len1 = (uint32_t)6U;
        break;
      }
    default:
      {
        len1 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len1);
  uint64_t t2[(uint32_t)2U * len1];
  memset(t2, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
  uint32_t len2;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len2 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len2 = (uint32_t)6U;
        break;
      }
    default:
      {
        len2 = (uint32_t)4U;
      }
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t sw18;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw18 = (uint64_t)0xffffffffffffffffU;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw18 = (uint64_t)0xffffffffU;
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    if (FStar_UInt64_v(sw18) == (krml_checked_int_t)18446744073709551615)
    {
      uint64_t t1 = t[0U];
      uint32_t sw;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            sw = (uint32_t)4U;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            sw = (uint32_t)6U;
            break;
          }
        default:
          {
            sw = (uint32_t)4U;
          }
      }
      uint32_t len30 = sw * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len30; i++)
      {
        t2[i] = (uint64_t)0U;
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            uint64_t temp = (uint64_t)0U;
            uint64_t f0 = (uint64_t)0xffffffffffffffffU;
            uint64_t f1 = (uint64_t)0xffffffffU;
            uint64_t f3 = (uint64_t)0xffffffff00000001U;
            uint64_t *o0 = t2;
            uint64_t *o1 = t2 + (uint32_t)1U;
            uint64_t *o2 = t2 + (uint32_t)2U;
            uint64_t *o3 = t2 + (uint32_t)3U;
            uint64_t *o4 = t2 + (uint32_t)4U;
            mul64(f0, t1, o0, &temp);
            uint64_t h2 = temp;
            mul64(f1, t1, o1, &temp);
            uint64_t l = o1[0U];
            uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h2, o1);
            uint64_t h3 = temp;
            o2[0U] = h3 + c1;
            mul64(f3, t1, o3, o4);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            uint64_t
            p1[6U] =
              {
                (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
                (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
                (uint64_t)0xffffffffffffffffU
              };
            uint32_t len3;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  len3 = (uint32_t)4U;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  len3 = (uint32_t)6U;
                  break;
                }
              default:
                {
                  len3 = (uint32_t)4U;
                }
            }
            uint64_t bBuffer = t1;
            uint64_t *partResult = t2;
            memset(partResult, 0U, (len3 + (uint32_t)1U) * sizeof (uint64_t));
            {
              uint64_t bj = (&bBuffer)[0U];
              uint64_t *res_j = partResult;
              uint64_t c1 = (uint64_t)0U;
              for (uint32_t i = (uint32_t)0U; i < len3 / (uint32_t)4U; i++)
              {
                uint64_t a_i = p1[(uint32_t)4U * i];
                uint64_t *res_i0 = res_j + (uint32_t)4U * i;
                c1 = mul_wide_add2_u64(a_i, bj, c1, res_i0);
                uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
                uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
                c1 = mul_wide_add2_u64(a_i0, bj, c1, res_i1);
                uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
                uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
                c1 = mul_wide_add2_u64(a_i1, bj, c1, res_i2);
                uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
                c1 = mul_wide_add2_u64(a_i2, bj, c1, res_i);
              }
              for (uint32_t i = len3 / (uint32_t)4U * (uint32_t)4U; i < len3; i++)
              {
                uint64_t a_i = p1[i];
                uint64_t *res_i = res_j + i;
                c1 = mul_wide_add2_u64(a_i, bj, c1, res_i);
              }
              uint64_t r1 = c1;
              partResult[len3 + (uint32_t)0U] = r1;
            }
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
    }
    else
    {
      uint64_t k0;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            k0 = (uint64_t)1U;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            k0 = (uint64_t)4294967297U;
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      uint64_t t1 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      mul_atomic(t1, k0, &y, &temp);
      uint64_t y_ = y;
      uint32_t sw;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            sw = (uint32_t)4U;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            sw = (uint32_t)6U;
            break;
          }
        default:
          {
            sw = (uint32_t)4U;
          }
      }
      uint32_t len30 = sw * (uint32_t)2U;
      for (uint32_t i = (uint32_t)0U; i < len30; i++)
      {
        t2[i] = (uint64_t)0U;
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            uint64_t temp1 = (uint64_t)0U;
            uint64_t f0 = (uint64_t)0xffffffffffffffffU;
            uint64_t f1 = (uint64_t)0xffffffffU;
            uint64_t f3 = (uint64_t)0xffffffff00000001U;
            uint64_t *o0 = t2;
            uint64_t *o1 = t2 + (uint32_t)1U;
            uint64_t *o2 = t2 + (uint32_t)2U;
            uint64_t *o3 = t2 + (uint32_t)3U;
            uint64_t *o4 = t2 + (uint32_t)4U;
            mul64(f0, y_, o0, &temp1);
            uint64_t h30 = temp1;
            mul64(f1, y_, o1, &temp1);
            uint64_t l = o1[0U];
            uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h30, o1);
            uint64_t h3 = temp1;
            o2[0U] = h3 + c1;
            mul64(f3, y_, o3, o4);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            uint64_t
            p1[6U] =
              {
                (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
                (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
                (uint64_t)0xffffffffffffffffU
              };
            uint32_t len3;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  len3 = (uint32_t)4U;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  len3 = (uint32_t)6U;
                  break;
                }
              default:
                {
                  len3 = (uint32_t)4U;
                }
            }
            uint64_t bBuffer = y_;
            uint64_t *partResult = t2;
            memset(partResult, 0U, (len3 + (uint32_t)1U) * sizeof (uint64_t));
            {
              uint64_t bj = (&bBuffer)[0U];
              uint64_t *res_j = partResult;
              uint64_t c1 = (uint64_t)0U;
              for (uint32_t i = (uint32_t)0U; i < len3 / (uint32_t)4U; i++)
              {
                uint64_t a_i = p1[(uint32_t)4U * i];
                uint64_t *res_i0 = res_j + (uint32_t)4U * i;
                c1 = mul_wide_add2_u64(a_i, bj, c1, res_i0);
                uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
                uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
                c1 = mul_wide_add2_u64(a_i0, bj, c1, res_i1);
                uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
                uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
                c1 = mul_wide_add2_u64(a_i1, bj, c1, res_i2);
                uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
                c1 = mul_wide_add2_u64(a_i2, bj, c1, res_i);
              }
              for (uint32_t i = len3 / (uint32_t)4U * (uint32_t)4U; i < len3; i++)
              {
                uint64_t a_i = p1[i];
                uint64_t *res_i = res_j + i;
                c1 = mul_wide_add2_u64(a_i, bj, c1, res_i);
              }
              uint64_t r1 = c1;
              partResult[len3 + (uint32_t)0U] = r1;
            }
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
    }
    uint32_t sw19;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw19 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw19 = (uint32_t)6U;
          break;
        }
      default:
        {
          sw19 = (uint32_t)4U;
        }
    }
    uint32_t len3 = sw19 * (uint32_t)2U;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len3 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      uint64_t *res_i0 = t2 + (uint32_t)4U * i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, res_i0);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = t2 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t211, res_i1);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = t2 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t212, res_i2);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = t2 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t21, res_i);
    }
    for (uint32_t i = len3 / (uint32_t)4U * (uint32_t)4U; i < len3; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      uint64_t *res_i = t2 + i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, res_i);
    }
    uint64_t carry = c1;
    uint32_t sw;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw = (uint32_t)6U;
          break;
        }
      default:
        {
          sw = (uint32_t)4U;
        }
    }
    uint32_t len30 = sw * (uint32_t)2U - (uint32_t)1U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len30] = carry;
  }
  uint32_t len20;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len20 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len20 = (uint32_t)6U;
        break;
      }
    default:
      {
        len20 = (uint32_t)4U;
      }
  }
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len3 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len3 = (uint32_t)6U;
        break;
      }
    default:
      {
        len3 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t carry0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint64_t
        p1[4U] =
          {
            (uint64_t)0xffffffffffffffffU,
            (uint64_t)0xffffffffU,
            (uint64_t)0U,
            (uint64_t)0xffffffff00000001U
          };
        uint32_t len4;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              len4 = (uint32_t)4U;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              len4 = (uint32_t)6U;
              break;
            }
          default:
            {
              len4 = (uint32_t)4U;
            }
        }
        uint64_t c1 = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t210 = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t210, res_i0);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t211, res_i1);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t212, res_i2);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t21, res_i);
        }
        for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t21 = p1[i];
          uint64_t *res_i = tempBuffer + i;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t21, res_i);
        }
        uint64_t r1 = c1;
        carry0 = r1;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t
        p1[6U] =
          {
            (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
            (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
            (uint64_t)0xffffffffffffffffU
          };
        uint32_t len4;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              len4 = (uint32_t)4U;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              len4 = (uint32_t)6U;
              break;
            }
          default:
            {
              len4 = (uint32_t)4U;
            }
        }
        uint64_t c1 = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t210 = p1[(uint32_t)4U * i];
          uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t210, res_i0);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t211, res_i1);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t212, res_i2);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t21, res_i);
        }
        for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t21 = p1[i];
          uint64_t *res_i = tempBuffer + i;
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t21, res_i);
        }
        uint64_t r1 = c1;
        carry0 = r1;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        cmovznz4_p256(carry, tempBuffer, x_, z1z2);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        cmovznz4_p384(carry, tempBuffer, x_, z1z2);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(z1z2, h, z3);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(z1z2, h, z3);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t *x3_out = t5;
  uint32_t sw18;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw18 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw18 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw18 = (uint32_t)4U;
      }
  }
  uint64_t *y3_out = t5 + sw18;
  uint32_t sw19;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw19 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw19 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw19 = (uint32_t)4U;
      }
  }
  uint64_t *z3_out = t5 + (uint32_t)2U * sw19;
  uint32_t sw20;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw20 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw20 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw20 = (uint32_t)4U;
      }
  }
  uint64_t *temp = t5 + (uint32_t)3U * sw20;
  copy_point_conditional(c, x3_out, y3_out, z3_out, q, p, temp);
  copy_point_conditional1(c, x3_out, y3_out, z3_out, p, q);
  uint64_t *uu____0 = result;
  uint32_t sw21;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw21 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw21 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw21 = (uint32_t)4U;
      }
  }
  memcpy(uu____0, x3_out, sw21 * sizeof (uint64_t));
  uint32_t sw22;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw22 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw22 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw22 = (uint32_t)4U;
      }
  }
  uint64_t *uu____1 = result + sw22;
  uint32_t sw23;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw23 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw23 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw23 = (uint32_t)4U;
      }
  }
  memcpy(uu____1, y3_out, sw23 * sizeof (uint64_t));
  uint32_t sw24;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw24 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw24 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw24 = (uint32_t)4U;
      }
  }
  uint64_t *uu____2 = result + (uint32_t)2U * sw24;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  memcpy(uu____2, z3_out, sw * sizeof (uint64_t));
}

static inline void
point_add_mixed_p256(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
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
  uint64_t *z2Square = t4;
  uint64_t *z1Square = t4 + (uint32_t)4U;
  uint64_t *z2Cube = t4 + (uint32_t)8U;
  uint64_t *z1Cube = t4 + (uint32_t)12U;
  montgomery_multiplication_buffer_by_one_mixed_p256(z2Square);
  montgomery_square_buffer_dh_p256(pZ, z1Square);
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, z2Square, len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len1);
  uint64_t t2[(uint32_t)2U * len1];
  memset(t2, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
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
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      uint64_t *res_i0 = t2 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = t2 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = t2 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t212, res_i2);
      uint64_t t14 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = t2 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t14, t21, res_i);
    }
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
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
  uint32_t len20 = (uint32_t)4U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer1[len3];
  memset(tempBuffer1, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p1[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len4 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t210 = p1[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
    uint64_t t13 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t13, t21, res_i);
  }
  for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t21 = p1[i];
    uint64_t *res_i = tempBuffer1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
  }
  uint64_t r0 = c;
  uint64_t carry0 = r0;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p256(carry, tempBuffer1, x_, z2Cube);
  montgomery_multiplication_buffer_dh_p256(z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer_dh_p256(z2Square, pX, u10);
  montgomery_multiplication_buffer_dh_p256(z1Square, qX, u20);
  montgomery_multiplication_buffer_dh_p256(z2Cube, pY, s10);
  montgomery_multiplication_buffer_dh_p256(z1Cube, qY, s20);
  uint64_t *temp = t12;
  uint64_t *u1 = t12 + (uint32_t)16U;
  uint64_t *u2 = t12 + (uint32_t)20U;
  uint64_t *s1 = t12 + (uint32_t)24U;
  uint64_t *s2 = t12 + (uint32_t)28U;
  uint64_t *h = t12 + (uint32_t)32U;
  uint64_t *r = t12 + (uint32_t)36U;
  uint64_t *uh = t12 + (uint32_t)40U;
  uint64_t *hCube = t12 + (uint32_t)44U;
  felem_sub_p256(u2, u1, h);
  felem_sub_p256(s2, s1, r);
  montgomery_square_buffer_dh_p256(h, temp);
  montgomery_multiplication_buffer_dh_p256(temp, u1, uh);
  montgomery_multiplication_buffer_dh_p256(temp, h, hCube);
  _point_add_if_second_branch_impl(Spec_ECC_Curves_P256, result, p, q, t12, t5);
}

static inline void
point_add_mixed_p384(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t12 = tempBuffer;
  uint64_t *t5 = tempBuffer + (uint32_t)72U;
  uint64_t *t4 = t12;
  uint64_t *u10 = t12 + (uint32_t)24U;
  uint64_t *u20 = t12 + (uint32_t)30U;
  uint64_t *s10 = t12 + (uint32_t)36U;
  uint64_t *s20 = t12 + (uint32_t)42U;
  uint64_t *pX = p;
  uint64_t *pY = p + (uint32_t)6U;
  uint64_t *pZ = p + (uint32_t)12U;
  uint64_t *qX = q;
  uint64_t *qY = q + (uint32_t)6U;
  uint64_t *z2Square = t4;
  uint64_t *z1Square = t4 + (uint32_t)6U;
  uint64_t *z2Cube = t4 + (uint32_t)12U;
  uint64_t *z1Cube = t4 + (uint32_t)18U;
  montgomery_multiplication_buffer_by_one_mixed_p384(z2Square);
  montgomery_square_buffer_dh_p384(pZ, z1Square);
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, z2Square, len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len1);
  uint64_t t2[(uint32_t)2U * len1];
  memset(t2, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)6U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p1[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len31 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p1[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p1[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p1[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p1[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p1[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      uint64_t *res_i0 = t2 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, res_i0);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = t2 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t211, res_i1);
      uint64_t t13 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = t2 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t212, res_i2);
      uint64_t t14 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = t2 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t14, t21, res_i);
    }
    for (uint32_t i = len32 / (uint32_t)4U * (uint32_t)4U; i < len32; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      uint64_t *res_i = t2 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, res_i);
    }
    uint64_t carry = c;
    uint32_t len3 = (uint32_t)11U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len20 = (uint32_t)6U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer1[len3];
  memset(tempBuffer1, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p1[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len4 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
  {
    uint64_t t1 = x_[(uint32_t)4U * i];
    uint64_t t210 = p1[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t210, res_i0);
    uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t211 = p1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t211, res_i1);
    uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t212 = p1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t212, res_i2);
    uint64_t t13 = x_[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t13, t21, res_i);
  }
  for (uint32_t i = len4 / (uint32_t)4U * (uint32_t)4U; i < len4; i++)
  {
    uint64_t t1 = x_[i];
    uint64_t t21 = p1[i];
    uint64_t *res_i = tempBuffer1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t21, res_i);
  }
  uint64_t r0 = c;
  uint64_t carry0 = r0;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4_p384(carry, tempBuffer1, x_, z2Cube);
  montgomery_multiplication_buffer_dh_p384(z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer_dh_p384(z2Square, pX, u10);
  montgomery_multiplication_buffer_dh_p384(z1Square, qX, u20);
  montgomery_multiplication_buffer_dh_p384(z2Cube, pY, s10);
  montgomery_multiplication_buffer_dh_p384(z1Cube, qY, s20);
  uint64_t *temp = t12;
  uint64_t *u1 = t12 + (uint32_t)24U;
  uint64_t *u2 = t12 + (uint32_t)30U;
  uint64_t *s1 = t12 + (uint32_t)36U;
  uint64_t *s2 = t12 + (uint32_t)42U;
  uint64_t *h = t12 + (uint32_t)48U;
  uint64_t *r = t12 + (uint32_t)54U;
  uint64_t *uh = t12 + (uint32_t)60U;
  uint64_t *hCube = t12 + (uint32_t)66U;
  felem_sub_p384(u2, u1, h);
  felem_sub_p384(s2, s1, r);
  montgomery_square_buffer_dh_p384(h, temp);
  montgomery_multiplication_buffer_dh_p384(temp, u1, uh);
  montgomery_multiplication_buffer_dh_p384(temp, h, hCube);
  _point_add_if_second_branch_impl(Spec_ECC_Curves_P384, result, p, q, t12, t5);
}

static uint32_t computeBit(Spec_ECC_Curves_curve c, uint32_t i)
{
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  return sw * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - (i << (uint32_t)2U);
}

static const
uint64_t
points_radix_16_p256[128U] =
  {
    (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U,
    (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x1fb38ab1388ad777U, (uint64_t)0x1dfee06615fa309dU,
    (uint64_t)0xfcac986c3afea4a7U, (uint64_t)0xdf65c2da29fb821aU, (uint64_t)0xeff44e23f63f8f6dU,
    (uint64_t)0xaa02cd3ed4b681a4U, (uint64_t)0xdd5fda3363818af8U, (uint64_t)0xfc53bc2629fbf0b3U,
    (uint64_t)0x12631d721b91beeaU, (uint64_t)0x5f73f2d3a11a09f8U, (uint64_t)0xac41f54484d5fcd8U,
    (uint64_t)0x86578e5c56025df4U, (uint64_t)0x577c956b15ed6b5aU, (uint64_t)0xb59c5f77982d848U,
    (uint64_t)0xb7c5e2c190fcdcc2U, (uint64_t)0x7d64d13ef1c91ffdU, (uint64_t)0xd40c2d6273f9d9f1U,
    (uint64_t)0x4dc6f628063ef17cU, (uint64_t)0x498e81df7ab17aa5U, (uint64_t)0xabb2a5026f17173cU,
    (uint64_t)0x4a3d7527f6739ef3U, (uint64_t)0xd941003268184c91U, (uint64_t)0xd2d458b8d401508bU,
    (uint64_t)0xb7437ab810ac5451U, (uint64_t)0x5256d9bdab491252U, (uint64_t)0x972d326eb1084c12U,
    (uint64_t)0xc3e96455e2ec3bfaU, (uint64_t)0xb75c723b549a10ffU, (uint64_t)0x9d9185f9f8a18961U,
    (uint64_t)0x2200a07b8589ba82U, (uint64_t)0x637b9d96fd4e9f5eU, (uint64_t)0xce75bfb2575e6cfaU,
    (uint64_t)0x7dd4477db8b77c7dU, (uint64_t)0x80818a776e5503b0U, (uint64_t)0x6fc7d58fb59581dU,
    (uint64_t)0xd899fb87efe43022U, (uint64_t)0x23b9912111694135U, (uint64_t)0x7e5de7bac33fa1c8U,
    (uint64_t)0xb3b83722a70e7d43U, (uint64_t)0xf06cfecbfb9bb38fU, (uint64_t)0xaa39277dfa93656U,
    (uint64_t)0x3dabb6cce67c5201U, (uint64_t)0x473ffb8bf1f94677U, (uint64_t)0xb9f0b93637453e56U,
    (uint64_t)0x8fce12ec20958fb2U, (uint64_t)0xcc16d74ff7786061U, (uint64_t)0x3678438a8235d096U,
    (uint64_t)0xe39ea044f06b43f6U, (uint64_t)0xbb40bdb5775c9950U, (uint64_t)0xd244a74cdc703cddU,
    (uint64_t)0x83dc1b8a6105dd53U, (uint64_t)0x38d9d50d49ef0437U, (uint64_t)0x58be44eba6096472U,
    (uint64_t)0x960afaec386fa5c5U, (uint64_t)0x1440032e000134b9U, (uint64_t)0x601e721454d6ba96U,
    (uint64_t)0x79ec42228671b9b6U, (uint64_t)0xfdc00dc48df9e25cU, (uint64_t)0x44500833d71d2e77U,
    (uint64_t)0x2bda4c3c0bc103d5U, (uint64_t)0x51528408aa925d53U, (uint64_t)0xefcb55b9c2f3a37dU,
    (uint64_t)0x9f28f6bb9846c915U, (uint64_t)0xe1547ce1d8340e55U, (uint64_t)0x97e310c1995b3ed2U,
    (uint64_t)0xed861937196256e6U, (uint64_t)0x1c6762abff2c65f2U, (uint64_t)0x268345e0978fceddU,
    (uint64_t)0x35ca2e572b784881U, (uint64_t)0x28ac888da0acd1b7U, (uint64_t)0x305640dc06a41bafU,
    (uint64_t)0x997c6fd2cb671bfbU, (uint64_t)0xf40d9eaf4a31e15aU, (uint64_t)0x8991dd7d54cfe03aU,
    (uint64_t)0x4889a3463a8deb0cU, (uint64_t)0x4cbf48092cd0a1faU, (uint64_t)0xc6965c4fbe18fb8cU,
    (uint64_t)0x1d499d0cb216fa84U, (uint64_t)0x8d5fe52c705dd3ebU, (uint64_t)0x812b268f84313b34U,
    (uint64_t)0x313b58808261591aU, (uint64_t)0xc2c322508f53d933U, (uint64_t)0xa49ef3f95094ed1bU,
    (uint64_t)0x13e326786e98c63U, (uint64_t)0x34be8167cd460429U, (uint64_t)0x698a328099a6b31U,
    (uint64_t)0xb9be3ba51b0c922dU, (uint64_t)0xe59cca03f7674edU, (uint64_t)0x4fbf7e505d3aca7cU,
    (uint64_t)0x2f4f8ba62020715U, (uint64_t)0x840502262ac1ec42U, (uint64_t)0xb8e0532775197de7U,
    (uint64_t)0x9142a358cf4e9b4bU, (uint64_t)0xc86a3c567e5d8626U, (uint64_t)0xd4051282b4a7992aU,
    (uint64_t)0xe7573c5999e3974eU, (uint64_t)0xd814a606da7bd76bU, (uint64_t)0x15604730f38cb788U,
    (uint64_t)0xbd195f868fbdd6c4U, (uint64_t)0xdb96f5b00a51d3f7U, (uint64_t)0xe1385c8a9b507feaU,
    (uint64_t)0x878e27813ee7310U, (uint64_t)0x6d7d8b12aea7e096U, (uint64_t)0x54978ad11e2f5ccaU,
    (uint64_t)0x49fffd6c3c4d07d4U, (uint64_t)0x703638f71fab7a5dU, (uint64_t)0xbed6e367fcc73960U,
    (uint64_t)0x215e161835a61d75U, (uint64_t)0xe52288a5e87a660bU, (uint64_t)0xf1d127ee3c802cb5U,
    (uint64_t)0xccde3c6aafc46044U, (uint64_t)0xdc11c08ef14cff32U, (uint64_t)0x29216f9ceca46668U,
    (uint64_t)0x22e584a3b2891c5eU, (uint64_t)0xe6deecd7810f6d87U, (uint64_t)0x6aff4b94a55659a3U,
    (uint64_t)0x12b59bb6d2e9f876U, (uint64_t)0x27ed01943aa02eabU, (uint64_t)0x8d6d420841f57075U,
    (uint64_t)0xe7b47285ef60a461U
  };

static const
uint64_t
points_radix_16_p384[192U] =
  {
    (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U,
    (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U, (uint64_t)0x0U,
    (uint64_t)0x32f2345cb5536b82U, (uint64_t)0x33ba95da2f7d6018U, (uint64_t)0xf2cd7729b1c03094U,
    (uint64_t)0x3159972fc3a90663U, (uint64_t)0x5827e6777fec9ce6U, (uint64_t)0x1af1e42821b04e1bU,
    (uint64_t)0xbbacc6d281184b31U, (uint64_t)0x5a08d98b36984428U, (uint64_t)0x73ba86bb86816030U,
    (uint64_t)0xe77b3c32da8c0cacU, (uint64_t)0x594336a7bc787585U, (uint64_t)0x7d25d16cde0af6c9U,
    (uint64_t)0xf1540d582ba14b3eU, (uint64_t)0x2e3457f23145b756U, (uint64_t)0x3fe78dcc087cfd43U,
    (uint64_t)0x281a423b111add53U, (uint64_t)0xbd34e442a5114f1cU, (uint64_t)0x3b519f3bffa3978dU,
    (uint64_t)0xb88dcc2161eb298aU, (uint64_t)0x61a90c2284e4289fU, (uint64_t)0x2c1a11d9238a73e1U,
    (uint64_t)0x5bee7ef92b222947U, (uint64_t)0x5cdb1c54277a3dc4U, (uint64_t)0x4e0243249bf36faeU,
    (uint64_t)0x4ee989be21361f68U, (uint64_t)0xafd40863847e1ecU, (uint64_t)0x2c512f43cd83f0ffU,
    (uint64_t)0xe48b4b50ed78fcc3U, (uint64_t)0x9541b91d4a92a8a5U, (uint64_t)0xfc09b8fb23ad6b1dU,
    (uint64_t)0xf10aa9975383b952U, (uint64_t)0xde9ab5738926a227U, (uint64_t)0x1f2ee4602710dc9eU,
    (uint64_t)0x8ba5023a9baeb840U, (uint64_t)0x237652a714d6dd45U, (uint64_t)0x462295d6123091d3U,
    (uint64_t)0xcab20eb810602defU, (uint64_t)0x8c395f33a87dd002U, (uint64_t)0x2fec596c5924beacU,
    (uint64_t)0x682b74489f1cf1e5U, (uint64_t)0x490bd9a2564c7a1aU, (uint64_t)0xe97a69779470060dU,
    (uint64_t)0xa2fd0fe85652626U, (uint64_t)0xe6da1173a40f9c1bU, (uint64_t)0x551f5e01228d56d1U,
    (uint64_t)0xe3e4e92afae58eb9U, (uint64_t)0xe84baf3a410bc2a9U, (uint64_t)0x38e40f38ce54b806U,
    (uint64_t)0x575a03d904682c6U, (uint64_t)0x3b1c513a911da1ecU, (uint64_t)0x49244a4f32b54168U,
    (uint64_t)0x5fd53f7cff693ebbU, (uint64_t)0x92d0bb818421982dU, (uint64_t)0x23cb51b8f5e404c0U,
    (uint64_t)0xe0a4c79de35bdc02U, (uint64_t)0x42d14e31fad23659U, (uint64_t)0x6b0b27c04f9f727eU,
    (uint64_t)0x7452f7a9b46ead0fU, (uint64_t)0x733ea8f242b7beafU, (uint64_t)0xfb39049721dbccc5U,
    (uint64_t)0x78bb9234f4efc52aU, (uint64_t)0xb56de919acfc6e2eU, (uint64_t)0x54feff0dea1c5ac8U,
    (uint64_t)0xf7f299a34c38d68dU, (uint64_t)0xa93c60d72804559fU, (uint64_t)0x77fab5c23575c358U,
    (uint64_t)0x5efe3510a7dc82ffU, (uint64_t)0x46c8fb1ee3434f87U, (uint64_t)0x876eed877fc1935dU,
    (uint64_t)0xb15f5e53c659cefcU, (uint64_t)0x606d48b09f2bccacU, (uint64_t)0xf22b90835d568517U,
    (uint64_t)0x4f57743cf3bbac55U, (uint64_t)0x4f9f2fe49f19163cU, (uint64_t)0x6bdfec70bbccb8afU,
    (uint64_t)0xa651335f997c464dU, (uint64_t)0x8f36ca3ea1f36e3dU, (uint64_t)0x952f13f0b537981aU,
    (uint64_t)0x104dcf1b8ee3d83U, (uint64_t)0x8aaea513ca0e5d27U, (uint64_t)0x1b2cd544ccda849eU,
    (uint64_t)0xe33a5040a6289feU, (uint64_t)0xce9de30ce002e4d0U, (uint64_t)0x14c32c89a73fd5e4U,
    (uint64_t)0xf090393c563e511U, (uint64_t)0x5d8fa7fb0ec9bbe6U, (uint64_t)0xe14f207dc35fafc4U,
    (uint64_t)0x4b69913b7770786U, (uint64_t)0xe34d1b9807020105U, (uint64_t)0xd7903931ccb65bbbU,
    (uint64_t)0x3ab44699c02a01a9U, (uint64_t)0x13d57fc62b0f2ea5U, (uint64_t)0xc3d135b66a95a394U,
    (uint64_t)0x4d688cce33b6be17U, (uint64_t)0xbe8737a518b6672fU, (uint64_t)0x726e41af1eb169c0U,
    (uint64_t)0x41e3b3b2fe071c07U, (uint64_t)0xdce07b75aa81d5dU, (uint64_t)0x15bed0d8277456ebU,
    (uint64_t)0x859db561a9bc0549U, (uint64_t)0x2ad498c4f890452dU, (uint64_t)0x10f2e86e0016a959U,
    (uint64_t)0x7519a47788194f3eU, (uint64_t)0xea6411ae90c18dbfU, (uint64_t)0xd510fed966098490U,
    (uint64_t)0xbc8209e3702df180U, (uint64_t)0xa12cbebc3e867526U, (uint64_t)0xd8b1128d8c00435dU,
    (uint64_t)0x49b697ef353ba3b1U, (uint64_t)0xbb54d2dbd6337dc9U, (uint64_t)0xf48e5c8f3650059cU,
    (uint64_t)0xe2b84c30b1a6d015U, (uint64_t)0x6881c5bca729c88aU, (uint64_t)0x2c80d8fd0ff92862U,
    (uint64_t)0x980fd9f699f80d77U, (uint64_t)0x4e170e65491f0011U, (uint64_t)0xdc39f58060a114d8U,
    (uint64_t)0x3e7ae1d658c0cd11U, (uint64_t)0x58a4abc6363ed354U, (uint64_t)0x33bce3bfde927b1bU,
    (uint64_t)0x7bde77c8369a96f4U, (uint64_t)0xad5993213577c683U, (uint64_t)0x84029d386008bc1fU,
    (uint64_t)0xf43fbc907cd9ea43U, (uint64_t)0x79bee143a07c79fcU, (uint64_t)0xfb21145d864cf408U,
    (uint64_t)0x5c980d203d789624U, (uint64_t)0x56d8efff9e4100ffU, (uint64_t)0xd212b18ba6da272bU,
    (uint64_t)0x35ee5bf1ba5cc6fU, (uint64_t)0x6ccb4f5ddc611c25U, (uint64_t)0x597bc89d74c6b1e1U,
    (uint64_t)0x587f56751011395bU, (uint64_t)0x7dbfba72b6d7edc9U, (uint64_t)0x96bf46bbd4bf0e99U,
    (uint64_t)0x77c9edabdc002fe0U, (uint64_t)0x21bd69abe9421c26U, (uint64_t)0x9de64f0b69c7dea9U,
    (uint64_t)0xcac40052cd7ab9fdU, (uint64_t)0xe3288f7d04655922U, (uint64_t)0x28d68b3bbb9a5f1cU,
    (uint64_t)0x7988bc2bdfe219b4U, (uint64_t)0xbbe3020d9eb46c29U, (uint64_t)0x6b81bbb979c673d7U,
    (uint64_t)0x8860adb3cf4aa41U, (uint64_t)0xaca9865403f1fb16U, (uint64_t)0xaee8454ec4f735a2U,
    (uint64_t)0xf2b875cd172e48f1U, (uint64_t)0x989a2846aed5c186U, (uint64_t)0x4907d727452e53e3U,
    (uint64_t)0xeec235cc38d73f5cU, (uint64_t)0xdd072b3a970422a2U, (uint64_t)0xc72d3adc399428f2U,
    (uint64_t)0x273501e954467443U, (uint64_t)0x120a7e861eb2319bU, (uint64_t)0xe3d4ddf9d3e69a3aU,
    (uint64_t)0x66ae2a548bc58d5eU, (uint64_t)0x412abebd62151597U, (uint64_t)0xd295fe4b80e00d9fU,
    (uint64_t)0x5db83d9f8bec48c0U, (uint64_t)0x330869a025cc0464U, (uint64_t)0xf3a45cc28e5fa579U,
    (uint64_t)0xb68395811ed3f011U, (uint64_t)0x6abe3da17b5b49d2U, (uint64_t)0x52df9a125384e282U,
    (uint64_t)0xdbe01aa7dbefcf5aU, (uint64_t)0x659954ee1ddfc5c3U, (uint64_t)0x4e958f32b1188c4eU,
    (uint64_t)0x2797876f470b54c5U, (uint64_t)0x4c6a43a656cf0b9cU, (uint64_t)0xeebca5ad676ed03bU,
    (uint64_t)0xae9208e7f7df959cU, (uint64_t)0xd69f061b3079e553U, (uint64_t)0xb81dba28e358689bU,
    (uint64_t)0x9b04ff9bdbe5cb49U, (uint64_t)0x3b03c307686324eeU, (uint64_t)0xe867901e57c05305U,
    (uint64_t)0xaec776b3efdf9a57U, (uint64_t)0x2efb6e881128ec96U, (uint64_t)0xd86d8452f015fd7bU
  };

static void
getPointPrecomputedTable_(
  Spec_ECC_Curves_curve c,
  uint32_t k,
  uint64_t *precomputedTable,
  uint64_t bits,
  uint64_t *r
)
{
  uint64_t mask = FStar_UInt64_eq_mask(bits, (uint64_t)k);
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint32_t pointLen = k * (sw * (uint32_t)3U);
  uint32_t coordLen;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        coordLen = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        coordLen = (uint32_t)6U;
        break;
      }
    default:
      {
        coordLen = (uint32_t)4U;
      }
  }
  uint64_t *lut_cmb = precomputedTable + pointLen;
  uint64_t *lut_cmb_x = lut_cmb;
  uint64_t *lut_cmb_y = lut_cmb + coordLen;
  uint64_t *lut_cmb_z = lut_cmb + (uint32_t)2U * coordLen;
  uint64_t *rX = r;
  uint64_t *rY = r + coordLen;
  uint64_t *rZ = r + (uint32_t)2U * coordLen;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(rX, lut_cmb_x, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(rX, lut_cmb_x, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(rY, lut_cmb_y, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(rY, lut_cmb_y, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(rZ, lut_cmb_z, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(rZ, lut_cmb_z, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
getPointPrecomputedTable_1(
  Spec_ECC_Curves_curve c,
  uint64_t *precomputedTable,
  uint64_t bits,
  uint64_t *r
)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    getPointPrecomputedTable_(c, i, precomputedTable, bits, r);
  }
}

static void
getPointPrecomputedTable_p256(
  void *scalar,
  uint64_t *precomputedTable,
  uint32_t i,
  uint64_t *pointToAdd
)
{
  uint32_t bit = computeBit(Spec_ECC_Curves_P256, i);
  uint64_t
  bit0 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
    * (uint32_t)8U
    - (uint32_t)1U
    - bit / (uint32_t)8U]
    >> bit % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)3U;
  uint64_t
  bit1 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
    * (uint32_t)8U
    - (uint32_t)1U
    - (bit - (uint32_t)1U) / (uint32_t)8U]
    >> (bit - (uint32_t)1U) % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)2U;
  uint64_t
  bit2 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
    * (uint32_t)8U
    - (uint32_t)1U
    - (bit - (uint32_t)2U) / (uint32_t)8U]
    >> (bit - (uint32_t)2U) % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)1U;
  uint64_t
  bit3 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
    * (uint32_t)8U
    - (uint32_t)1U
    - (bit - (uint32_t)3U) / (uint32_t)8U]
    >> (bit - (uint32_t)3U) % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)0U;
  uint64_t bits = (bit0 ^ bit1) ^ (bit2 ^ bit3);
  getPointPrecomputedTable_1(Spec_ECC_Curves_P256, precomputedTable, bits, pointToAdd);
}

static void
getPointPrecomputedTable_p384(
  void *scalar,
  uint64_t *precomputedTable,
  uint32_t i,
  uint64_t *pointToAdd
)
{
  uint32_t bit = computeBit(Spec_ECC_Curves_P384, i);
  uint64_t
  bit0 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
    * (uint32_t)8U
    - (uint32_t)1U
    - bit / (uint32_t)8U]
    >> bit % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)3U;
  uint64_t
  bit1 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
    * (uint32_t)8U
    - (uint32_t)1U
    - (bit - (uint32_t)1U) / (uint32_t)8U]
    >> (bit - (uint32_t)1U) % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)2U;
  uint64_t
  bit2 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
    * (uint32_t)8U
    - (uint32_t)1U
    - (bit - (uint32_t)2U) / (uint32_t)8U]
    >> (bit - (uint32_t)2U) % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)1U;
  uint64_t
  bit3 =
    (uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
    * (uint32_t)8U
    - (uint32_t)1U
    - (bit - (uint32_t)3U) / (uint32_t)8U]
    >> (bit - (uint32_t)3U) % (uint32_t)8U
    & (uint8_t)1U)
    << (uint32_t)0U;
  uint64_t bits = (bit0 ^ bit1) ^ (bit2 ^ bit3);
  getPointPrecomputedTable_1(Spec_ECC_Curves_P384, precomputedTable, bits, pointToAdd);
}

static void
getPointPrecomputedTable(
  Spec_ECC_Curves_curve c,
  void *scalar,
  uint64_t *precomputedTable,
  uint32_t i,
  uint64_t *pointToAdd
)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        getPointPrecomputedTable_p256(scalar, precomputedTable, i, pointToAdd);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        getPointPrecomputedTable_p384(scalar, precomputedTable, i, pointToAdd);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t *getPointTable_buffer(Spec_ECC_Curves_curve c, uint64_t *table, uint32_t i)
{
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint32_t pointLen = sw * (uint32_t)3U;
  return table + i * pointLen;
}

static void
generatePrecomputedTable_step(
  Spec_ECC_Curves_curve c,
  uint64_t *table,
  uint32_t i,
  uint64_t *tempBuffer
)
{
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint32_t pointLen = sw * (uint32_t)3U;
  uint64_t *point1 = getPointTable_buffer(c, table, (uint32_t)1U);
  uint64_t *point_n = getPointTable_buffer(c, table, i);
  uint64_t *point_2n = getPointTable_buffer(c, table, (uint32_t)2U * i);
  uint64_t *point_2n_1 = getPointTable_buffer(c, table, (uint32_t)2U * i + (uint32_t)1U);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        point_double_p256(point_n, point_2n, tempBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        point_double_p384(point_n, point_2n, tempBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        point_add_p256(point_2n, point1, point_2n_1, tempBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        point_add_p384(point_2n, point1, point_2n_1, tempBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
generatePrecomputedTable_loop(Spec_ECC_Curves_curve c, uint64_t *table, uint64_t *tempBuffer)
{
  {
    generatePrecomputedTable_step(c, table, (uint32_t)1U, tempBuffer);
  }
  {
    generatePrecomputedTable_step(c, table, (uint32_t)2U, tempBuffer);
  }
  {
    generatePrecomputedTable_step(c, table, (uint32_t)3U, tempBuffer);
  }
  {
    generatePrecomputedTable_step(c, table, (uint32_t)4U, tempBuffer);
  }
  {
    generatePrecomputedTable_step(c, table, (uint32_t)5U, tempBuffer);
  }
  {
    generatePrecomputedTable_step(c, table, (uint32_t)6U, tempBuffer);
  }
  {
    generatePrecomputedTable_step(c, table, (uint32_t)7U, tempBuffer);
  }
}

static inline void
generatePrecomputedTable(
  Spec_ECC_Curves_curve c,
  uint64_t *table,
  uint64_t *publicKey,
  uint64_t *tempBuffer
)
{
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint32_t pointLen = sw * (uint32_t)3U;
  uint64_t *point0 = table;
  uint64_t *point1 = table + pointLen;
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint64_t *x = point0;
  uint64_t *y = point0 + len;
  uint64_t *z = point0 + (uint32_t)2U * len;
  uint32_t len1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len1 = (uint32_t)6U;
        break;
      }
    default:
      {
        len1 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len10;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len10 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len10 = (uint32_t)6U;
        break;
      }
    default:
      {
        len10 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len11;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len11 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len11 = (uint32_t)6U;
        break;
      }
    default:
      {
        len11 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    z[i] = (uint64_t)0U;
  }
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  memcpy(point1, publicKey, sw0 * (uint32_t)3U * sizeof (uint64_t));
  generatePrecomputedTable_loop(c, table, tempBuffer);
}

static uint32_t getLenWnaf(Spec_ECC_Curves_curve c)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return (uint32_t)51U;
      }
    case Spec_ECC_Curves_P384:
      {
        return (uint32_t)76U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void scalar_rwnaf_step_compute_di(uint64_t w, uint64_t *out, uint64_t *r, uint32_t i)
{
  uint64_t c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, w, (uint64_t)32U, r);
  uint64_t r0 = r[0U];
  uint64_t r2 = (uint64_t)0U - r0;
  uint64_t cAsFlag = ~FStar_UInt64_eq_mask(c1, (uint64_t)0U);
  uint64_t r3 = (r2 & cAsFlag) | (r0 & ~cAsFlag);
  out[(uint32_t)2U * i] = r3;
  out[(uint32_t)2U * i + (uint32_t)1U] = cAsFlag;
}

static uint64_t
scalar_rwnaf_step_compute_window_(
  Spec_ECC_Curves_curve c,
  uint64_t wStart,
  void *scalar,
  uint32_t k
)
{
  uint32_t i = ((uint32_t)1U + k) * (uint32_t)5U;
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  uint64_t
  w0 =
    wStart
    +
      ((uint64_t)(((uint8_t *)scalar)[sw0
      * (uint32_t)8U
      - (uint32_t)1U
      - (i + (uint32_t)1U) / (uint32_t)8U]
      >> (i + (uint32_t)1U) % (uint32_t)8U
      & (uint8_t)1U)
      << (uint32_t)1U);
  uint32_t sw1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw1 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw1 = (uint32_t)4U;
      }
  }
  uint64_t
  w01 =
    w0
    +
      ((uint64_t)(((uint8_t *)scalar)[sw1
      * (uint32_t)8U
      - (uint32_t)1U
      - (i + (uint32_t)2U) / (uint32_t)8U]
      >> (i + (uint32_t)2U) % (uint32_t)8U
      & (uint8_t)1U)
      << (uint32_t)2U);
  uint32_t sw2;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw2 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw2 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw2 = (uint32_t)4U;
      }
  }
  uint64_t
  w02 =
    w01
    +
      ((uint64_t)(((uint8_t *)scalar)[sw2
      * (uint32_t)8U
      - (uint32_t)1U
      - (i + (uint32_t)3U) / (uint32_t)8U]
      >> (i + (uint32_t)3U) % (uint32_t)8U
      & (uint8_t)1U)
      << (uint32_t)3U);
  uint32_t sw3;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw3 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw3 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw3 = (uint32_t)4U;
      }
  }
  uint64_t
  w03 =
    w02
    +
      ((uint64_t)(((uint8_t *)scalar)[sw3
      * (uint32_t)8U
      - (uint32_t)1U
      - (i + (uint32_t)4U) / (uint32_t)8U]
      >> (i + (uint32_t)4U) % (uint32_t)8U
      & (uint8_t)1U)
      << (uint32_t)4U);
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint64_t
  w04 =
    w03
    +
      ((uint64_t)(((uint8_t *)scalar)[sw
      * (uint32_t)8U
      - (uint32_t)1U
      - (i + (uint32_t)5U) / (uint32_t)8U]
      >> (i + (uint32_t)5U) % (uint32_t)8U
      & (uint8_t)1U)
      << (uint32_t)5U);
  return w04;
}

static void
scalar_rwnaf_loop(
  Spec_ECC_Curves_curve c,
  uint64_t *out,
  void *scalar,
  uint64_t mask,
  uint64_t *window
)
{
  uint64_t r = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < getLenWnaf(c) - (uint32_t)1U; i++)
  {
    uint64_t wVar = window[0U];
    uint64_t wMask = wVar & mask;
    scalar_rwnaf_step_compute_di(wMask, out, &r, i);
    uint64_t d = wMask - (uint64_t)32U;
    uint64_t wStart = (wVar - d) >> (uint32_t)5U;
    uint64_t w0 = scalar_rwnaf_step_compute_window_(c, wStart, scalar, i);
    window[0U] = w0;
  }
}

static uint64_t scalar_rwnaf_tail__(Spec_ECC_Curves_curve c, void *scalar, uint64_t wStart)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return wStart;
      }
    case Spec_ECC_Curves_P384:
      {
        uint32_t i = getLenWnaf(Spec_ECC_Curves_P384) * (uint32_t)5U;
        uint64_t
        w0 =
          wStart
          +
            ((uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
            * (uint32_t)8U
            - (uint32_t)1U
            - (i + (uint32_t)1U) / (uint32_t)8U]
            >> (i + (uint32_t)1U) % (uint32_t)8U
            & (uint8_t)1U)
            << (uint32_t)1U);
        uint64_t
        w01 =
          w0
          +
            ((uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
            * (uint32_t)8U
            - (uint32_t)1U
            - (i + (uint32_t)2U) / (uint32_t)8U]
            >> (i + (uint32_t)2U) % (uint32_t)8U
            & (uint8_t)1U)
            << (uint32_t)2U);
        return
          w01
          +
            ((uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
            * (uint32_t)8U
            - (uint32_t)1U
            - (i + (uint32_t)3U) / (uint32_t)8U]
            >> (i + (uint32_t)3U) % (uint32_t)8U
            & (uint8_t)1U)
            << (uint32_t)3U);
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t
scalar_rwnaf_tail_(Spec_ECC_Curves_curve c, void *scalar, uint64_t mask, uint64_t wVar)
{
  uint64_t d = mask - (uint64_t)32U;
  uint64_t wStart = (wVar - d) >> (uint32_t)5U;
  return scalar_rwnaf_tail__(c, scalar, wStart);
}

static uint64_t
scalar_rwnaf_tail(Spec_ECC_Curves_curve c, void *scalar, uint64_t mask, uint64_t wVar)
{
  uint64_t wLast = scalar_rwnaf_tail_(c, scalar, mask, wVar);
  return wLast;
}

extern void
Hacl_Impl_EC_ScalarMultiplication_WNAF_getPointPrecomputed_P256(
  uint32_t index,
  uint64_t *result
);

extern void
Hacl_Impl_EC_ScalarMultiplication_WNAF_getPointPrecomputed_P384(
  uint32_t index,
  uint64_t *result
);

static void getPointPrecomputed(Spec_ECC_Curves_curve c, uint32_t index, uint64_t *result)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        Hacl_Impl_EC_ScalarMultiplication_WNAF_getPointPrecomputed_P256(index, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        Hacl_Impl_EC_ScalarMultiplication_WNAF_getPointPrecomputed_P384(index, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
copy_point_conditional_affine(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  uint64_t mask
)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint64_t *pX = p;
  uint64_t *pY = p + len;
  uint64_t *pointToAddX = result;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint64_t *pointToAddY = result + sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(pointToAddX, pX, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(pointToAddX, pX, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(pointToAddY, pY, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(pointToAddY, pY, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
loopK_step(
  Spec_ECC_Curves_curve c,
  uint64_t d,
  uint64_t *result,
  uint32_t j,
  uint32_t k,
  uint64_t *tempPoint
)
{
  uint64_t mask = FStar_UInt64_eq_mask(d, (uint64_t)k);
  getPointPrecomputed(c, j * (uint32_t)16U + k, tempPoint);
  copy_point_conditional_affine(c, result, tempPoint, mask);
}

static void
loopK_loop(
  Spec_ECC_Curves_curve c,
  uint64_t d,
  uint64_t *result,
  uint32_t j,
  uint64_t *tempPoint
)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    loopK_step(c, d, result, j, i, tempPoint);
  }
}

static void loopK(Spec_ECC_Curves_curve c, uint64_t d, uint64_t *result, uint32_t j)
{
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), sw * (uint32_t)2U);
  uint64_t tempPoint[sw * (uint32_t)2U];
  memset(tempPoint, 0U, sw * (uint32_t)2U * sizeof (uint64_t));
  loopK_loop(c, d, result, j, tempPoint);
}

static void point_affine_neg(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *result)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint64_t *pX = p;
  uint64_t *pY = p + len;
  uint64_t *rX = result;
  uint64_t *rY = result + len;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  memcpy(rX, pX, sw * sizeof (uint64_t));
  felem_sub_zero(c, pY, rY);
}

static void
point_neg_conditional(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *tempBuffer,
  uint64_t mask
)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint64_t *temp = tempBuffer;
  uint64_t *pY = p + len;
  felem_sub_zero(c, pY, temp);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(pY, temp, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(pY, temp, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t conditional_subtraction_compute_mask(Spec_ECC_Curves_curve c, void *scalar)
{
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint32_t len = sw * (uint32_t)8U - (uint32_t)1U;
  uint8_t i0 = ((uint8_t *)scalar)[len];
  return ~((uint64_t)0U - (uint64_t)(i0 & (uint8_t)1U));
}

static void uploadBasePointAffine(Spec_ECC_Curves_curve c, uint64_t *p)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        p[0U] = (uint64_t)0x1fb38ab1388ad777U;
        p[1U] = (uint64_t)0x1dfee06615fa309dU;
        p[2U] = (uint64_t)0xfcac986c3afea4a7U;
        p[3U] = (uint64_t)0xdf65c2da29fb821aU;
        p[4U] = (uint64_t)0xeff44e23f63f8f6dU;
        p[5U] = (uint64_t)0xaa02cd3ed4b681a4U;
        p[6U] = (uint64_t)0xdd5fda3363818af8U;
        p[7U] = (uint64_t)0xfc53bc2629fbf0b3U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        p[0U] = (uint64_t)0x32f2345cb5536b82U;
        p[1U] = (uint64_t)0x33ba95da2f7d6018U;
        p[2U] = (uint64_t)0xf2cd7729b1c03094U;
        p[3U] = (uint64_t)0x3159972fc3a90663U;
        p[4U] = (uint64_t)0x5827e6777fec9ce6U;
        p[5U] = (uint64_t)0x1af1e42821b04e1bU;
        p[6U] = (uint64_t)0xbbacc6d281184b31U;
        p[7U] = (uint64_t)0x5a08d98b36984428U;
        p[8U] = (uint64_t)0x73ba86bb86816030U;
        p[9U] = (uint64_t)0xe77b3c32da8c0cacU;
        p[10U] = (uint64_t)0x594336a7bc787585U;
        p[11U] = (uint64_t)0x7d25d16cde0af6c9U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
uploadMinusBasePointAffine(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *tempBuffer)
{
  uint64_t *tempBasePoint = tempBuffer;
  uploadBasePointAffine(c, tempBasePoint);
  point_affine_neg(c, tempBasePoint, p);
}

static void
conditional_subtraction_upload_masked(
  Spec_ECC_Curves_curve c,
  void *scalar,
  uint64_t *tempPointJacobian,
  uint64_t *result
)
{
  uint64_t mask = conditional_subtraction_compute_mask(c, scalar);
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint64_t *p_x = tempPointJacobian;
  uint64_t *p_y = tempPointJacobian + len;
  uint64_t *p_z = tempPointJacobian + (uint32_t)2U * len;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len;
  uint64_t *r_z = result + (uint32_t)2U * len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(r_x, p_x, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(r_x, p_x, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(r_y, p_y, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(r_y, p_y, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        copy_conditional_p256_l(r_z, p_z, mask);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        copy_conditional_p384_l(r_z, p_z, mask);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
conditional_substraction_(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  void *scalar,
  uint64_t *tempBuffer,
  uint64_t *precompNegativePoint,
  uint64_t *tempPointJacobian
)
{
  uploadMinusBasePointAffine(c, precompNegativePoint, tempBuffer);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        point_add_mixed_p256(p, precompNegativePoint, tempPointJacobian, tempBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        point_add_mixed_p384(p, precompNegativePoint, tempPointJacobian, tempBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  conditional_subtraction_upload_masked(c, scalar, tempPointJacobian, result);
}

static void
conditional_substraction(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), sw * (uint32_t)3U);
  uint64_t tempPointJacobian[sw * (uint32_t)3U];
  memset(tempPointJacobian, 0U, sw * (uint32_t)3U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t precompNegativePoint[(uint32_t)2U * len];
  memset(precompNegativePoint, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  conditional_substraction_(c,
    result,
    p,
    scalar,
    tempBuffer,
    precompNegativePoint,
    tempPointJacobian);
}

static uint64_t compute_index_rwnaf(uint64_t *rnaf, uint32_t k)
{
  uint64_t d0 = rnaf[(uint32_t)2U * k];
  return (d0 - (uint64_t)1U) >> (uint32_t)1U;
}

static void
point_add_complete_last_step_main_p256(uint64_t *rnaf, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t temp3[12U] = { 0U };
  uint64_t d = compute_index_rwnaf(rnaf, (uint32_t)0U);
  uint64_t is_neg = rnaf[1U];
  uint64_t *temp2 = temp3;
  loopK(Spec_ECC_Curves_P256, d, temp2, (uint32_t)0U);
  point_neg_conditional(Spec_ECC_Curves_P256, temp2, tempBuffer, is_neg);
  uint64_t *pX = temp3 + (uint32_t)8U;
  pX[0U] = (uint64_t)1U;
  uint32_t len0 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len0; i++)
  {
    pX[i] = (uint64_t)0U;
  }
  uint64_t result_point_double[12U] = { 0U };
  uint32_t len2 = (uint32_t)4U;
  uint64_t *sq_z1 = tempBuffer;
  uint64_t *tr_z1 = tempBuffer + len2;
  uint64_t *sq_z2 = tempBuffer + (uint32_t)2U * len2;
  uint64_t *tr_z2 = tempBuffer + (uint32_t)3U * len2;
  uint64_t *x1 = temp3;
  uint64_t *y1 = temp3 + len2;
  uint64_t *z1 = temp3 + (uint32_t)2U * len2;
  uint64_t *x2 = result;
  uint64_t *y2 = result + len2;
  uint64_t *z2 = result + (uint32_t)2U * len2;
  montgomery_square_buffer_dh_p256(z1, sq_z1);
  montgomery_square_buffer_dh_p256(z2, sq_z2);
  montgomery_multiplication_buffer_dh_p256(sq_z1, z1, tr_z1);
  montgomery_multiplication_buffer_dh_p256(sq_z2, z2, tr_z2);
  montgomery_multiplication_buffer_dh_p256(sq_z1, x2, sq_z1);
  montgomery_multiplication_buffer_dh_p256(sq_z2, x1, sq_z2);
  montgomery_multiplication_buffer_dh_p256(tr_z1, y2, tr_z1);
  montgomery_multiplication_buffer_dh_p256(tr_z2, y1, tr_z2);
  uint64_t tmp1 = (uint64_t)0U;
  tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    uint64_t a_i = sq_z1[i];
    uint64_t b_i = sq_z2[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t equalX = tmp1;
  uint64_t tmp2 = (uint64_t)0U;
  tmp2 = (uint64_t)18446744073709551615U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t a_i = tr_z1[i];
    uint64_t b_i = tr_z2[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp2;
    tmp2 = r_i & tmp0;
  }
  uint64_t equalY = tmp2;
  uint64_t equal = equalX & equalY;
  uint32_t len = (uint32_t)4U;
  uint64_t *pY = temp3 + len;
  uint64_t *pZ = temp3 + (uint32_t)2U * len;
  uint64_t *x3 = result_point_double;
  uint64_t *y3 = result_point_double + len;
  uint64_t *z3 = result_point_double + (uint32_t)2U * len;
  uint64_t *delta = tempBuffer;
  uint64_t *gamma = tempBuffer + len;
  uint64_t *beta = tempBuffer + (uint32_t)2U * len;
  uint64_t *alpha = tempBuffer + (uint32_t)3U * len;
  uint64_t *fourBeta = tempBuffer + (uint32_t)4U * len;
  uint64_t *eightBeta = tempBuffer + (uint32_t)5U * len;
  uint64_t *eightGamma = tempBuffer + (uint32_t)6U * len;
  uint64_t *tmp = tempBuffer + (uint32_t)7U * len;
  uint32_t coordinateLen = (uint32_t)4U;
  uint64_t *pX1 = temp3;
  uint64_t *pY1 = temp3 + coordinateLen;
  uint64_t *pZ1 = temp3 + (uint32_t)2U * coordinateLen;
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
  point_add_p256(temp3, result, result, tempBuffer);
  uint32_t len3 = (uint32_t)4U;
  uint64_t *p_x = result_point_double;
  uint64_t *p_y = result_point_double + len3;
  uint64_t *p_z = result_point_double + (uint32_t)2U * len3;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len3;
  uint64_t *r_z = result + (uint32_t)2U * len3;
  copy_conditional_p256_l(r_x, p_x, equal);
  copy_conditional_p256_l(r_y, p_y, equal);
  copy_conditional_p256_l(r_z, p_z, equal);
}

static void
point_add_complete_last_step_main_p384(uint64_t *rnaf, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t temp3[18U] = { 0U };
  uint64_t d = compute_index_rwnaf(rnaf, (uint32_t)0U);
  uint64_t is_neg = rnaf[1U];
  uint64_t *temp2 = temp3;
  loopK(Spec_ECC_Curves_P384, d, temp2, (uint32_t)0U);
  point_neg_conditional(Spec_ECC_Curves_P384, temp2, tempBuffer, is_neg);
  uint64_t *pX = temp3 + (uint32_t)12U;
  pX[0U] = (uint64_t)1U;
  uint32_t len0 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)1U; i < len0; i++)
  {
    pX[i] = (uint64_t)0U;
  }
  uint64_t result_point_double[18U] = { 0U };
  uint32_t len2 = (uint32_t)6U;
  uint64_t *sq_z1 = tempBuffer;
  uint64_t *tr_z1 = tempBuffer + len2;
  uint64_t *sq_z2 = tempBuffer + (uint32_t)2U * len2;
  uint64_t *tr_z2 = tempBuffer + (uint32_t)3U * len2;
  uint64_t *x1 = temp3;
  uint64_t *y1 = temp3 + len2;
  uint64_t *z1 = temp3 + (uint32_t)2U * len2;
  uint64_t *x2 = result;
  uint64_t *y2 = result + len2;
  uint64_t *z2 = result + (uint32_t)2U * len2;
  montgomery_square_buffer_dh_p384(z1, sq_z1);
  montgomery_square_buffer_dh_p384(z2, sq_z2);
  montgomery_multiplication_buffer_dh_p384(sq_z1, z1, tr_z1);
  montgomery_multiplication_buffer_dh_p384(sq_z2, z2, tr_z2);
  montgomery_multiplication_buffer_dh_p384(sq_z1, x2, sq_z1);
  montgomery_multiplication_buffer_dh_p384(sq_z2, x1, sq_z2);
  montgomery_multiplication_buffer_dh_p384(tr_z1, y2, tr_z1);
  montgomery_multiplication_buffer_dh_p384(tr_z2, y1, tr_z2);
  uint64_t tmp1 = (uint64_t)0U;
  tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len10 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    uint64_t a_i = sq_z1[i];
    uint64_t b_i = sq_z2[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t equalX = tmp1;
  uint64_t tmp2 = (uint64_t)0U;
  tmp2 = (uint64_t)18446744073709551615U;
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t a_i = tr_z1[i];
    uint64_t b_i = tr_z2[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp2;
    tmp2 = r_i & tmp0;
  }
  uint64_t equalY = tmp2;
  uint64_t equal = equalX & equalY;
  uint32_t len = (uint32_t)6U;
  uint64_t *pY = temp3 + len;
  uint64_t *pZ = temp3 + (uint32_t)2U * len;
  uint64_t *x3 = result_point_double;
  uint64_t *y3 = result_point_double + len;
  uint64_t *z3 = result_point_double + (uint32_t)2U * len;
  uint64_t *delta = tempBuffer;
  uint64_t *gamma = tempBuffer + len;
  uint64_t *beta = tempBuffer + (uint32_t)2U * len;
  uint64_t *alpha = tempBuffer + (uint32_t)3U * len;
  uint64_t *fourBeta = tempBuffer + (uint32_t)4U * len;
  uint64_t *eightBeta = tempBuffer + (uint32_t)5U * len;
  uint64_t *eightGamma = tempBuffer + (uint32_t)6U * len;
  uint64_t *tmp = tempBuffer + (uint32_t)7U * len;
  uint32_t coordinateLen = (uint32_t)6U;
  uint64_t *pX1 = temp3;
  uint64_t *pY1 = temp3 + coordinateLen;
  uint64_t *pZ1 = temp3 + (uint32_t)2U * coordinateLen;
  uint64_t *a0 = tmp;
  uint64_t *a1 = tmp + coordinateLen;
  uint64_t *alpha0 = tmp + (uint32_t)2U * coordinateLen;
  montgomery_square_buffer_dh_p384(pZ1, delta);
  montgomery_square_buffer_dh_p384(pY1, gamma);
  montgomery_multiplication_buffer_dh_p384(pX1, gamma, beta);
  felem_sub_p384(pX1, delta, a0);
  felem_add_p384(pX1, delta, a1);
  montgomery_multiplication_buffer_dh_p384(a0, a1, alpha0);
  felem_add_p384(alpha0, alpha0, alpha);
  felem_add_p384(alpha0, alpha, alpha);
  montgomery_square_buffer_dh_p384(alpha, x3);
  felem_add_p384(beta, beta, fourBeta);
  felem_add_p384(fourBeta, fourBeta, fourBeta);
  felem_add_p384(fourBeta, fourBeta, eightBeta);
  felem_sub_p384(x3, eightBeta, x3);
  felem_add_p384(pY, pZ, z3);
  montgomery_square_buffer_dh_p384(z3, z3);
  felem_sub_p384(z3, gamma, z3);
  felem_sub_p384(z3, delta, z3);
  felem_sub_p384(fourBeta, x3, y3);
  montgomery_multiplication_buffer_dh_p384(alpha, y3, y3);
  montgomery_square_buffer_dh_p384(gamma, gamma);
  felem_add_p384(gamma, gamma, eightGamma);
  felem_add_p384(eightGamma, eightGamma, eightGamma);
  felem_add_p384(eightGamma, eightGamma, eightGamma);
  felem_sub_p384(y3, eightGamma, y3);
  point_add_p384(temp3, result, result, tempBuffer);
  uint32_t len3 = (uint32_t)6U;
  uint64_t *p_x = result_point_double;
  uint64_t *p_y = result_point_double + len3;
  uint64_t *p_z = result_point_double + (uint32_t)2U * len3;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len3;
  uint64_t *r_z = result + (uint32_t)2U * len3;
  copy_conditional_p384_l(r_x, p_x, equal);
  copy_conditional_p384_l(r_y, p_y, equal);
  copy_conditional_p384_l(r_z, p_z, equal);
}

static void
scalar_multiplication_cmb_p256(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t lenWnaf = getLenWnaf(Spec_ECC_Curves_P256) + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * lenWnaf);
  uint64_t rnaf[(uint32_t)2U * lenWnaf];
  memset(rnaf, 0U, (uint32_t)2U * lenWnaf * sizeof (uint64_t));
  uint64_t temp[8U] = { 0U };
  uint32_t len = (uint32_t)4U;
  uint64_t *x = result;
  uint64_t *y = result + len;
  uint64_t *z = result + (uint32_t)2U * len;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    z[i] = (uint64_t)0U;
  }
  uint64_t mask = (uint64_t)63U;
  uint64_t in01 = (uint64_t)((uint8_t *)scalar)[(uint32_t)4U * (uint32_t)8U - (uint32_t)1U];
  uint64_t windowStartValue = (uint64_t)1U | (in01 & mask);
  uint64_t window = windowStartValue;
  uint64_t r = (uint64_t)0U;
  scalar_rwnaf_loop(Spec_ECC_Curves_P256, rnaf, scalar, mask, &window);
  uint64_t wVar = window;
  uint64_t wMask = wVar & mask;
  scalar_rwnaf_step_compute_di(wMask, rnaf, &r, getLenWnaf(Spec_ECC_Curves_P256) - (uint32_t)1U);
  uint64_t wLast = scalar_rwnaf_tail(Spec_ECC_Curves_P256, scalar, wMask, wVar);
  rnaf[(uint32_t)2U * getLenWnaf(Spec_ECC_Curves_P256)] = wLast;
  uint32_t lenWnaf1 = getLenWnaf(Spec_ECC_Curves_P256) + (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenWnaf1 - (uint32_t)1U; i++)
  {
    uint32_t j = getLenWnaf(Spec_ECC_Curves_P256) - i;
    uint64_t is_neg = rnaf[(uint32_t)2U * j + (uint32_t)1U];
    uint64_t d = compute_index_rwnaf(rnaf, j);
    loopK(Spec_ECC_Curves_P256, d, temp, j);
    point_neg_conditional(Spec_ECC_Curves_P256, temp, tempBuffer, is_neg);
    point_add_mixed_p256(result, temp, result, tempBuffer);
  }
  point_add_complete_last_step_main_p256(rnaf, result, tempBuffer);
  conditional_substraction(Spec_ECC_Curves_P256, result, result, scalar, tempBuffer);
}

static void
scalar_multiplication_cmb_p384(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t lenWnaf = getLenWnaf(Spec_ECC_Curves_P384) + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * lenWnaf);
  uint64_t rnaf[(uint32_t)2U * lenWnaf];
  memset(rnaf, 0U, (uint32_t)2U * lenWnaf * sizeof (uint64_t));
  uint64_t temp[12U] = { 0U };
  uint32_t len = (uint32_t)6U;
  uint64_t *x = result;
  uint64_t *y = result + len;
  uint64_t *z = result + (uint32_t)2U * len;
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len10 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    z[i] = (uint64_t)0U;
  }
  uint64_t mask = (uint64_t)63U;
  uint64_t in01 = (uint64_t)((uint8_t *)scalar)[(uint32_t)6U * (uint32_t)8U - (uint32_t)1U];
  uint64_t windowStartValue = (uint64_t)1U | (in01 & mask);
  uint64_t window = windowStartValue;
  uint64_t r = (uint64_t)0U;
  scalar_rwnaf_loop(Spec_ECC_Curves_P384, rnaf, scalar, mask, &window);
  uint64_t wVar = window;
  uint64_t wMask = wVar & mask;
  scalar_rwnaf_step_compute_di(wMask, rnaf, &r, getLenWnaf(Spec_ECC_Curves_P384) - (uint32_t)1U);
  uint64_t wLast = scalar_rwnaf_tail(Spec_ECC_Curves_P384, scalar, wMask, wVar);
  rnaf[(uint32_t)2U * getLenWnaf(Spec_ECC_Curves_P384)] = wLast;
  uint32_t lenWnaf1 = getLenWnaf(Spec_ECC_Curves_P384) + (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenWnaf1 - (uint32_t)1U; i++)
  {
    uint32_t j = getLenWnaf(Spec_ECC_Curves_P384) - i;
    uint64_t is_neg = rnaf[(uint32_t)2U * j + (uint32_t)1U];
    uint64_t d = compute_index_rwnaf(rnaf, j);
    loopK(Spec_ECC_Curves_P384, d, temp, j);
    point_neg_conditional(Spec_ECC_Curves_P384, temp, tempBuffer, is_neg);
    point_add_mixed_p384(result, temp, result, tempBuffer);
  }
  point_add_complete_last_step_main_p384(rnaf, result, tempBuffer);
  conditional_substraction(Spec_ECC_Curves_P384, result, result, scalar, tempBuffer);
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

static inline void
montgomery_ladderP384L(uint64_t *p, uint64_t *q, uint8_t *scalar, uint64_t *tempBuffer)
{
  uint32_t cycleLoop = (uint32_t)6U * (uint32_t)8U * (uint32_t)8U;
  for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
  {
    uint32_t bit0 = (uint32_t)6U * (uint32_t)8U * (uint32_t)8U - (uint32_t)1U - i0;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)6U
      * (uint32_t)8U
      - (uint32_t)1U
      - bit0 / (uint32_t)8U]
      >> bit0 % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len0 = (uint32_t)18U;
    for (uint32_t i = (uint32_t)0U; i < len0; i++)
    {
      uint64_t dummy = mask & (p[i] ^ q[i]);
      p[i] = p[i] ^ dummy;
      q[i] = q[i] ^ dummy;
    }
    point_add_p384(p, q, q, tempBuffer);
    point_double_p384(p, p, tempBuffer);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len = (uint32_t)18U;
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len10 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len11 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len12 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len13 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len14 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len15 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len16 / (uint32_t)4U; i8++)
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
  for (uint32_t i8 = (uint32_t)0U; i8 < len1 / (uint32_t)4U; i8++)
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

static inline void solinas_reduction_impl_p384(uint64_t *i, uint64_t *o)
{
  uint64_t tempBuffer[60U] = { 0U };
  uint64_t i0 = i[0U];
  uint64_t i1 = i[1U];
  uint64_t i2 = i[2U];
  uint64_t i3 = i[3U];
  uint64_t i4 = i[4U];
  uint64_t i5 = i[5U];
  uint64_t i6 = i[6U];
  uint64_t i7 = i[7U];
  uint64_t i8 = i[8U];
  uint64_t i9 = i[9U];
  uint64_t i10 = i[10U];
  uint64_t i11 = i[11U];
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
  uint32_t c16 = (uint32_t)i8;
  uint32_t c17 = (uint32_t)(i8 >> (uint32_t)32U);
  uint32_t c18 = (uint32_t)i9;
  uint32_t c19 = (uint32_t)(i9 >> (uint32_t)32U);
  uint32_t c20 = (uint32_t)i10;
  uint32_t c21 = (uint32_t)(i10 >> (uint32_t)32U);
  uint32_t c22 = (uint32_t)i11;
  uint32_t c23 = (uint32_t)(i11 >> (uint32_t)32U);
  uint64_t *t01 = tempBuffer;
  uint64_t *t110 = tempBuffer + (uint32_t)6U;
  uint64_t *t210 = tempBuffer + (uint32_t)12U;
  uint64_t *t310 = tempBuffer + (uint32_t)18U;
  uint64_t *t410 = tempBuffer + (uint32_t)24U;
  uint64_t *t510 = tempBuffer + (uint32_t)30U;
  uint64_t *t610 = tempBuffer + (uint32_t)36U;
  uint64_t *t710 = tempBuffer + (uint32_t)42U;
  uint64_t *t810 = tempBuffer + (uint32_t)48U;
  uint64_t *t910 = tempBuffer + (uint32_t)54U;
  uint64_t as_uint64_high0 = (uint64_t)c1;
  uint64_t as_uint64_high1 = as_uint64_high0 << (uint32_t)32U;
  uint64_t as_uint64_low0 = (uint64_t)c0;
  uint64_t a0 = as_uint64_low0 ^ as_uint64_high1;
  uint64_t as_uint64_high2 = (uint64_t)c3;
  uint64_t as_uint64_high10 = as_uint64_high2 << (uint32_t)32U;
  uint64_t as_uint64_low1 = (uint64_t)c2;
  uint64_t a1 = as_uint64_low1 ^ as_uint64_high10;
  uint64_t as_uint64_high3 = (uint64_t)c5;
  uint64_t as_uint64_high11 = as_uint64_high3 << (uint32_t)32U;
  uint64_t as_uint64_low2 = (uint64_t)c4;
  uint64_t a2 = as_uint64_low2 ^ as_uint64_high11;
  uint64_t as_uint64_high4 = (uint64_t)c7;
  uint64_t as_uint64_high12 = as_uint64_high4 << (uint32_t)32U;
  uint64_t as_uint64_low3 = (uint64_t)c6;
  uint64_t a3 = as_uint64_low3 ^ as_uint64_high12;
  uint64_t as_uint64_high5 = (uint64_t)c9;
  uint64_t as_uint64_high13 = as_uint64_high5 << (uint32_t)32U;
  uint64_t as_uint64_low4 = (uint64_t)c8;
  uint64_t a4 = as_uint64_low4 ^ as_uint64_high13;
  uint64_t as_uint64_high6 = (uint64_t)c11;
  uint64_t as_uint64_high14 = as_uint64_high6 << (uint32_t)32U;
  uint64_t as_uint64_low5 = (uint64_t)c10;
  uint64_t a5 = as_uint64_low5 ^ as_uint64_high14;
  t01[0U] = a0;
  t01[1U] = a1;
  t01[2U] = a2;
  t01[3U] = a3;
  t01[4U] = a4;
  t01[5U] = a5;
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer1[len];
  memset(tempBuffer1, 0U, len * sizeof (uint64_t));
  uint64_t
  p0[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len10 = (uint32_t)6U;
  uint64_t c24 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len10 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t01[(uint32_t)4U * i12];
    uint64_t t220 = p0[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i12;
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t12, t220, res_i0);
    uint64_t t120 = t01[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p0[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i12 + (uint32_t)1U;
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t120, t221, res_i1);
    uint64_t t121 = t01[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p0[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i12 + (uint32_t)2U;
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t121, t222, res_i2);
    uint64_t t122 = t01[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p0[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i12 + (uint32_t)3U;
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t122, t22, res_i);
  }
  for (uint32_t i12 = len10 / (uint32_t)4U * (uint32_t)4U; i12 < len10; i12++)
  {
    uint64_t t12 = t01[i12];
    uint64_t t22 = p0[i12];
    uint64_t *res_i = tempBuffer1 + i12;
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t12, t22, res_i);
  }
  uint64_t r = c24;
  uint64_t r0 = r;
  cmovznz4_p384(r0, tempBuffer1, t01, t01);
  uint64_t as_uint64_high7 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high15 = as_uint64_high7 << (uint32_t)32U;
  uint64_t as_uint64_low6 = (uint64_t)(uint32_t)0U;
  uint64_t b0 = as_uint64_low6 ^ as_uint64_high15;
  uint64_t as_uint64_high8 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high16 = as_uint64_high8 << (uint32_t)32U;
  uint64_t as_uint64_low7 = (uint64_t)(uint32_t)0U;
  uint64_t b1 = as_uint64_low7 ^ as_uint64_high16;
  uint64_t as_uint64_high9 = (uint64_t)c22;
  uint64_t as_uint64_high17 = as_uint64_high9 << (uint32_t)32U;
  uint64_t as_uint64_low8 = (uint64_t)c21;
  uint64_t b2 = as_uint64_low8 ^ as_uint64_high17;
  uint64_t as_uint64_high18 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high19 = as_uint64_high18 << (uint32_t)32U;
  uint64_t as_uint64_low9 = (uint64_t)c23;
  uint64_t b3 = as_uint64_low9 ^ as_uint64_high19;
  uint64_t as_uint64_high20 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high110 = as_uint64_high20 << (uint32_t)32U;
  uint64_t as_uint64_low10 = (uint64_t)(uint32_t)0U;
  uint64_t b4 = as_uint64_low10 ^ as_uint64_high110;
  uint64_t as_uint64_high21 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high111 = as_uint64_high21 << (uint32_t)32U;
  uint64_t as_uint64_low11 = (uint64_t)(uint32_t)0U;
  uint64_t b5 = as_uint64_low11 ^ as_uint64_high111;
  t110[0U] = b0;
  t110[1U] = b1;
  t110[2U] = b2;
  t110[3U] = b3;
  t110[4U] = b4;
  t110[5U] = b5;
  uint64_t as_uint64_high22 = (uint64_t)c13;
  uint64_t as_uint64_high112 = as_uint64_high22 << (uint32_t)32U;
  uint64_t as_uint64_low12 = (uint64_t)c12;
  uint64_t b00 = as_uint64_low12 ^ as_uint64_high112;
  uint64_t as_uint64_high23 = (uint64_t)c15;
  uint64_t as_uint64_high113 = as_uint64_high23 << (uint32_t)32U;
  uint64_t as_uint64_low13 = (uint64_t)c14;
  uint64_t b10 = as_uint64_low13 ^ as_uint64_high113;
  uint64_t as_uint64_high24 = (uint64_t)c17;
  uint64_t as_uint64_high114 = as_uint64_high24 << (uint32_t)32U;
  uint64_t as_uint64_low14 = (uint64_t)c16;
  uint64_t b20 = as_uint64_low14 ^ as_uint64_high114;
  uint64_t as_uint64_high25 = (uint64_t)c19;
  uint64_t as_uint64_high115 = as_uint64_high25 << (uint32_t)32U;
  uint64_t as_uint64_low15 = (uint64_t)c18;
  uint64_t b30 = as_uint64_low15 ^ as_uint64_high115;
  uint64_t as_uint64_high26 = (uint64_t)c21;
  uint64_t as_uint64_high116 = as_uint64_high26 << (uint32_t)32U;
  uint64_t as_uint64_low16 = (uint64_t)c20;
  uint64_t b40 = as_uint64_low16 ^ as_uint64_high116;
  uint64_t as_uint64_high27 = (uint64_t)c23;
  uint64_t as_uint64_high117 = as_uint64_high27 << (uint32_t)32U;
  uint64_t as_uint64_low17 = (uint64_t)c22;
  uint64_t b50 = as_uint64_low17 ^ as_uint64_high117;
  t210[0U] = b00;
  t210[1U] = b10;
  t210[2U] = b20;
  t210[3U] = b30;
  t210[4U] = b40;
  t210[5U] = b50;
  uint32_t len0 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len0);
  uint64_t tempBuffer10[len0];
  memset(tempBuffer10, 0U, len0 * sizeof (uint64_t));
  uint64_t
  p1[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len11 = (uint32_t)6U;
  uint64_t c25 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len11 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t210[(uint32_t)4U * i12];
    uint64_t t220 = p1[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer10 + (uint32_t)4U * i12;
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t12, t220, res_i0);
    uint64_t t120 = t210[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p1[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer10 + (uint32_t)4U * i12 + (uint32_t)1U;
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t120, t221, res_i1);
    uint64_t t121 = t210[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p1[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer10 + (uint32_t)4U * i12 + (uint32_t)2U;
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t121, t222, res_i2);
    uint64_t t122 = t210[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p1[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer10 + (uint32_t)4U * i12 + (uint32_t)3U;
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t122, t22, res_i);
  }
  for (uint32_t i12 = len11 / (uint32_t)4U * (uint32_t)4U; i12 < len11; i12++)
  {
    uint64_t t12 = t210[i12];
    uint64_t t22 = p1[i12];
    uint64_t *res_i = tempBuffer10 + i12;
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t12, t22, res_i);
  }
  uint64_t r1 = c25;
  uint64_t r2 = r1;
  cmovznz4_p384(r2, tempBuffer10, t210, t210);
  uint64_t as_uint64_high28 = (uint64_t)c22;
  uint64_t as_uint64_high118 = as_uint64_high28 << (uint32_t)32U;
  uint64_t as_uint64_low18 = (uint64_t)c21;
  uint64_t b01 = as_uint64_low18 ^ as_uint64_high118;
  uint64_t as_uint64_high29 = (uint64_t)c12;
  uint64_t as_uint64_high119 = as_uint64_high29 << (uint32_t)32U;
  uint64_t as_uint64_low19 = (uint64_t)c23;
  uint64_t b11 = as_uint64_low19 ^ as_uint64_high119;
  uint64_t as_uint64_high30 = (uint64_t)c14;
  uint64_t as_uint64_high120 = as_uint64_high30 << (uint32_t)32U;
  uint64_t as_uint64_low20 = (uint64_t)c13;
  uint64_t b21 = as_uint64_low20 ^ as_uint64_high120;
  uint64_t as_uint64_high31 = (uint64_t)c16;
  uint64_t as_uint64_high121 = as_uint64_high31 << (uint32_t)32U;
  uint64_t as_uint64_low21 = (uint64_t)c15;
  uint64_t b31 = as_uint64_low21 ^ as_uint64_high121;
  uint64_t as_uint64_high32 = (uint64_t)c18;
  uint64_t as_uint64_high122 = as_uint64_high32 << (uint32_t)32U;
  uint64_t as_uint64_low22 = (uint64_t)c17;
  uint64_t b41 = as_uint64_low22 ^ as_uint64_high122;
  uint64_t as_uint64_high33 = (uint64_t)c20;
  uint64_t as_uint64_high123 = as_uint64_high33 << (uint32_t)32U;
  uint64_t as_uint64_low23 = (uint64_t)c19;
  uint64_t b51 = as_uint64_low23 ^ as_uint64_high123;
  t310[0U] = b01;
  t310[1U] = b11;
  t310[2U] = b21;
  t310[3U] = b31;
  t310[4U] = b41;
  t310[5U] = b51;
  uint32_t len2 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len2);
  uint64_t tempBuffer11[len2];
  memset(tempBuffer11, 0U, len2 * sizeof (uint64_t));
  uint64_t
  p2[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len12 = (uint32_t)6U;
  uint64_t c26 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len12 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t310[(uint32_t)4U * i12];
    uint64_t t220 = p2[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer11 + (uint32_t)4U * i12;
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t12, t220, res_i0);
    uint64_t t120 = t310[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p2[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer11 + (uint32_t)4U * i12 + (uint32_t)1U;
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t120, t221, res_i1);
    uint64_t t121 = t310[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p2[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer11 + (uint32_t)4U * i12 + (uint32_t)2U;
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t121, t222, res_i2);
    uint64_t t122 = t310[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p2[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer11 + (uint32_t)4U * i12 + (uint32_t)3U;
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t122, t22, res_i);
  }
  for (uint32_t i12 = len12 / (uint32_t)4U * (uint32_t)4U; i12 < len12; i12++)
  {
    uint64_t t12 = t310[i12];
    uint64_t t22 = p2[i12];
    uint64_t *res_i = tempBuffer11 + i12;
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t12, t22, res_i);
  }
  uint64_t r3 = c26;
  uint64_t r4 = r3;
  cmovznz4_p384(r4, tempBuffer11, t310, t310);
  uint64_t as_uint64_high34 = (uint64_t)c23;
  uint64_t as_uint64_high124 = as_uint64_high34 << (uint32_t)32U;
  uint64_t as_uint64_low24 = (uint64_t)(uint32_t)0U;
  uint64_t b02 = as_uint64_low24 ^ as_uint64_high124;
  uint64_t as_uint64_high35 = (uint64_t)c20;
  uint64_t as_uint64_high125 = as_uint64_high35 << (uint32_t)32U;
  uint64_t as_uint64_low25 = (uint64_t)(uint32_t)0U;
  uint64_t b12 = as_uint64_low25 ^ as_uint64_high125;
  uint64_t as_uint64_high36 = (uint64_t)c13;
  uint64_t as_uint64_high126 = as_uint64_high36 << (uint32_t)32U;
  uint64_t as_uint64_low26 = (uint64_t)c12;
  uint64_t b22 = as_uint64_low26 ^ as_uint64_high126;
  uint64_t as_uint64_high37 = (uint64_t)c15;
  uint64_t as_uint64_high127 = as_uint64_high37 << (uint32_t)32U;
  uint64_t as_uint64_low27 = (uint64_t)c14;
  uint64_t b32 = as_uint64_low27 ^ as_uint64_high127;
  uint64_t as_uint64_high38 = (uint64_t)c17;
  uint64_t as_uint64_high128 = as_uint64_high38 << (uint32_t)32U;
  uint64_t as_uint64_low28 = (uint64_t)c16;
  uint64_t b42 = as_uint64_low28 ^ as_uint64_high128;
  uint64_t as_uint64_high39 = (uint64_t)c19;
  uint64_t as_uint64_high129 = as_uint64_high39 << (uint32_t)32U;
  uint64_t as_uint64_low29 = (uint64_t)c18;
  uint64_t b52 = as_uint64_low29 ^ as_uint64_high129;
  t410[0U] = b02;
  t410[1U] = b12;
  t410[2U] = b22;
  t410[3U] = b32;
  t410[4U] = b42;
  t410[5U] = b52;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer12[len3];
  memset(tempBuffer12, 0U, len3 * sizeof (uint64_t));
  uint64_t
  p3[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len13 = (uint32_t)6U;
  uint64_t c27 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len13 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t410[(uint32_t)4U * i12];
    uint64_t t220 = p3[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer12 + (uint32_t)4U * i12;
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t12, t220, res_i0);
    uint64_t t120 = t410[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p3[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer12 + (uint32_t)4U * i12 + (uint32_t)1U;
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t120, t221, res_i1);
    uint64_t t121 = t410[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p3[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer12 + (uint32_t)4U * i12 + (uint32_t)2U;
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t121, t222, res_i2);
    uint64_t t122 = t410[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p3[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer12 + (uint32_t)4U * i12 + (uint32_t)3U;
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t122, t22, res_i);
  }
  for (uint32_t i12 = len13 / (uint32_t)4U * (uint32_t)4U; i12 < len13; i12++)
  {
    uint64_t t12 = t410[i12];
    uint64_t t22 = p3[i12];
    uint64_t *res_i = tempBuffer12 + i12;
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t12, t22, res_i);
  }
  uint64_t r5 = c27;
  uint64_t r6 = r5;
  cmovznz4_p384(r6, tempBuffer12, t410, t410);
  uint64_t as_uint64_high40 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high130 = as_uint64_high40 << (uint32_t)32U;
  uint64_t as_uint64_low30 = (uint64_t)(uint32_t)0U;
  uint64_t b03 = as_uint64_low30 ^ as_uint64_high130;
  uint64_t as_uint64_high41 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high131 = as_uint64_high41 << (uint32_t)32U;
  uint64_t as_uint64_low31 = (uint64_t)(uint32_t)0U;
  uint64_t b13 = as_uint64_low31 ^ as_uint64_high131;
  uint64_t as_uint64_high42 = (uint64_t)c21;
  uint64_t as_uint64_high132 = as_uint64_high42 << (uint32_t)32U;
  uint64_t as_uint64_low32 = (uint64_t)c20;
  uint64_t b23 = as_uint64_low32 ^ as_uint64_high132;
  uint64_t as_uint64_high43 = (uint64_t)c23;
  uint64_t as_uint64_high133 = as_uint64_high43 << (uint32_t)32U;
  uint64_t as_uint64_low33 = (uint64_t)c22;
  uint64_t b33 = as_uint64_low33 ^ as_uint64_high133;
  uint64_t as_uint64_high44 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high134 = as_uint64_high44 << (uint32_t)32U;
  uint64_t as_uint64_low34 = (uint64_t)(uint32_t)0U;
  uint64_t b43 = as_uint64_low34 ^ as_uint64_high134;
  uint64_t as_uint64_high45 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high135 = as_uint64_high45 << (uint32_t)32U;
  uint64_t as_uint64_low35 = (uint64_t)(uint32_t)0U;
  uint64_t b53 = as_uint64_low35 ^ as_uint64_high135;
  t510[0U] = b03;
  t510[1U] = b13;
  t510[2U] = b23;
  t510[3U] = b33;
  t510[4U] = b43;
  t510[5U] = b53;
  uint32_t len4 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len4);
  uint64_t tempBuffer13[len4];
  memset(tempBuffer13, 0U, len4 * sizeof (uint64_t));
  uint64_t
  p4[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len14 = (uint32_t)6U;
  uint64_t c28 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len14 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t510[(uint32_t)4U * i12];
    uint64_t t220 = p4[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer13 + (uint32_t)4U * i12;
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t12, t220, res_i0);
    uint64_t t120 = t510[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p4[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer13 + (uint32_t)4U * i12 + (uint32_t)1U;
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t120, t221, res_i1);
    uint64_t t121 = t510[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p4[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer13 + (uint32_t)4U * i12 + (uint32_t)2U;
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t121, t222, res_i2);
    uint64_t t122 = t510[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p4[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer13 + (uint32_t)4U * i12 + (uint32_t)3U;
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t122, t22, res_i);
  }
  for (uint32_t i12 = len14 / (uint32_t)4U * (uint32_t)4U; i12 < len14; i12++)
  {
    uint64_t t12 = t510[i12];
    uint64_t t22 = p4[i12];
    uint64_t *res_i = tempBuffer13 + i12;
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t12, t22, res_i);
  }
  uint64_t r7 = c28;
  uint64_t r8 = r7;
  cmovznz4_p384(r8, tempBuffer13, t510, t510);
  uint64_t as_uint64_high46 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high136 = as_uint64_high46 << (uint32_t)32U;
  uint64_t as_uint64_low36 = (uint64_t)c20;
  uint64_t b04 = as_uint64_low36 ^ as_uint64_high136;
  uint64_t as_uint64_high47 = (uint64_t)c21;
  uint64_t as_uint64_high137 = as_uint64_high47 << (uint32_t)32U;
  uint64_t as_uint64_low37 = (uint64_t)(uint32_t)0U;
  uint64_t b14 = as_uint64_low37 ^ as_uint64_high137;
  uint64_t as_uint64_high48 = (uint64_t)c23;
  uint64_t as_uint64_high138 = as_uint64_high48 << (uint32_t)32U;
  uint64_t as_uint64_low38 = (uint64_t)c22;
  uint64_t b24 = as_uint64_low38 ^ as_uint64_high138;
  uint64_t as_uint64_high49 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high139 = as_uint64_high49 << (uint32_t)32U;
  uint64_t as_uint64_low39 = (uint64_t)(uint32_t)0U;
  uint64_t b34 = as_uint64_low39 ^ as_uint64_high139;
  uint64_t as_uint64_high50 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high140 = as_uint64_high50 << (uint32_t)32U;
  uint64_t as_uint64_low40 = (uint64_t)(uint32_t)0U;
  uint64_t b44 = as_uint64_low40 ^ as_uint64_high140;
  uint64_t as_uint64_high51 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high141 = as_uint64_high51 << (uint32_t)32U;
  uint64_t as_uint64_low41 = (uint64_t)(uint32_t)0U;
  uint64_t b54 = as_uint64_low41 ^ as_uint64_high141;
  t610[0U] = b04;
  t610[1U] = b14;
  t610[2U] = b24;
  t610[3U] = b34;
  t610[4U] = b44;
  t610[5U] = b54;
  uint32_t len5 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len5);
  uint64_t tempBuffer14[len5];
  memset(tempBuffer14, 0U, len5 * sizeof (uint64_t));
  uint64_t
  p5[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len15 = (uint32_t)6U;
  uint64_t c29 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len15 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t610[(uint32_t)4U * i12];
    uint64_t t220 = p5[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer14 + (uint32_t)4U * i12;
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t12, t220, res_i0);
    uint64_t t120 = t610[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p5[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer14 + (uint32_t)4U * i12 + (uint32_t)1U;
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t120, t221, res_i1);
    uint64_t t121 = t610[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p5[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer14 + (uint32_t)4U * i12 + (uint32_t)2U;
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t121, t222, res_i2);
    uint64_t t122 = t610[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p5[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer14 + (uint32_t)4U * i12 + (uint32_t)3U;
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t122, t22, res_i);
  }
  for (uint32_t i12 = len15 / (uint32_t)4U * (uint32_t)4U; i12 < len15; i12++)
  {
    uint64_t t12 = t610[i12];
    uint64_t t22 = p5[i12];
    uint64_t *res_i = tempBuffer14 + i12;
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t12, t22, res_i);
  }
  uint64_t r9 = c29;
  uint64_t r10 = r9;
  cmovznz4_p384(r10, tempBuffer14, t610, t610);
  uint64_t as_uint64_high52 = (uint64_t)c12;
  uint64_t as_uint64_high142 = as_uint64_high52 << (uint32_t)32U;
  uint64_t as_uint64_low42 = (uint64_t)c23;
  uint64_t b05 = as_uint64_low42 ^ as_uint64_high142;
  uint64_t as_uint64_high53 = (uint64_t)c14;
  uint64_t as_uint64_high143 = as_uint64_high53 << (uint32_t)32U;
  uint64_t as_uint64_low43 = (uint64_t)c13;
  uint64_t b15 = as_uint64_low43 ^ as_uint64_high143;
  uint64_t as_uint64_high54 = (uint64_t)c16;
  uint64_t as_uint64_high144 = as_uint64_high54 << (uint32_t)32U;
  uint64_t as_uint64_low44 = (uint64_t)c15;
  uint64_t b25 = as_uint64_low44 ^ as_uint64_high144;
  uint64_t as_uint64_high55 = (uint64_t)c18;
  uint64_t as_uint64_high145 = as_uint64_high55 << (uint32_t)32U;
  uint64_t as_uint64_low45 = (uint64_t)c17;
  uint64_t b35 = as_uint64_low45 ^ as_uint64_high145;
  uint64_t as_uint64_high56 = (uint64_t)c20;
  uint64_t as_uint64_high146 = as_uint64_high56 << (uint32_t)32U;
  uint64_t as_uint64_low46 = (uint64_t)c19;
  uint64_t b45 = as_uint64_low46 ^ as_uint64_high146;
  uint64_t as_uint64_high57 = (uint64_t)c22;
  uint64_t as_uint64_high147 = as_uint64_high57 << (uint32_t)32U;
  uint64_t as_uint64_low47 = (uint64_t)c21;
  uint64_t b55 = as_uint64_low47 ^ as_uint64_high147;
  t710[0U] = b05;
  t710[1U] = b15;
  t710[2U] = b25;
  t710[3U] = b35;
  t710[4U] = b45;
  t710[5U] = b55;
  uint32_t len6 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len6);
  uint64_t tempBuffer15[len6];
  memset(tempBuffer15, 0U, len6 * sizeof (uint64_t));
  uint64_t
  p6[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len16 = (uint32_t)6U;
  uint64_t c30 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len16 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t710[(uint32_t)4U * i12];
    uint64_t t220 = p6[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer15 + (uint32_t)4U * i12;
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t12, t220, res_i0);
    uint64_t t120 = t710[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p6[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer15 + (uint32_t)4U * i12 + (uint32_t)1U;
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t120, t221, res_i1);
    uint64_t t121 = t710[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p6[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer15 + (uint32_t)4U * i12 + (uint32_t)2U;
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t121, t222, res_i2);
    uint64_t t122 = t710[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p6[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer15 + (uint32_t)4U * i12 + (uint32_t)3U;
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t122, t22, res_i);
  }
  for (uint32_t i12 = len16 / (uint32_t)4U * (uint32_t)4U; i12 < len16; i12++)
  {
    uint64_t t12 = t710[i12];
    uint64_t t22 = p6[i12];
    uint64_t *res_i = tempBuffer15 + i12;
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t12, t22, res_i);
  }
  uint64_t r11 = c30;
  uint64_t r12 = r11;
  cmovznz4_p384(r12, tempBuffer15, t710, t710);
  uint64_t as_uint64_high58 = (uint64_t)c20;
  uint64_t as_uint64_high148 = as_uint64_high58 << (uint32_t)32U;
  uint64_t as_uint64_low48 = (uint64_t)(uint32_t)0U;
  uint64_t b06 = as_uint64_low48 ^ as_uint64_high148;
  uint64_t as_uint64_high59 = (uint64_t)c22;
  uint64_t as_uint64_high149 = as_uint64_high59 << (uint32_t)32U;
  uint64_t as_uint64_low49 = (uint64_t)c21;
  uint64_t b16 = as_uint64_low49 ^ as_uint64_high149;
  uint64_t as_uint64_high60 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high150 = as_uint64_high60 << (uint32_t)32U;
  uint64_t as_uint64_low50 = (uint64_t)c23;
  uint64_t b26 = as_uint64_low50 ^ as_uint64_high150;
  uint64_t as_uint64_high61 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high151 = as_uint64_high61 << (uint32_t)32U;
  uint64_t as_uint64_low51 = (uint64_t)(uint32_t)0U;
  uint64_t b36 = as_uint64_low51 ^ as_uint64_high151;
  uint64_t as_uint64_high62 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high152 = as_uint64_high62 << (uint32_t)32U;
  uint64_t as_uint64_low52 = (uint64_t)(uint32_t)0U;
  uint64_t b46 = as_uint64_low52 ^ as_uint64_high152;
  uint64_t as_uint64_high63 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high153 = as_uint64_high63 << (uint32_t)32U;
  uint64_t as_uint64_low53 = (uint64_t)(uint32_t)0U;
  uint64_t b56 = as_uint64_low53 ^ as_uint64_high153;
  t810[0U] = b06;
  t810[1U] = b16;
  t810[2U] = b26;
  t810[3U] = b36;
  t810[4U] = b46;
  t810[5U] = b56;
  uint32_t len7 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len7);
  uint64_t tempBuffer16[len7];
  memset(tempBuffer16, 0U, len7 * sizeof (uint64_t));
  uint64_t
  p7[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len17 = (uint32_t)6U;
  uint64_t c31 = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len17 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t810[(uint32_t)4U * i12];
    uint64_t t220 = p7[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer16 + (uint32_t)4U * i12;
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t12, t220, res_i0);
    uint64_t t120 = t810[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p7[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer16 + (uint32_t)4U * i12 + (uint32_t)1U;
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t120, t221, res_i1);
    uint64_t t121 = t810[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p7[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer16 + (uint32_t)4U * i12 + (uint32_t)2U;
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t121, t222, res_i2);
    uint64_t t122 = t810[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p7[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer16 + (uint32_t)4U * i12 + (uint32_t)3U;
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t122, t22, res_i);
  }
  for (uint32_t i12 = len17 / (uint32_t)4U * (uint32_t)4U; i12 < len17; i12++)
  {
    uint64_t t12 = t810[i12];
    uint64_t t22 = p7[i12];
    uint64_t *res_i = tempBuffer16 + i12;
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t12, t22, res_i);
  }
  uint64_t r13 = c31;
  uint64_t r14 = r13;
  cmovznz4_p384(r14, tempBuffer16, t810, t810);
  uint64_t as_uint64_high64 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high154 = as_uint64_high64 << (uint32_t)32U;
  uint64_t as_uint64_low54 = (uint64_t)(uint32_t)0U;
  uint64_t b07 = as_uint64_low54 ^ as_uint64_high154;
  uint64_t as_uint64_high65 = (uint64_t)c23;
  uint64_t as_uint64_high155 = as_uint64_high65 << (uint32_t)32U;
  uint64_t as_uint64_low55 = (uint64_t)(uint32_t)0U;
  uint64_t b17 = as_uint64_low55 ^ as_uint64_high155;
  uint64_t as_uint64_high66 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high156 = as_uint64_high66 << (uint32_t)32U;
  uint64_t as_uint64_low56 = (uint64_t)c23;
  uint64_t b27 = as_uint64_low56 ^ as_uint64_high156;
  uint64_t as_uint64_high67 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high157 = as_uint64_high67 << (uint32_t)32U;
  uint64_t as_uint64_low57 = (uint64_t)(uint32_t)0U;
  uint64_t b37 = as_uint64_low57 ^ as_uint64_high157;
  uint64_t as_uint64_high68 = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high158 = as_uint64_high68 << (uint32_t)32U;
  uint64_t as_uint64_low58 = (uint64_t)(uint32_t)0U;
  uint64_t b47 = as_uint64_low58 ^ as_uint64_high158;
  uint64_t as_uint64_high = (uint64_t)(uint32_t)0U;
  uint64_t as_uint64_high159 = as_uint64_high << (uint32_t)32U;
  uint64_t as_uint64_low = (uint64_t)(uint32_t)0U;
  uint64_t b57 = as_uint64_low ^ as_uint64_high159;
  t910[0U] = b07;
  t910[1U] = b17;
  t910[2U] = b27;
  t910[3U] = b37;
  t910[4U] = b47;
  t910[5U] = b57;
  uint32_t len8 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len8);
  uint64_t tempBuffer17[len8];
  memset(tempBuffer17, 0U, len8 * sizeof (uint64_t));
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len1 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len1 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t910[(uint32_t)4U * i12];
    uint64_t t220 = p[(uint32_t)4U * i12];
    uint64_t *res_i0 = tempBuffer17 + (uint32_t)4U * i12;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t220, res_i0);
    uint64_t t120 = t910[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer17 + (uint32_t)4U * i12 + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t120, t221, res_i1);
    uint64_t t121 = t910[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer17 + (uint32_t)4U * i12 + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t121, t222, res_i2);
    uint64_t t122 = t910[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t *res_i = tempBuffer17 + (uint32_t)4U * i12 + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t122, t22, res_i);
  }
  for (uint32_t i12 = len1 / (uint32_t)4U * (uint32_t)4U; i12 < len1; i12++)
  {
    uint64_t t12 = t910[i12];
    uint64_t t22 = p[i12];
    uint64_t *res_i = tempBuffer17 + i12;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t22, res_i);
  }
  uint64_t r15 = c;
  uint64_t r16 = r15;
  cmovznz4_p384(r16, tempBuffer17, t910, t910);
  uint64_t *t010 = tempBuffer;
  uint64_t *t11 = tempBuffer + (uint32_t)6U;
  uint64_t *t21 = tempBuffer + (uint32_t)12U;
  uint64_t *t31 = tempBuffer + (uint32_t)18U;
  uint64_t *t41 = tempBuffer + (uint32_t)24U;
  uint64_t *t51 = tempBuffer + (uint32_t)30U;
  uint64_t *t61 = tempBuffer + (uint32_t)36U;
  uint64_t *t71 = tempBuffer + (uint32_t)42U;
  uint64_t *t81 = tempBuffer + (uint32_t)48U;
  uint64_t *t91 = tempBuffer + (uint32_t)54U;
  felem_double_p384(t11, t11);
  felem_add_p384(t010, t11, t11);
  felem_add_p384(t11, t21, t21);
  felem_add_p384(t21, t31, t31);
  felem_add_p384(t31, t41, t41);
  felem_add_p384(t41, t51, t51);
  felem_add_p384(t51, t61, t61);
  felem_sub_p384(t61, t71, t71);
  felem_sub_p384(t71, t81, t81);
  felem_sub_p384(t81, t91, o);
}

#define MontLadder 0
#define Radix 1
#define WNAF 2

typedef uint8_t ladder;

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

static inline void toDomain_p384(uint64_t *value, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t multBuffer[(uint32_t)2U * len];
  memset(multBuffer, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  uint64_t *oToZero = multBuffer;
  uint64_t *oToCopy = multBuffer + len1;
  memcpy(oToCopy, value, len1 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    oToZero[i] = (uint64_t)0U;
  }
  solinas_reduction_impl_p384(multBuffer, result);
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
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t t10 = t[0U];
    uint32_t len30 = (uint32_t)4U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
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
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
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
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
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
  uint32_t len20 = (uint32_t)4U;
  uint64_t cin = t[len20];
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
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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

static inline void fromDomain_p384(uint64_t *f, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, f, len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len1);
  uint64_t t2[(uint32_t)2U * len1];
  memset(t2, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len2; i0++)
  {
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    mul_atomic(t10, k0, &y, &temp);
    uint64_t y_ = y;
    uint32_t len30 = (uint32_t)6U * (uint32_t)2U;
    for (uint32_t i = (uint32_t)0U; i < len30; i++)
    {
      t2[i] = (uint64_t)0U;
    }
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len31 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    memset(partResult, 0U, (len31 + (uint32_t)1U) * sizeof (uint64_t));
    {
      uint64_t bj = (&bBuffer)[0U];
      uint64_t *res_j = partResult;
      uint64_t c = (uint64_t)0U;
      for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
      {
        uint64_t a_i = p[(uint32_t)4U * i];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i0);
        uint64_t a_i0 = p[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
        c = mul_wide_add2_u64(a_i0, bj, c, res_i1);
        uint64_t a_i1 = p[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
        c = mul_wide_add2_u64(a_i1, bj, c, res_i2);
        uint64_t a_i2 = p[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
        c = mul_wide_add2_u64(a_i2, bj, c, res_i);
      }
      for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
      {
        uint64_t a_i = p[i];
        uint64_t *res_i = res_j + i;
        c = mul_wide_add2_u64(a_i, bj, c, res_i);
      }
      uint64_t r = c;
      partResult[len31 + (uint32_t)0U] = r;
    }
    uint32_t len32 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len32 / (uint32_t)4U; i++)
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
    uint32_t len3 = (uint32_t)11U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len3] = carry;
  }
  uint32_t len20 = (uint32_t)6U;
  uint64_t cin = t[len20];
  uint64_t *x_ = t;
  uint32_t len3 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer[len3];
  memset(tempBuffer, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len4 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len4 / (uint32_t)4U; i++)
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
  cmovznz4_p384(carry, tempBuffer, x_, result);
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
  copy_conditional_p256_l(resultZ, zeroBuffer, bit);
}

static inline void norm_p384(uint64_t *p, uint64_t *resultPoint, uint64_t *tempBuffer)
{
  uint64_t *xf = p;
  uint64_t *yf = p + (uint32_t)6U;
  uint64_t *zf = p + (uint32_t)12U;
  uint64_t *z2f = tempBuffer + (uint32_t)6U;
  uint64_t *z3f = tempBuffer + (uint32_t)12U;
  uint64_t *t8 = tempBuffer + (uint32_t)18U;
  montgomery_square_buffer_dh_p384(zf, z2f);
  montgomery_multiplication_buffer_dh_p384(z2f, zf, z3f);
  exponent_p384(z2f, z2f, t8);
  exponent_p384(z3f, z3f, t8);
  montgomery_multiplication_buffer_dh_p384(xf, z2f, z2f);
  montgomery_multiplication_buffer_dh_p384(yf, z3f, z3f);
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t zeroBuffer[len];
  memset(zeroBuffer, 0U, len * sizeof (uint64_t));
  uint64_t *resultX = resultPoint;
  uint64_t *resultY = resultPoint + len;
  uint64_t *resultZ = resultPoint + (uint32_t)2U * len;
  uint32_t len10 = (uint32_t)6U;
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = p + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t bit = r;
  fromDomain_p384(z2f, resultX);
  fromDomain_p384(z3f, resultY);
  resultZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    resultZ[i] = (uint64_t)0U;
  }
  copy_conditional_p384_l(resultZ, zeroBuffer, bit);
}

static inline void
scalarMultiplicationWithoutNorm_p256_ml(
  uint64_t *p,
  uint64_t *result,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *q = tempBuffer;
  uint64_t *temp = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *x = q;
  uint64_t *y = q + len1;
  uint64_t *z = q + (uint32_t)2U * len1;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len20 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len21 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    z[i] = (uint64_t)0U;
  }
  uint32_t len10 = (uint32_t)4U;
  uint64_t *p_x = p;
  uint64_t *p_y = p + len10;
  uint64_t *p_z = p + (uint32_t)2U * len10;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len10;
  uint64_t *r_z = result + (uint32_t)2U * len10;
  toDomain_p256(p_x, r_x);
  toDomain_p256(p_y, r_y);
  toDomain_p256(p_z, r_z);
  montgomery_ladderP256L(q, result, (uint8_t *)scalar, temp);
  memcpy(result, q, (uint32_t)12U * sizeof (uint64_t));
}

static inline void
scalarMultiplicationWithoutNorm_p384_ml(
  uint64_t *p,
  uint64_t *result,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t len = (uint32_t)6U;
  uint64_t *q = tempBuffer;
  uint64_t *temp = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)6U;
  uint64_t *x = q;
  uint64_t *y = q + len1;
  uint64_t *z = q + (uint32_t)2U * len1;
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len20 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len21 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    z[i] = (uint64_t)0U;
  }
  uint32_t len10 = (uint32_t)6U;
  uint64_t *p_x = p;
  uint64_t *p_y = p + len10;
  uint64_t *p_z = p + (uint32_t)2U * len10;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len10;
  uint64_t *r_z = result + (uint32_t)2U * len10;
  toDomain_p384(p_x, r_x);
  toDomain_p384(p_y, r_y);
  toDomain_p384(p_z, r_z);
  montgomery_ladderP384L(q, result, (uint8_t *)scalar, temp);
  memcpy(result, q, (uint32_t)18U * sizeof (uint64_t));
}

static inline void
scalarMultiplicationWithoutNorm_p256_radix(
  uint64_t *p,
  uint64_t *result,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *p_x = p;
  uint64_t *p_y = p + len;
  uint64_t *p_z = p + (uint32_t)2U * len;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len;
  uint64_t *r_z = result + (uint32_t)2U * len;
  toDomain_p256(p_x, r_x);
  toDomain_p256(p_y, r_y);
  toDomain_p256(p_z, r_z);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * ((uint32_t)4U * (uint32_t)3U));
  uint64_t precomputedTable[(uint32_t)16U * ((uint32_t)4U * (uint32_t)3U)];
  memset(precomputedTable,
    0U,
    (uint32_t)16U * ((uint32_t)4U * (uint32_t)3U) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)3U);
  uint64_t tempPoint[(uint32_t)4U * (uint32_t)3U];
  memset(tempPoint, 0U, (uint32_t)4U * (uint32_t)3U * sizeof (uint64_t));
  uint64_t *tempBuffer1 = tempBuffer;
  generatePrecomputedTable(Spec_ECC_Curves_P256, precomputedTable, result, tempBuffer1);
  getPointPrecomputedTable(Spec_ECC_Curves_P256, scalar, precomputedTable, (uint32_t)0U, result);
  for (uint32_t i = (uint32_t)1U; i < (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U); i++)
  {
    getPointPrecomputedTable(Spec_ECC_Curves_P256, scalar, precomputedTable, i, tempPoint);
    {
      point_double_p256(result, result, tempBuffer1);
    }
    {
      point_double_p256(result, result, tempBuffer1);
    }
    {
      point_double_p256(result, result, tempBuffer1);
    }
    {
      point_double_p256(result, result, tempBuffer1);
    }
    point_add_p256(tempPoint, result, result, tempBuffer1);
  }
}

static inline void
scalarMultiplicationWithoutNorm_p384_radix(
  uint64_t *p,
  uint64_t *result,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t len = (uint32_t)6U;
  uint64_t *p_x = p;
  uint64_t *p_y = p + len;
  uint64_t *p_z = p + (uint32_t)2U * len;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len;
  uint64_t *r_z = result + (uint32_t)2U * len;
  toDomain_p384(p_x, r_x);
  toDomain_p384(p_y, r_y);
  toDomain_p384(p_z, r_z);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * ((uint32_t)6U * (uint32_t)3U));
  uint64_t precomputedTable[(uint32_t)16U * ((uint32_t)6U * (uint32_t)3U)];
  memset(precomputedTable,
    0U,
    (uint32_t)16U * ((uint32_t)6U * (uint32_t)3U) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)6U * (uint32_t)3U);
  uint64_t tempPoint[(uint32_t)6U * (uint32_t)3U];
  memset(tempPoint, 0U, (uint32_t)6U * (uint32_t)3U * sizeof (uint64_t));
  uint64_t *tempBuffer1 = tempBuffer;
  generatePrecomputedTable(Spec_ECC_Curves_P384, precomputedTable, result, tempBuffer1);
  getPointPrecomputedTable(Spec_ECC_Curves_P384, scalar, precomputedTable, (uint32_t)0U, result);
  for (uint32_t i = (uint32_t)1U; i < (uint32_t)2U * ((uint32_t)6U * (uint32_t)8U); i++)
  {
    getPointPrecomputedTable(Spec_ECC_Curves_P384, scalar, precomputedTable, i, tempPoint);
    {
      point_double_p384(result, result, tempBuffer1);
    }
    {
      point_double_p384(result, result, tempBuffer1);
    }
    {
      point_double_p384(result, result, tempBuffer1);
    }
    {
      point_double_p384(result, result, tempBuffer1);
    }
    point_add_p384(tempPoint, result, result, tempBuffer1);
  }
}

static inline void
secretToPublicWithoutNorm_p256_ml(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *x = q;
  uint64_t *y = q + len1;
  uint64_t *z = q + (uint32_t)2U * len1;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len20 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len21 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    z[i] = (uint64_t)0U;
  }
  result[0U] = (uint64_t)0x79e730d418a9143cU;
  result[1U] = (uint64_t)0x75ba95fc5fedb601U;
  result[2U] = (uint64_t)0x79fb732b77622510U;
  result[3U] = (uint64_t)0x18905f76a53755c6U;
  result[4U] = (uint64_t)0xddf25357ce95560aU;
  result[5U] = (uint64_t)0x8b4ab8e4ba19e45cU;
  result[6U] = (uint64_t)0xd2e88688dd21f325U;
  result[7U] = (uint64_t)0x8571ff1825885d85U;
  result[8U] = (uint64_t)0x1U;
  result[9U] = (uint64_t)0xffffffff00000000U;
  result[10U] = (uint64_t)0xffffffffffffffffU;
  result[11U] = (uint64_t)0xfffffffeU;
  montgomery_ladderP256L(q, result, (uint8_t *)scalar, buff);
  memcpy(result, q, (uint32_t)12U * sizeof (uint64_t));
}

static inline void
secretToPublicWithoutNorm_p384_ml(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)6U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)6U;
  uint64_t *x = q;
  uint64_t *y = q + len1;
  uint64_t *z = q + (uint32_t)2U * len1;
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len20 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len21 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    z[i] = (uint64_t)0U;
  }
  result[0U] = (uint64_t)0x3dd0756649c0b528U;
  result[1U] = (uint64_t)0x20e378e2a0d6ce38U;
  result[2U] = (uint64_t)0x879c3afc541b4d6eU;
  result[3U] = (uint64_t)0x6454868459a30effU;
  result[4U] = (uint64_t)0x812ff723614ede2bU;
  result[5U] = (uint64_t)0x4d3aadc2299e1513U;
  result[6U] = (uint64_t)0x23043dad4b03a4feU;
  result[7U] = (uint64_t)0xa1bfa8bf7bb4a9acU;
  result[8U] = (uint64_t)0x8bade7562e83b050U;
  result[9U] = (uint64_t)0xc6c3521968f4ffd9U;
  result[10U] = (uint64_t)0xdd8002263969a840U;
  result[11U] = (uint64_t)0x2b78abc25a15c5e9U;
  result[12U] = (uint64_t)0xffffffff00000001U;
  result[13U] = (uint64_t)0xffffffffU;
  result[14U] = (uint64_t)0x1U;
  result[15U] = (uint64_t)0U;
  result[16U] = (uint64_t)0U;
  result[17U] = (uint64_t)0U;
  montgomery_ladderP384L(q, result, (uint8_t *)scalar, buff);
  memcpy(result, q, (uint32_t)18U * sizeof (uint64_t));
}

static inline void
secretToPublicWithoutNorm_p256_radix(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  uint64_t *pXpY = result;
  uint32_t half0 = (uint32_t)0U;
  uint32_t word = (uint32_t)((uint8_t *)scalar)[half0];
  uint32_t bitShift0 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate = bitShift0;
  uint32_t leftWord0 = word >> (uint32_t)0x4U;
  uint32_t rightWord0 = word & (uint32_t)0x0fU;
  uint32_t mask0 = (uint32_t)0U - bitShiftAsPrivate;
  uint32_t bits = leftWord0 ^ (mask0 & (leftWord0 ^ rightWord0));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits, (uint64_t)i);
    const uint64_t *lut_cmb_x = points_radix_16_p256 + (uint32_t)8U * i;
    const uint64_t *lut_cmb_y = points_radix_16_p256 + (uint32_t)8U * i + (uint32_t)4U;
    uint64_t *pointToAddX = pXpY;
    uint64_t *pointToAddY = pXpY + (uint32_t)4U;
    copy_conditional_p256_c(pointToAddX, lut_cmb_x, mask);
    copy_conditional_p256_c(pointToAddY, lut_cmb_y, mask);
  }
  uint64_t *pZ = result + (uint32_t)8U;
  uint32_t half1 = (uint32_t)0U;
  uint32_t word0 = (uint32_t)((uint8_t *)scalar)[half1];
  uint32_t bitShift1 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate0 = bitShift1;
  uint32_t leftWord1 = word0 >> (uint32_t)0x4U;
  uint32_t rightWord1 = word0 & (uint32_t)0x0fU;
  uint32_t mask1 = (uint32_t)0U - bitShiftAsPrivate0;
  uint32_t bits0 = leftWord1 ^ (mask1 & (leftWord1 ^ rightWord1));
  uint64_t flag = FStar_UInt64_eq_mask((uint64_t)bits0, (uint64_t)0U);
  pZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    pZ[i] = (uint64_t)0U;
  }
  uint64_t *pz_0 = pZ;
  uint64_t out_0 = pz_0[0U];
  uint64_t r_0 = out_0 ^ (flag & (out_0 ^ (uint64_t)0U));
  pz_0[0U] = r_0;
  for (uint32_t i0 = (uint32_t)1U; i0 < (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U); i0++)
  {
    uint64_t pointToAdd[8U] = { 0U };
    uint32_t half = i0 >> (uint32_t)1U;
    uint32_t word1 = (uint32_t)((uint8_t *)scalar)[half];
    uint32_t bitShift = i0 & (uint32_t)1U;
    uint32_t bitShiftAsPrivate1 = bitShift;
    uint32_t leftWord = word1 >> (uint32_t)0x4U;
    uint32_t rightWord = word1 & (uint32_t)0x0fU;
    uint32_t mask2 = (uint32_t)0U - bitShiftAsPrivate1;
    uint32_t bits1 = leftWord ^ (mask2 & (leftWord ^ rightWord));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits1, (uint64_t)i);
      const uint64_t *lut_cmb_x = points_radix_16_p256 + (uint32_t)8U * i;
      const uint64_t *lut_cmb_y = points_radix_16_p256 + (uint32_t)8U * i + (uint32_t)4U;
      uint64_t *pointToAddX = pointToAdd;
      uint64_t *pointToAddY = pointToAdd + (uint32_t)4U;
      copy_conditional_p256_c(pointToAddX, lut_cmb_x, mask);
      copy_conditional_p256_c(pointToAddY, lut_cmb_y, mask);
    }
    {
      point_double_p256(result, result, buff);
    }
    {
      point_double_p256(result, result, buff);
    }
    {
      point_double_p256(result, result, buff);
    }
    {
      point_double_p256(result, result, buff);
    }
    point_add_mixed_p256(result, pointToAdd, result, buff);
  }
}

static inline void
secretToPublicWithoutNorm_p384_radix(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)6U;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  uint64_t *pXpY = result;
  uint32_t half0 = (uint32_t)0U;
  uint32_t word = (uint32_t)((uint8_t *)scalar)[half0];
  uint32_t bitShift0 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate = bitShift0;
  uint32_t leftWord0 = word >> (uint32_t)0x4U;
  uint32_t rightWord0 = word & (uint32_t)0x0fU;
  uint32_t mask0 = (uint32_t)0U - bitShiftAsPrivate;
  uint32_t bits = leftWord0 ^ (mask0 & (leftWord0 ^ rightWord0));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits, (uint64_t)i);
    const uint64_t *lut_cmb_x = points_radix_16_p384 + (uint32_t)12U * i;
    const uint64_t *lut_cmb_y = points_radix_16_p384 + (uint32_t)12U * i + (uint32_t)6U;
    uint64_t *pointToAddX = pXpY;
    uint64_t *pointToAddY = pXpY + (uint32_t)6U;
    copy_conditional_p384_c(pointToAddX, lut_cmb_x, mask);
    copy_conditional_p384_c(pointToAddY, lut_cmb_y, mask);
  }
  uint64_t *pZ = result + (uint32_t)12U;
  uint32_t half1 = (uint32_t)0U;
  uint32_t word0 = (uint32_t)((uint8_t *)scalar)[half1];
  uint32_t bitShift1 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate0 = bitShift1;
  uint32_t leftWord1 = word0 >> (uint32_t)0x4U;
  uint32_t rightWord1 = word0 & (uint32_t)0x0fU;
  uint32_t mask1 = (uint32_t)0U - bitShiftAsPrivate0;
  uint32_t bits0 = leftWord1 ^ (mask1 & (leftWord1 ^ rightWord1));
  uint64_t flag = FStar_UInt64_eq_mask((uint64_t)bits0, (uint64_t)0U);
  pZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    pZ[i] = (uint64_t)0U;
  }
  uint64_t *pz_0 = pZ;
  uint64_t out_0 = pz_0[0U];
  uint64_t r_0 = out_0 ^ (flag & (out_0 ^ (uint64_t)0U));
  pz_0[0U] = r_0;
  for (uint32_t i0 = (uint32_t)1U; i0 < (uint32_t)2U * ((uint32_t)6U * (uint32_t)8U); i0++)
  {
    uint64_t pointToAdd[12U] = { 0U };
    uint32_t half = i0 >> (uint32_t)1U;
    uint32_t word1 = (uint32_t)((uint8_t *)scalar)[half];
    uint32_t bitShift = i0 & (uint32_t)1U;
    uint32_t bitShiftAsPrivate1 = bitShift;
    uint32_t leftWord = word1 >> (uint32_t)0x4U;
    uint32_t rightWord = word1 & (uint32_t)0x0fU;
    uint32_t mask2 = (uint32_t)0U - bitShiftAsPrivate1;
    uint32_t bits1 = leftWord ^ (mask2 & (leftWord ^ rightWord));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits1, (uint64_t)i);
      const uint64_t *lut_cmb_x = points_radix_16_p384 + (uint32_t)12U * i;
      const uint64_t *lut_cmb_y = points_radix_16_p384 + (uint32_t)12U * i + (uint32_t)6U;
      uint64_t *pointToAddX = pointToAdd;
      uint64_t *pointToAddY = pointToAdd + (uint32_t)6U;
      copy_conditional_p384_c(pointToAddX, lut_cmb_x, mask);
      copy_conditional_p384_c(pointToAddY, lut_cmb_y, mask);
    }
    {
      point_double_p384(result, result, buff);
    }
    {
      point_double_p384(result, result, buff);
    }
    {
      point_double_p384(result, result, buff);
    }
    {
      point_double_p384(result, result, buff);
    }
    point_add_mixed_p384(result, pointToAdd, result, buff);
  }
}

static inline void
secretToPublicWithoutNorm_p256_wnaf(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  scalar_multiplication_cmb_p256(result, scalar, buff);
}

static inline void
secretToPublicWithoutNorm_p384_wnaf(uint64_t *result, void *scalar, uint64_t *tempBuffer)
{
  uint32_t len = (uint32_t)6U;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  scalar_multiplication_cmb_p384(result, scalar, buff);
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

static inline void fromFormPoint_p384(uint64_t *i, uint8_t *o)
{
  uint32_t len = (uint32_t)6U;
  uint32_t scalarLen = (uint32_t)48U;
  uint64_t *resultBufferX = i;
  uint64_t *resultBufferY = i + len;
  uint8_t *resultX = o;
  uint8_t *resultY = o + scalarLen;
  uint32_t len1 = (uint32_t)6U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i0;
    uint64_t left = resultBufferX[i0];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i0] = right;
    resultBufferX[lenRight] = left;
  }
  uint32_t len10 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    store64_be(resultX + i0 * (uint32_t)8U, resultBufferX[i0]);
  }
  uint32_t len11 = (uint32_t)6U;
  uint32_t lenByTwo0 = len11 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo0; i0++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i0;
    uint64_t left = resultBufferY[i0];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i0] = right;
    resultBufferY[lenRight] = left;
  }
  uint32_t len12 = (uint32_t)6U;
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
  toUint64ChangeEndian_p256(pointScalarX, pointX);
  toUint64ChangeEndian_p256(pointScalarY, pointY);
  pointZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i0 = (uint32_t)1U; i0 < len1; i0++)
  {
    pointZ[i0] = (uint64_t)0U;
  }
}

static inline void toFormPoint_p384(uint8_t *i, uint64_t *o)
{
  uint32_t len = (uint32_t)6U;
  uint32_t coordLen = (uint32_t)48U;
  uint8_t *pointScalarX = i;
  uint8_t *pointScalarY = i + coordLen;
  uint64_t *pointX = o;
  uint64_t *pointY = o + len;
  uint64_t *pointZ = o + (uint32_t)2U * len;
  toUint64ChangeEndian_p384(pointScalarX, pointX);
  toUint64ChangeEndian_p384(pointScalarY, pointY);
  pointZ[0U] = (uint64_t)1U;
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)1U; i0 < len1; i0++)
  {
    pointZ[i0] = (uint64_t)0U;
  }
}

static inline bool isPointOnCurve_p256(uint64_t *p)
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

static inline bool isPointOnCurve_p384(uint64_t *p)
{
  uint32_t sz = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t y2Buffer[sz];
  memset(y2Buffer, 0U, sz * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t xBuffer[sz];
  memset(xBuffer, 0U, sz * sizeof (uint64_t));
  uint64_t *x = p;
  uint64_t *y = p + sz;
  toDomain_p384(y, y2Buffer);
  montgomery_square_buffer_dh_p384(y2Buffer, y2Buffer);
  uint32_t sz1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t xToDomainBuffer[sz1];
  memset(xToDomainBuffer, 0U, sz1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t minusThreeXBuffer[sz1];
  memset(minusThreeXBuffer, 0U, sz1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t b_constant[sz1];
  memset(b_constant, 0U, sz1 * sizeof (uint64_t));
  toDomain_p384(x, xToDomainBuffer);
  montgomery_square_buffer_dh_p384(xToDomainBuffer, xBuffer);
  montgomery_multiplication_buffer_dh_p384(xBuffer, xToDomainBuffer, xBuffer);
  felem_add_p384(xToDomainBuffer, xToDomainBuffer, minusThreeXBuffer);
  felem_add_p384(xToDomainBuffer, minusThreeXBuffer, minusThreeXBuffer);
  felem_sub_p384(xBuffer, minusThreeXBuffer, xBuffer);
  b_constant[0U] = (uint64_t)581395848458481100U;
  b_constant[1U] = (uint64_t)17809957346689692396U;
  b_constant[2U] = (uint64_t)8643006485390950958U;
  b_constant[3U] = (uint64_t)16372638458395724514U;
  b_constant[4U] = (uint64_t)13126622871277412500U;
  b_constant[5U] = (uint64_t)14774077593024970745U;
  felem_add_p384(xBuffer, b_constant, xBuffer);
  uint64_t tmp = (uint64_t)0U;
  tmp = (uint64_t)18446744073709551615U;
  uint32_t len = (uint32_t)6U;
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

static bool verifyQValidCurvePoint_private_p256(uint64_t *pubKey)
{
  uint32_t len0 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len0);
  uint64_t tempBuffer1[len0];
  memset(tempBuffer1, 0U, len0 * sizeof (uint64_t));
  uint64_t *x0 = pubKey;
  uint64_t *y0 = pubKey + len0;
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
  for (uint32_t i = (uint32_t)0U; i < len10 / (uint32_t)4U; i++)
  {
    uint64_t t1 = x0[(uint32_t)4U * i];
    uint64_t t20 = p0[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = x0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = x0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = x0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len10 / (uint32_t)4U * (uint32_t)4U; i < len10; i++)
  {
    uint64_t t1 = x0[i];
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
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = y0[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    uint64_t *res_i0 = tempBuffer1 + (uint32_t)4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = y0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = y0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = y0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / (uint32_t)4U * (uint32_t)4U; i < len1; i++)
  {
    uint64_t t1 = y0[i];
    uint64_t t2 = p[i];
    uint64_t *res_i = tempBuffer1 + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t r0 = c;
  uint64_t carryY = r0;
  uint64_t lessX = FStar_UInt64_eq_mask(carryX, (uint64_t)1U);
  uint64_t lessY = FStar_UInt64_eq_mask(carryY, (uint64_t)1U);
  uint64_t r1 = lessX & lessY;
  bool coordinatesValid = !(r1 == (uint64_t)0U);
  if (!coordinatesValid)
  {
    return false;
  }
  uint32_t sz = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t y2Buffer[sz];
  memset(y2Buffer, 0U, sz * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t xBuffer[sz];
  memset(xBuffer, 0U, sz * sizeof (uint64_t));
  uint64_t *x = pubKey;
  uint64_t *y = pubKey + sz;
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
  uint64_t r2 = tmp;
  bool belongsToCurve = !(r2 == (uint64_t)0U);
  return coordinatesValid && belongsToCurve;
}

static bool verifyQValidCurvePoint_public_p256(uint64_t *pubKey)
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
  for (uint32_t i = (uint32_t)0U; i < len10 / (uint32_t)4U; i++)
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
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  bool belongsToCurve = isPointOnCurve_p256(pubKey);
  return coordinatesValid && belongsToCurve;
}

static bool verifyQValidCurvePoint_public_p384(uint64_t *pubKey)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer1[len];
  memset(tempBuffer1, 0U, len * sizeof (uint64_t));
  uint64_t *x = pubKey;
  uint64_t *y = pubKey + len;
  uint64_t
  p0[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len10 = (uint32_t)6U;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len10 / (uint32_t)4U; i++)
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
  p[6U] =
    {
      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
    };
  uint32_t len1 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < len1 / (uint32_t)4U; i++)
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
  bool belongsToCurve = isPointOnCurve_p384(pubKey);
  return coordinatesValid && belongsToCurve;
}

static const
uint8_t
prime256order_buffer[32U] =
  {
    (uint8_t)79U, (uint8_t)37U, (uint8_t)99U, (uint8_t)252U, (uint8_t)194U, (uint8_t)202U,
    (uint8_t)185U, (uint8_t)243U, (uint8_t)132U, (uint8_t)158U, (uint8_t)23U, (uint8_t)167U,
    (uint8_t)173U, (uint8_t)250U, (uint8_t)230U, (uint8_t)188U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U
  };

static const
uint8_t
prime384order_buffer[48U] =
  {
    (uint8_t)113U, (uint8_t)41U, (uint8_t)197U, (uint8_t)204U, (uint8_t)106U, (uint8_t)25U,
    (uint8_t)236U, (uint8_t)236U, (uint8_t)122U, (uint8_t)167U, (uint8_t)176U, (uint8_t)72U,
    (uint8_t)178U, (uint8_t)13U, (uint8_t)26U, (uint8_t)88U, (uint8_t)223U, (uint8_t)45U,
    (uint8_t)55U, (uint8_t)244U, (uint8_t)129U, (uint8_t)77U, (uint8_t)99U, (uint8_t)199U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U
  };

static inline void montgomery_ladder_exponent_dsa_p256(uint64_t *a, uint64_t *r)
{
  montgomery_ladder_power_p256_dsa(a, prime256order_buffer, r);
}

static inline void montgomery_ladder_exponent_dsa_p384(uint64_t *a, uint64_t *r)
{
  montgomery_ladder_power_p384_dsa(a, prime384order_buffer, r);
}

static void
ecdsa_verification_step5_0_0(
  Spec_ECC_Curves_curve c,
  ladder l,
  uint64_t *points,
  uint64_t *pubKeyAsPoint,
  void *u1,
  void *u2,
  uint64_t *tempBuffer
)
{
  uint64_t *pointU1G = points;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  uint64_t *pointU2Q = points + sw * (uint32_t)3U;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        switch (l)
        {
          case MontLadder:
            {
              secretToPublicWithoutNorm_p256_ml(pointU1G, u1, tempBuffer);
              break;
            }
          case Radix:
            {
              secretToPublicWithoutNorm_p256_radix(pointU1G, u1, tempBuffer);
              break;
            }
          case WNAF:
            {
              secretToPublicWithoutNorm_p256_wnaf(pointU1G, u1, tempBuffer);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        switch (l)
        {
          case MontLadder:
            {
              secretToPublicWithoutNorm_p384_ml(pointU1G, u1, tempBuffer);
              break;
            }
          case Radix:
            {
              secretToPublicWithoutNorm_p384_radix(pointU1G, u1, tempBuffer);
              break;
            }
          case WNAF:
            {
              secretToPublicWithoutNorm_p384_wnaf(pointU1G, u1, tempBuffer);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        switch (l)
        {
          case MontLadder:
            {
              scalarMultiplicationWithoutNorm_p256_ml(pubKeyAsPoint, pointU2Q, u2, tempBuffer);
              break;
            }
          case Radix:
            {
              scalarMultiplicationWithoutNorm_p256_radix(pubKeyAsPoint, pointU2Q, u2, tempBuffer);
              break;
            }
          case WNAF:
            {
              scalarMultiplicationWithoutNorm_p256_radix(pubKeyAsPoint, pointU2Q, u2, tempBuffer);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        switch (l)
        {
          case MontLadder:
            {
              scalarMultiplicationWithoutNorm_p384_ml(pubKeyAsPoint, pointU2Q, u2, tempBuffer);
              break;
            }
          case Radix:
            {
              scalarMultiplicationWithoutNorm_p384_radix(pubKeyAsPoint, pointU2Q, u2, tempBuffer);
              break;
            }
          case WNAF:
            {
              scalarMultiplicationWithoutNorm_p384_radix(pubKeyAsPoint, pointU2Q, u2, tempBuffer);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
ecdsa_verification_step5_0(
  Spec_ECC_Curves_curve c,
  ladder l,
  uint64_t *points,
  uint64_t *pubKeyAsPoint,
  void *u1,
  void *u2,
  uint64_t *tempBuffer
)
{
  ecdsa_verification_step5_0_0(c, l, points, pubKeyAsPoint, u1, u2, tempBuffer);
}

static bool
ecdsa_verification_step45(
  Spec_ECC_Curves_curve c,
  ladder l,
  void *u1,
  void *u2,
  uint64_t *r,
  uint64_t *s,
  uint64_t *hash,
  uint64_t *x,
  uint64_t *pubKeyAsPoint,
  uint64_t *tempBuffer
)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t tempBuffer1[(uint32_t)3U * len];
  memset(tempBuffer1, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint64_t *inverseS = tempBuffer1;
  uint64_t *u11 = tempBuffer1 + len;
  uint64_t *u21 = tempBuffer1 + (uint32_t)2U * len;
  uint32_t len10;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len10 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len10 = (uint32_t)6U;
        break;
      }
    default:
      {
        len10 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t one[len10];
  memset(one, 0U, len10 * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t len20;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len20 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len20 = (uint32_t)6U;
        break;
      }
    default:
      {
        len20 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)1U; i < len20; i++)
  {
    one[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(one, s, inverseS);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(one, s, inverseS);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_ladder_exponent_dsa_p256(inverseS, inverseS);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_ladder_exponent_dsa_p384(inverseS, inverseS);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len11;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len11 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len11 = (uint32_t)6U;
        break;
      }
    default:
      {
        len11 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t buffFromDB[len11];
  memset(buffFromDB, 0U, len11 * sizeof (uint64_t));
  uint32_t len21;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len21 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len21 = (uint32_t)6U;
        break;
      }
    default:
      {
        len21 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len21);
  uint64_t one0[len21];
  memset(one0, 0U, len21 * sizeof (uint64_t));
  one0[0U] = (uint64_t)1U;
  uint32_t len30;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len30 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len30 = (uint32_t)6U;
        break;
      }
    default:
      {
        len30 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)1U; i < len30; i++)
  {
    one0[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(one0, hash, buffFromDB);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(one0, hash, buffFromDB);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len22;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len22 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len22 = (uint32_t)6U;
        break;
      }
    default:
      {
        len22 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t one1[len22];
  memset(one1, 0U, len22 * sizeof (uint64_t));
  one1[0U] = (uint64_t)1U;
  uint32_t len31;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len31 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len31 = (uint32_t)6U;
        break;
      }
    default:
      {
        len31 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)1U; i < len31; i++)
  {
    one1[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(one1, buffFromDB, buffFromDB);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(one1, buffFromDB, buffFromDB);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(inverseS, buffFromDB, u11);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(inverseS, buffFromDB, u11);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len12;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len12 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len12 = (uint32_t)6U;
        break;
      }
    default:
      {
        len12 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len12);
  uint64_t buffFromDB0[len12];
  memset(buffFromDB0, 0U, len12 * sizeof (uint64_t));
  uint32_t len23;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len23 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len23 = (uint32_t)6U;
        break;
      }
    default:
      {
        len23 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len23);
  uint64_t one2[len23];
  memset(one2, 0U, len23 * sizeof (uint64_t));
  one2[0U] = (uint64_t)1U;
  uint32_t len32;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len32 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len32 = (uint32_t)6U;
        break;
      }
    default:
      {
        len32 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)1U; i < len32; i++)
  {
    one2[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(one2, r, buffFromDB0);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(one2, r, buffFromDB0);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len24;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len24 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len24 = (uint32_t)6U;
        break;
      }
    default:
      {
        len24 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len24);
  uint64_t one3[len24];
  memset(one3, 0U, len24 * sizeof (uint64_t));
  one3[0U] = (uint64_t)1U;
  uint32_t len33;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len33 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len33 = (uint32_t)6U;
        break;
      }
    default:
      {
        len33 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)1U; i < len33; i++)
  {
    one3[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(one3, buffFromDB0, buffFromDB0);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(one3, buffFromDB0, buffFromDB0);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dsa_p256(inverseS, buffFromDB0, u21);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dsa_p384(inverseS, buffFromDB0, u21);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len13;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len13 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len13 = (uint32_t)6U;
        break;
      }
    default:
      {
        len13 = (uint32_t)4U;
      }
  }
  uint32_t lenByTwo = len13 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t sw;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw = (uint32_t)6U;
          break;
        }
      default:
        {
          sw = (uint32_t)4U;
        }
    }
    uint32_t lenRight = sw - (uint32_t)1U - i;
    uint64_t left = u11[i];
    uint64_t right = u11[lenRight];
    u11[i] = right;
    u11[lenRight] = left;
  }
  uint32_t len14;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len14 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len14 = (uint32_t)6U;
        break;
      }
    default:
      {
        len14 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len14; i++)
  {
    store64_be((uint8_t *)u1 + i * (uint32_t)8U, u11[i]);
  }
  uint32_t len15;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len15 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len15 = (uint32_t)6U;
        break;
      }
    default:
      {
        len15 = (uint32_t)4U;
      }
  }
  uint32_t lenByTwo0 = len15 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t sw;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw = (uint32_t)6U;
          break;
        }
      default:
        {
          sw = (uint32_t)4U;
        }
    }
    uint32_t lenRight = sw - (uint32_t)1U - i;
    uint64_t left = u21[i];
    uint64_t right = u21[lenRight];
    u21[i] = right;
    u21[lenRight] = left;
  }
  uint32_t len16;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len16 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len16 = (uint32_t)6U;
        break;
      }
    default:
      {
        len16 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len16; i++)
  {
    store64_be((uint8_t *)u2 + i * (uint32_t)8U, u21[i]);
  }
  uint32_t len0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len0 = (uint32_t)6U;
        break;
      }
    default:
      {
        len0 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len0 * (uint32_t)3U);
  uint64_t result[len0 * (uint32_t)3U];
  memset(result, 0U, len0 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len1 = (uint32_t)6U;
        break;
      }
    default:
      {
        len1 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len1 * (uint32_t)6U);
  uint64_t points[len1 * (uint32_t)6U];
  memset(points, 0U, len1 * (uint32_t)6U * sizeof (uint64_t));
  ecdsa_verification_step5_0(c, l, points, pubKeyAsPoint, u1, u2, tempBuffer);
  uint64_t *tempBuffer17 = tempBuffer;
  uint64_t *p = points;
  uint32_t sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw0 = (uint32_t)4U;
      }
  }
  uint64_t *q = points + sw0 * (uint32_t)3U;
  uint32_t len25;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len25 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len25 = (uint32_t)6U;
        break;
      }
    default:
      {
        len25 = (uint32_t)4U;
      }
  }
  uint64_t *zCoordinate = p + (uint32_t)2U * len25;
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len34;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len34 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len34 = (uint32_t)6U;
        break;
      }
    default:
      {
        len34 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len34; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t f = tmp1;
  bool pInfinity = f == (uint64_t)0xffffffffffffffffU;
  uint32_t len26;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len26 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len26 = (uint32_t)6U;
        break;
      }
    default:
      {
        len26 = (uint32_t)4U;
      }
  }
  uint64_t *zCoordinate0 = q + (uint32_t)2U * len26;
  uint64_t tmp2 = (uint64_t)18446744073709551615U;
  uint32_t len35;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len35 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len35 = (uint32_t)6U;
        break;
      }
    default:
      {
        len35 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len35; i++)
  {
    uint64_t a_i = zCoordinate0[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp2;
    tmp2 = r_i & tmp0;
  }
  uint64_t f0 = tmp2;
  bool qInfinity = f0 == (uint64_t)0xffffffffffffffffU;
  if (pInfinity)
  {
    uint32_t sw;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw = (uint32_t)6U;
          break;
        }
      default:
        {
          sw = (uint32_t)4U;
        }
    }
    memcpy(result, q, sw * (uint32_t)3U * sizeof (uint64_t));
  }
  else
  {
    uint32_t len2;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len2 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len2 = (uint32_t)6U;
          break;
        }
      default:
        {
          len2 = (uint32_t)4U;
        }
    }
    uint64_t *sq_z1 = tempBuffer17;
    uint64_t *tr_z1 = tempBuffer17 + len2;
    uint64_t *sq_z2 = tempBuffer17 + (uint32_t)2U * len2;
    uint64_t *tr_z2 = tempBuffer17 + (uint32_t)3U * len2;
    uint64_t *x1 = p;
    uint64_t *y1 = p + len2;
    uint64_t *z1 = p + (uint32_t)2U * len2;
    uint64_t *x2 = q;
    uint64_t *y2 = q + len2;
    uint64_t *z2 = q + (uint32_t)2U * len2;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_square_buffer_dh_p256(z1, sq_z1);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_square_buffer_dh_p384(z1, sq_z1);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_square_buffer_dh_p256(z2, sq_z2);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_square_buffer_dh_p384(z2, sq_z2);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_multiplication_buffer_dh_p256(sq_z1, z1, tr_z1);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_multiplication_buffer_dh_p384(sq_z1, z1, tr_z1);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_multiplication_buffer_dh_p256(sq_z2, z2, tr_z2);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_multiplication_buffer_dh_p384(sq_z2, z2, tr_z2);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_multiplication_buffer_dh_p256(sq_z1, x2, sq_z1);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_multiplication_buffer_dh_p384(sq_z1, x2, sq_z1);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_multiplication_buffer_dh_p256(sq_z2, x1, sq_z2);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_multiplication_buffer_dh_p384(sq_z2, x1, sq_z2);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_multiplication_buffer_dh_p256(tr_z1, y2, tr_z1);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_multiplication_buffer_dh_p384(tr_z1, y2, tr_z1);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          montgomery_multiplication_buffer_dh_p256(tr_z2, y1, tr_z2);
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          montgomery_multiplication_buffer_dh_p384(tr_z2, y1, tr_z2);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    uint64_t tmp3 = (uint64_t)0U;
    tmp3 = (uint64_t)18446744073709551615U;
    uint32_t len36;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len36 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len36 = (uint32_t)6U;
          break;
        }
      default:
        {
          len36 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len36; i++)
    {
      uint64_t a_i = sq_z1[i];
      uint64_t b_i = sq_z2[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
      uint64_t tmp0 = tmp3;
      tmp3 = r_i & tmp0;
    }
    uint64_t equalX = tmp3;
    uint64_t tmp4 = (uint64_t)0U;
    tmp4 = (uint64_t)18446744073709551615U;
    uint32_t len3;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len3 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len3 = (uint32_t)6U;
          break;
        }
      default:
        {
          len3 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t a_i = tr_z1[i];
      uint64_t b_i = tr_z2[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
      uint64_t tmp0 = tmp4;
      tmp4 = r_i & tmp0;
    }
    uint64_t equalY = tmp4;
    uint64_t equal = equalX & equalY;
    bool equal_b = !(equal == (uint64_t)0U);
    if (equal_b)
    {
      uint32_t len27;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            len27 = (uint32_t)4U;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            len27 = (uint32_t)6U;
            break;
          }
        default:
          {
            len27 = (uint32_t)4U;
          }
      }
      uint64_t *pY = p + len27;
      uint64_t *pZ = p + (uint32_t)2U * len27;
      uint64_t *x3 = result;
      uint64_t *y3 = result + len27;
      uint64_t *z3 = result + (uint32_t)2U * len27;
      uint64_t *delta = tempBuffer17;
      uint64_t *gamma = tempBuffer17 + len27;
      uint64_t *beta = tempBuffer17 + (uint32_t)2U * len27;
      uint64_t *alpha = tempBuffer17 + (uint32_t)3U * len27;
      uint64_t *fourBeta = tempBuffer17 + (uint32_t)4U * len27;
      uint64_t *eightBeta = tempBuffer17 + (uint32_t)5U * len27;
      uint64_t *eightGamma = tempBuffer17 + (uint32_t)6U * len27;
      uint64_t *tmp = tempBuffer17 + (uint32_t)7U * len27;
      uint32_t coordinateLen;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            coordinateLen = (uint32_t)4U;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            coordinateLen = (uint32_t)6U;
            break;
          }
        default:
          {
            coordinateLen = (uint32_t)4U;
          }
      }
      uint64_t *pX1 = p;
      uint64_t *pY1 = p + coordinateLen;
      uint64_t *pZ1 = p + (uint32_t)2U * coordinateLen;
      uint64_t *a0 = tmp;
      uint64_t *a1 = tmp + coordinateLen;
      uint64_t *alpha0 = tmp + (uint32_t)2U * coordinateLen;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_square_buffer_dh_p256(pZ1, delta);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_square_buffer_dh_p384(pZ1, delta);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_square_buffer_dh_p256(pY1, gamma);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_square_buffer_dh_p384(pY1, gamma);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_multiplication_buffer_dh_p256(pX1, gamma, beta);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_multiplication_buffer_dh_p384(pX1, gamma, beta);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_sub_p256(pX1, delta, a0);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_sub_p384(pX1, delta, a0);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(pX1, delta, a1);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(pX1, delta, a1);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_multiplication_buffer_dh_p256(a0, a1, alpha0);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_multiplication_buffer_dh_p384(a0, a1, alpha0);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(alpha0, alpha0, alpha);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(alpha0, alpha0, alpha);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(alpha0, alpha, alpha);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(alpha0, alpha, alpha);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_square_buffer_dh_p256(alpha, x3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_square_buffer_dh_p384(alpha, x3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(beta, beta, fourBeta);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(beta, beta, fourBeta);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(fourBeta, fourBeta, fourBeta);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(fourBeta, fourBeta, fourBeta);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(fourBeta, fourBeta, eightBeta);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(fourBeta, fourBeta, eightBeta);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_sub_p256(x3, eightBeta, x3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_sub_p384(x3, eightBeta, x3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(pY, pZ, z3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(pY, pZ, z3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_square_buffer_dh_p256(z3, z3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_square_buffer_dh_p384(z3, z3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_sub_p256(z3, gamma, z3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_sub_p384(z3, gamma, z3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_sub_p256(z3, delta, z3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_sub_p384(z3, delta, z3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_sub_p256(fourBeta, x3, y3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_sub_p384(fourBeta, x3, y3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_multiplication_buffer_dh_p256(alpha, y3, y3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_multiplication_buffer_dh_p384(alpha, y3, y3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            montgomery_square_buffer_dh_p256(gamma, gamma);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            montgomery_square_buffer_dh_p384(gamma, gamma);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(gamma, gamma, eightGamma);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(gamma, gamma, eightGamma);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(eightGamma, eightGamma, eightGamma);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(eightGamma, eightGamma, eightGamma);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_add_p256(eightGamma, eightGamma, eightGamma);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_add_p384(eightGamma, eightGamma, eightGamma);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            felem_sub_p256(y3, eightGamma, y3);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            felem_sub_p384(y3, eightGamma, y3);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
    }
    else
    {
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            point_add_p256(p, q, result, tempBuffer17);
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            point_add_p384(p, q, result, tempBuffer17);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
    }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        norm_p256(result, result, tempBuffer17);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        norm_p384(result, result, tempBuffer17);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len17;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len17 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len17 = (uint32_t)6U;
        break;
      }
    default:
      {
        len17 = (uint32_t)4U;
      }
  }
  uint64_t *zCoordinate1 = result + (uint32_t)2U * len17;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len2 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len2 = (uint32_t)6U;
        break;
      }
    default:
      {
        len2 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate1[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t f1 = tmp;
  bool resultIsPAI = f1 == (uint64_t)0xffffffffffffffffU;
  uint64_t *xCoordinateSum = result;
  uint32_t sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = (uint32_t)6U;
        break;
      }
    default:
      {
        sw = (uint32_t)4U;
      }
  }
  memcpy(x, xCoordinateSum, sw * sizeof (uint64_t));
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        reduction_prime_2prime_order_p256(x, x);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        reduction_prime_2prime_order_p384(x, x);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  return !resultIsPAI;
}

static void
computeYFromX(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *result, uint64_t sign)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t aCoordinateBuffer[len];
  memset(aCoordinateBuffer, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t bCoordinateBuffer[len];
  memset(bCoordinateBuffer, 0U, len * sizeof (uint64_t));
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        aCoordinateBuffer[0U] = (uint64_t)18446744073709551612U;
        aCoordinateBuffer[1U] = (uint64_t)17179869183U;
        aCoordinateBuffer[2U] = (uint64_t)0U;
        aCoordinateBuffer[3U] = (uint64_t)18446744056529682436U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        aCoordinateBuffer[0U] = (uint64_t)0x3fffffffcU;
        aCoordinateBuffer[1U] = (uint64_t)0xfffffffc00000000U;
        aCoordinateBuffer[2U] = (uint64_t)0xfffffffffffffffbU;
        aCoordinateBuffer[3U] = (uint64_t)0xffffffffffffffffU;
        aCoordinateBuffer[4U] = (uint64_t)0xffffffffffffffffU;
        aCoordinateBuffer[5U] = (uint64_t)0xffffffffffffffffU;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        bCoordinateBuffer[0U] = (uint64_t)15608596021259845087U;
        bCoordinateBuffer[1U] = (uint64_t)12461466548982526096U;
        bCoordinateBuffer[2U] = (uint64_t)16546823903870267094U;
        bCoordinateBuffer[3U] = (uint64_t)15866188208926050356U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        bCoordinateBuffer[0U] = (uint64_t)0x81188719d412dccU;
        bCoordinateBuffer[1U] = (uint64_t)0xf729add87a4c32ecU;
        bCoordinateBuffer[2U] = (uint64_t)0x77f2209b1920022eU;
        bCoordinateBuffer[3U] = (uint64_t)0xe3374bee94938ae2U;
        bCoordinateBuffer[4U] = (uint64_t)0xb62b21f41f022094U;
        bCoordinateBuffer[5U] = (uint64_t)0xcd08114b604fbff9U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(aCoordinateBuffer, x, aCoordinateBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(aCoordinateBuffer, x, aCoordinateBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_square_buffer_dh_p256(x, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_square_buffer_dh_p384(x, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(result, x, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(result, x, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_add_p256(result, aCoordinateBuffer, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_add_p384(result, aCoordinateBuffer, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_add_p256(result, bCoordinateBuffer, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_add_p384(result, bCoordinateBuffer, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t len1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len1 = (uint32_t)6U;
        break;
      }
    default:
      {
        len1 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    aCoordinateBuffer[i] = (uint64_t)0U;
  }
  square_root(c, result, result);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        fromDomain_p256(result, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        fromDomain_p384(result, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_sub_p256(aCoordinateBuffer, result, bCoordinateBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_sub_p384(aCoordinateBuffer, result, bCoordinateBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t word = result[0U];
  uint64_t bitToCheck = word & (uint64_t)1U;
  uint64_t flag = FStar_UInt64_eq_mask(bitToCheck, sign);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        cmovznz4_p256(flag, bCoordinateBuffer, result, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        cmovznz4_p384(flag, bCoordinateBuffer, result, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t r[len];
  memset(r, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t s[len];
  memset(s, 0U, len * sizeof (uint64_t));
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  uint64_t privKeyAsFelem[4U] = { 0U };
  toUint64ChangeEndian_p256(privKey, privKeyAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len10);
  uint64_t tempBuffer[(uint32_t)20U * len10];
  memset(tempBuffer, 0U, (uint32_t)20U * len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t kAsFelem[len10];
  memset(kAsFelem, 0U, len10 * sizeof (uint64_t));
  toUint64ChangeEndian_p256(k, kAsFelem);
  uint32_t sz_hash = (uint32_t)32U;
  uint32_t len20 = sz_hash + (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), len20);
  uint8_t mHash[len20];
  memset(mHash, 0U, len20 * sizeof (uint8_t));
  uint8_t *mHashHPart = mHash;
  uint8_t *mHashRPart = mHash;
  Hacl_Hash_SHA2_hash_256(m, mLen, mHashHPart);
  toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
  reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
  uint32_t len21 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len21);
  uint64_t result1[(uint32_t)3U * len21];
  memset(result1, 0U, (uint32_t)3U * len21 * sizeof (uint64_t));
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm_p256_ml(result1, (void *)k, tempBuffer);
  uint64_t *xf = result1;
  uint64_t *zf = result1 + (uint32_t)8U;
  uint64_t *z2f = tempForNorm + (uint32_t)4U;
  uint64_t *t8 = tempForNorm + (uint32_t)3U * (uint32_t)4U;
  montgomery_square_buffer_dh_p256(zf, z2f);
  exponent_p256(z2f, z2f, t8);
  montgomery_multiplication_buffer_dh_p256(z2f, xf, z2f);
  fromDomain_p256(z2f, r);
  reduction_prime_2prime_order_p256(r, r);
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len30; i++)
  {
    uint64_t a_i = r[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t step5Flag = tmp;
  uint32_t len22 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t rda[len22];
  memset(rda, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t zBuffer[len22];
  memset(zBuffer, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t kInv[len22];
  memset(kInv, 0U, len22 * sizeof (uint64_t));
  montgomery_multiplication_buffer_dsa_p256(r, privKeyAsFelem, rda);
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t one[len3];
  memset(one, 0U, len3 * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len4; i++)
  {
    one[i] = (uint64_t)0U;
  }
  montgomery_multiplication_buffer_dsa_p256(one, hashAsFelem, zBuffer);
  felem_add_ecdsa_P256(rda, zBuffer, zBuffer);
  memcpy(kInv, kAsFelem, len22 * sizeof (uint64_t));
  montgomery_ladder_exponent_dsa_p256(kInv, kInv);
  montgomery_multiplication_buffer_dsa_p256(zBuffer, kInv, s);
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = s[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t sIsZero = tmp1;
  uint64_t flagU64 = step5Flag | sIsZero;
  bool flag = flagU64 == (uint64_t)0U;
  uint32_t len1 = (uint32_t)4U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = r[i];
    uint64_t right = r[lenRight];
    r[i] = right;
    r[lenRight] = left;
  }
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    store64_be(resultR + i * (uint32_t)8U, r[i]);
  }
  uint32_t len12 = (uint32_t)4U;
  uint32_t lenByTwo0 = len12 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = s[i];
    uint64_t right = s[lenRight];
    s[i] = right;
    s[lenRight] = left;
  }
  uint32_t len13 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len13; i++)
  {
    store64_be(resultS + i * (uint32_t)8U, s[i]);
  }
  return flag;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t r[len];
  memset(r, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t s[len];
  memset(s, 0U, len * sizeof (uint64_t));
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  uint64_t privKeyAsFelem[4U] = { 0U };
  toUint64ChangeEndian_p256(privKey, privKeyAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len10);
  uint64_t tempBuffer[(uint32_t)20U * len10];
  memset(tempBuffer, 0U, (uint32_t)20U * len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t kAsFelem[len10];
  memset(kAsFelem, 0U, len10 * sizeof (uint64_t));
  toUint64ChangeEndian_p256(k, kAsFelem);
  uint32_t sz_hash = (uint32_t)48U;
  uint32_t len20 = sz_hash + (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), len20);
  uint8_t mHash[len20];
  memset(mHash, 0U, len20 * sizeof (uint8_t));
  uint8_t *mHashHPart = mHash;
  uint8_t *mHashRPart = mHash;
  Hacl_Hash_SHA2_hash_384(m, mLen, mHashHPart);
  toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
  reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
  uint32_t len21 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len21);
  uint64_t result1[(uint32_t)3U * len21];
  memset(result1, 0U, (uint32_t)3U * len21 * sizeof (uint64_t));
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm_p256_ml(result1, (void *)k, tempBuffer);
  uint64_t *xf = result1;
  uint64_t *zf = result1 + (uint32_t)8U;
  uint64_t *z2f = tempForNorm + (uint32_t)4U;
  uint64_t *t8 = tempForNorm + (uint32_t)3U * (uint32_t)4U;
  montgomery_square_buffer_dh_p256(zf, z2f);
  exponent_p256(z2f, z2f, t8);
  montgomery_multiplication_buffer_dh_p256(z2f, xf, z2f);
  fromDomain_p256(z2f, r);
  reduction_prime_2prime_order_p256(r, r);
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len30; i++)
  {
    uint64_t a_i = r[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t step5Flag = tmp;
  uint32_t len22 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t rda[len22];
  memset(rda, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t zBuffer[len22];
  memset(zBuffer, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t kInv[len22];
  memset(kInv, 0U, len22 * sizeof (uint64_t));
  montgomery_multiplication_buffer_dsa_p256(r, privKeyAsFelem, rda);
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t one[len3];
  memset(one, 0U, len3 * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len4; i++)
  {
    one[i] = (uint64_t)0U;
  }
  montgomery_multiplication_buffer_dsa_p256(one, hashAsFelem, zBuffer);
  felem_add_ecdsa_P256(rda, zBuffer, zBuffer);
  memcpy(kInv, kAsFelem, len22 * sizeof (uint64_t));
  montgomery_ladder_exponent_dsa_p256(kInv, kInv);
  montgomery_multiplication_buffer_dsa_p256(zBuffer, kInv, s);
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = s[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t sIsZero = tmp1;
  uint64_t flagU64 = step5Flag | sIsZero;
  bool flag = flagU64 == (uint64_t)0U;
  uint32_t len1 = (uint32_t)4U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = r[i];
    uint64_t right = r[lenRight];
    r[i] = right;
    r[lenRight] = left;
  }
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    store64_be(resultR + i * (uint32_t)8U, r[i]);
  }
  uint32_t len12 = (uint32_t)4U;
  uint32_t lenByTwo0 = len12 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = s[i];
    uint64_t right = s[lenRight];
    s[i] = right;
    s[lenRight] = left;
  }
  uint32_t len13 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len13; i++)
  {
    store64_be(resultS + i * (uint32_t)8U, s[i]);
  }
  return flag;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t r[len];
  memset(r, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t s[len];
  memset(s, 0U, len * sizeof (uint64_t));
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  uint64_t privKeyAsFelem[4U] = { 0U };
  toUint64ChangeEndian_p256(privKey, privKeyAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len10);
  uint64_t tempBuffer[(uint32_t)20U * len10];
  memset(tempBuffer, 0U, (uint32_t)20U * len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t kAsFelem[len10];
  memset(kAsFelem, 0U, len10 * sizeof (uint64_t));
  toUint64ChangeEndian_p256(k, kAsFelem);
  uint32_t sz_hash = (uint32_t)64U;
  uint32_t len20 = sz_hash + (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), len20);
  uint8_t mHash[len20];
  memset(mHash, 0U, len20 * sizeof (uint8_t));
  uint8_t *mHashHPart = mHash;
  uint8_t *mHashRPart = mHash;
  Hacl_Hash_SHA2_hash_512(m, mLen, mHashHPart);
  toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
  reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
  uint32_t len21 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len21);
  uint64_t result1[(uint32_t)3U * len21];
  memset(result1, 0U, (uint32_t)3U * len21 * sizeof (uint64_t));
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm_p256_ml(result1, (void *)k, tempBuffer);
  uint64_t *xf = result1;
  uint64_t *zf = result1 + (uint32_t)8U;
  uint64_t *z2f = tempForNorm + (uint32_t)4U;
  uint64_t *t8 = tempForNorm + (uint32_t)3U * (uint32_t)4U;
  montgomery_square_buffer_dh_p256(zf, z2f);
  exponent_p256(z2f, z2f, t8);
  montgomery_multiplication_buffer_dh_p256(z2f, xf, z2f);
  fromDomain_p256(z2f, r);
  reduction_prime_2prime_order_p256(r, r);
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len30; i++)
  {
    uint64_t a_i = r[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t step5Flag = tmp;
  uint32_t len22 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t rda[len22];
  memset(rda, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t zBuffer[len22];
  memset(zBuffer, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t kInv[len22];
  memset(kInv, 0U, len22 * sizeof (uint64_t));
  montgomery_multiplication_buffer_dsa_p256(r, privKeyAsFelem, rda);
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t one[len3];
  memset(one, 0U, len3 * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len4; i++)
  {
    one[i] = (uint64_t)0U;
  }
  montgomery_multiplication_buffer_dsa_p256(one, hashAsFelem, zBuffer);
  felem_add_ecdsa_P256(rda, zBuffer, zBuffer);
  memcpy(kInv, kAsFelem, len22 * sizeof (uint64_t));
  montgomery_ladder_exponent_dsa_p256(kInv, kInv);
  montgomery_multiplication_buffer_dsa_p256(zBuffer, kInv, s);
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = s[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t sIsZero = tmp1;
  uint64_t flagU64 = step5Flag | sIsZero;
  bool flag = flagU64 == (uint64_t)0U;
  uint32_t len1 = (uint32_t)4U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = r[i];
    uint64_t right = r[lenRight];
    r[i] = right;
    r[lenRight] = left;
  }
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    store64_be(resultR + i * (uint32_t)8U, r[i]);
  }
  uint32_t len12 = (uint32_t)4U;
  uint32_t lenByTwo0 = len12 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = s[i];
    uint64_t right = s[lenRight];
    s[i] = right;
    s[lenRight] = left;
  }
  uint32_t len13 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len13; i++)
  {
    store64_be(resultS + i * (uint32_t)8U, s[i]);
  }
  return flag;
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order. 
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_sign_p256_without_hash(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t r[len];
  memset(r, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t s[len];
  memset(s, 0U, len * sizeof (uint64_t));
  uint8_t *resultR = result;
  uint8_t *resultS = result + (uint32_t)32U;
  uint64_t privKeyAsFelem[4U] = { 0U };
  toUint64ChangeEndian_p256(privKey, privKeyAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len10);
  uint64_t tempBuffer[(uint32_t)20U * len10];
  memset(tempBuffer, 0U, (uint32_t)20U * len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t kAsFelem[len10];
  memset(kAsFelem, 0U, len10 * sizeof (uint64_t));
  toUint64ChangeEndian_p256(k, kAsFelem);
  uint32_t sz_hash = mLen;
  uint32_t len20 = sz_hash + (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), len20);
  uint8_t mHash[len20];
  memset(mHash, 0U, len20 * sizeof (uint8_t));
  uint8_t *mHashHPart = mHash;
  uint8_t *mHashRPart = mHash;
  memcpy(mHashHPart, m, sz_hash * sizeof (uint8_t));
  toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
  reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
  uint32_t len21 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len21);
  uint64_t result1[(uint32_t)3U * len21];
  memset(result1, 0U, (uint32_t)3U * len21 * sizeof (uint64_t));
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm_p256_ml(result1, (void *)k, tempBuffer);
  uint64_t *xf = result1;
  uint64_t *zf = result1 + (uint32_t)8U;
  uint64_t *z2f = tempForNorm + (uint32_t)4U;
  uint64_t *t8 = tempForNorm + (uint32_t)3U * (uint32_t)4U;
  montgomery_square_buffer_dh_p256(zf, z2f);
  exponent_p256(z2f, z2f, t8);
  montgomery_multiplication_buffer_dh_p256(z2f, xf, z2f);
  fromDomain_p256(z2f, r);
  reduction_prime_2prime_order_p256(r, r);
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len30; i++)
  {
    uint64_t a_i = r[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t step5Flag = tmp;
  uint32_t len22 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t rda[len22];
  memset(rda, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t zBuffer[len22];
  memset(zBuffer, 0U, len22 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len22);
  uint64_t kInv[len22];
  memset(kInv, 0U, len22 * sizeof (uint64_t));
  montgomery_multiplication_buffer_dsa_p256(r, privKeyAsFelem, rda);
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t one[len3];
  memset(one, 0U, len3 * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len4; i++)
  {
    one[i] = (uint64_t)0U;
  }
  montgomery_multiplication_buffer_dsa_p256(one, hashAsFelem, zBuffer);
  felem_add_ecdsa_P256(rda, zBuffer, zBuffer);
  memcpy(kInv, kAsFelem, len22 * sizeof (uint64_t));
  montgomery_ladder_exponent_dsa_p256(kInv, kInv);
  montgomery_multiplication_buffer_dsa_p256(zBuffer, kInv, s);
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = s[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t sIsZero = tmp1;
  uint64_t flagU64 = step5Flag | sIsZero;
  bool flag = flagU64 == (uint64_t)0U;
  uint32_t len1 = (uint32_t)4U;
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = r[i];
    uint64_t right = r[lenRight];
    r[i] = right;
    r[lenRight] = left;
  }
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    store64_be(resultR + i * (uint32_t)8U, r[i]);
  }
  uint32_t len12 = (uint32_t)4U;
  uint32_t lenByTwo0 = len12 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = s[i];
    uint64_t right = s[lenRight];
    s[i] = right;
    s[lenRight] = left;
  }
  uint32_t len13 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len13; i++)
  {
    store64_be(resultS + i * (uint32_t)8U, s[i]);
  }
  return flag;
}

/*
 This code is not side-channel resistant.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tempBuffer[(uint32_t)4U * len];
  memset(tempBuffer, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  uint64_t *publicKeyAsFelem = tempBuffer;
  uint64_t *rAsFelem = tempBuffer + (uint32_t)2U * len;
  uint64_t *sAsFelem = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len1;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  toUint64ChangeEndian_p256(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian_p256(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian_p256(r, rAsFelem);
  toUint64ChangeEndian_p256(s, sAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)20U);
  uint64_t tempBuffer1[len10 * (uint32_t)20U];
  memset(tempBuffer1, 0U, len10 * (uint32_t)20U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t x[len10];
  memset(x, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)3U);
  uint64_t publicKeyBuffer[len10 * (uint32_t)3U];
  memset(publicKeyBuffer, 0U, len10 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len20 = (uint32_t)4U;
  uint32_t lengthXY = len20 * (uint32_t)2U;
  uint64_t *partPoint = publicKeyBuffer;
  uint64_t *zCoordinate = publicKeyBuffer + lengthXY;
  memcpy(partPoint, publicKeyAsFelem, lengthXY * sizeof (uint64_t));
  zCoordinate[0U] = (uint64_t)1U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len30; i++)
  {
    zCoordinate[i] = (uint64_t)0U;
  }
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(publicKeyBuffer);
  bool r1;
  if (publicKeyCorrect == false)
  {
    r1 = false;
  }
  else
  {
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len21);
    uint64_t tempBuffer2[len21];
    memset(tempBuffer2, 0U, len21 * sizeof (uint64_t));
    uint64_t
    p0[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len31 = (uint32_t)4U;
    uint64_t c0 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
    {
      uint64_t t1 = rAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p0[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer2 + (uint32_t)4U * i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
      uint64_t t10 = rAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)1U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
      uint64_t t11 = rAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)2U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
      uint64_t t12 = rAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer2 + (uint32_t)4U * i + (uint32_t)3U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
    }
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
    {
      uint64_t t1 = rAsFelem[i];
      uint64_t t2 = p0[i];
      uint64_t *res_i = tempBuffer2 + i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
    }
    uint64_t r10 = c0;
    uint64_t carry = r10;
    bool less = carry == (uint64_t)1U;
    uint64_t tmp1 = (uint64_t)18446744073709551615U;
    uint32_t len32 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len32; i++)
    {
      uint64_t a_i = rAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp1;
      tmp1 = r_i & tmp0;
    }
    uint64_t f = tmp1;
    bool more = f == (uint64_t)0xffffffffffffffffU;
    bool isRCorrect = less && !more;
    uint32_t len2 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len2);
    uint64_t tempBuffer20[len2];
    memset(tempBuffer20, 0U, len2 * sizeof (uint64_t));
    uint64_t
    p[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len33 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len33 / (uint32_t)4U; i++)
    {
      uint64_t t1 = sAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer20 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      uint64_t t10 = sAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
      uint64_t t11 = sAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
      uint64_t t12 = sAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer20 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
    }
    for (uint32_t i = len33 / (uint32_t)4U * (uint32_t)4U; i < len33; i++)
    {
      uint64_t t1 = sAsFelem[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer20 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
    uint64_t r11 = c;
    uint64_t carry0 = r11;
    bool less0 = carry0 == (uint64_t)1U;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t a_i = sAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t f0 = tmp;
    bool more0 = f0 == (uint64_t)0xffffffffffffffffU;
    bool isSCorrect = less0 && !more0;
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      r1 = false;
    }
    else
    {
      uint32_t len22 = (uint32_t)4U * (uint32_t)8U;
      KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * len22);
      uint8_t tempBufferU8[(uint32_t)2U * len22];
      memset(tempBufferU8, 0U, (uint32_t)2U * len22 * sizeof (uint8_t));
      void *u1 = (void *)tempBufferU8;
      void *u2 = (void *)(tempBufferU8 + len22);
      uint32_t sz_hash = (uint32_t)32U;
      uint32_t len34 = sz_hash + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len34);
      uint8_t mHash[len34];
      memset(mHash, 0U, len34 * sizeof (uint8_t));
      uint8_t *mHashHPart = mHash;
      uint8_t *mHashRPart = mHash;
      Hacl_Hash_SHA2_hash_256(m, mLen, mHashHPart);
      toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
      reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
      bool
      r12 =
        ecdsa_verification_step45(Spec_ECC_Curves_P256,
          MontLadder,
          u1,
          u2,
          rAsFelem,
          sAsFelem,
          hashAsFelem,
          x,
          publicKeyBuffer,
          tempBuffer1);
      bool state = r12;
      if (state == false)
      {
        r1 = false;
      }
      else
      {
        r1 = cmp_felem_felem_bool_p256(x, rAsFelem);
      }
    }
  }
  bool result = r1;
  return result;
}

/*
 This code is not side-channel resistant.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tempBuffer[(uint32_t)4U * len];
  memset(tempBuffer, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  uint64_t *publicKeyAsFelem = tempBuffer;
  uint64_t *rAsFelem = tempBuffer + (uint32_t)2U * len;
  uint64_t *sAsFelem = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len1;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  toUint64ChangeEndian_p256(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian_p256(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian_p256(r, rAsFelem);
  toUint64ChangeEndian_p256(s, sAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)20U);
  uint64_t tempBuffer1[len10 * (uint32_t)20U];
  memset(tempBuffer1, 0U, len10 * (uint32_t)20U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t x[len10];
  memset(x, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)3U);
  uint64_t publicKeyBuffer[len10 * (uint32_t)3U];
  memset(publicKeyBuffer, 0U, len10 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len20 = (uint32_t)4U;
  uint32_t lengthXY = len20 * (uint32_t)2U;
  uint64_t *partPoint = publicKeyBuffer;
  uint64_t *zCoordinate = publicKeyBuffer + lengthXY;
  memcpy(partPoint, publicKeyAsFelem, lengthXY * sizeof (uint64_t));
  zCoordinate[0U] = (uint64_t)1U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len30; i++)
  {
    zCoordinate[i] = (uint64_t)0U;
  }
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(publicKeyBuffer);
  bool r1;
  if (publicKeyCorrect == false)
  {
    r1 = false;
  }
  else
  {
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len21);
    uint64_t tempBuffer2[len21];
    memset(tempBuffer2, 0U, len21 * sizeof (uint64_t));
    uint64_t
    p0[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len31 = (uint32_t)4U;
    uint64_t c0 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
    {
      uint64_t t1 = rAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p0[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer2 + (uint32_t)4U * i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
      uint64_t t10 = rAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)1U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
      uint64_t t11 = rAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)2U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
      uint64_t t12 = rAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer2 + (uint32_t)4U * i + (uint32_t)3U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
    }
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
    {
      uint64_t t1 = rAsFelem[i];
      uint64_t t2 = p0[i];
      uint64_t *res_i = tempBuffer2 + i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
    }
    uint64_t r10 = c0;
    uint64_t carry = r10;
    bool less = carry == (uint64_t)1U;
    uint64_t tmp1 = (uint64_t)18446744073709551615U;
    uint32_t len32 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len32; i++)
    {
      uint64_t a_i = rAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp1;
      tmp1 = r_i & tmp0;
    }
    uint64_t f = tmp1;
    bool more = f == (uint64_t)0xffffffffffffffffU;
    bool isRCorrect = less && !more;
    uint32_t len2 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len2);
    uint64_t tempBuffer20[len2];
    memset(tempBuffer20, 0U, len2 * sizeof (uint64_t));
    uint64_t
    p[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len33 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len33 / (uint32_t)4U; i++)
    {
      uint64_t t1 = sAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer20 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      uint64_t t10 = sAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
      uint64_t t11 = sAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
      uint64_t t12 = sAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer20 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
    }
    for (uint32_t i = len33 / (uint32_t)4U * (uint32_t)4U; i < len33; i++)
    {
      uint64_t t1 = sAsFelem[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer20 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
    uint64_t r11 = c;
    uint64_t carry0 = r11;
    bool less0 = carry0 == (uint64_t)1U;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t a_i = sAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t f0 = tmp;
    bool more0 = f0 == (uint64_t)0xffffffffffffffffU;
    bool isSCorrect = less0 && !more0;
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      r1 = false;
    }
    else
    {
      uint32_t len22 = (uint32_t)4U * (uint32_t)8U;
      KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * len22);
      uint8_t tempBufferU8[(uint32_t)2U * len22];
      memset(tempBufferU8, 0U, (uint32_t)2U * len22 * sizeof (uint8_t));
      void *u1 = (void *)tempBufferU8;
      void *u2 = (void *)(tempBufferU8 + len22);
      uint32_t sz_hash = (uint32_t)48U;
      uint32_t len34 = sz_hash + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len34);
      uint8_t mHash[len34];
      memset(mHash, 0U, len34 * sizeof (uint8_t));
      uint8_t *mHashHPart = mHash;
      uint8_t *mHashRPart = mHash;
      Hacl_Hash_SHA2_hash_384(m, mLen, mHashHPart);
      toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
      reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
      bool
      r12 =
        ecdsa_verification_step45(Spec_ECC_Curves_P256,
          MontLadder,
          u1,
          u2,
          rAsFelem,
          sAsFelem,
          hashAsFelem,
          x,
          publicKeyBuffer,
          tempBuffer1);
      bool state = r12;
      if (state == false)
      {
        r1 = false;
      }
      else
      {
        r1 = cmp_felem_felem_bool_p256(x, rAsFelem);
      }
    }
  }
  bool result = r1;
  return result;
}

/*
 This code is not side-channel resistant.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tempBuffer[(uint32_t)4U * len];
  memset(tempBuffer, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  uint64_t *publicKeyAsFelem = tempBuffer;
  uint64_t *rAsFelem = tempBuffer + (uint32_t)2U * len;
  uint64_t *sAsFelem = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len1;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  toUint64ChangeEndian_p256(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian_p256(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian_p256(r, rAsFelem);
  toUint64ChangeEndian_p256(s, sAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)20U);
  uint64_t tempBuffer1[len10 * (uint32_t)20U];
  memset(tempBuffer1, 0U, len10 * (uint32_t)20U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t x[len10];
  memset(x, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)3U);
  uint64_t publicKeyBuffer[len10 * (uint32_t)3U];
  memset(publicKeyBuffer, 0U, len10 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len20 = (uint32_t)4U;
  uint32_t lengthXY = len20 * (uint32_t)2U;
  uint64_t *partPoint = publicKeyBuffer;
  uint64_t *zCoordinate = publicKeyBuffer + lengthXY;
  memcpy(partPoint, publicKeyAsFelem, lengthXY * sizeof (uint64_t));
  zCoordinate[0U] = (uint64_t)1U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len30; i++)
  {
    zCoordinate[i] = (uint64_t)0U;
  }
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(publicKeyBuffer);
  bool r1;
  if (publicKeyCorrect == false)
  {
    r1 = false;
  }
  else
  {
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len21);
    uint64_t tempBuffer2[len21];
    memset(tempBuffer2, 0U, len21 * sizeof (uint64_t));
    uint64_t
    p0[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len31 = (uint32_t)4U;
    uint64_t c0 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
    {
      uint64_t t1 = rAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p0[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer2 + (uint32_t)4U * i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
      uint64_t t10 = rAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)1U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
      uint64_t t11 = rAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)2U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
      uint64_t t12 = rAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer2 + (uint32_t)4U * i + (uint32_t)3U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
    }
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
    {
      uint64_t t1 = rAsFelem[i];
      uint64_t t2 = p0[i];
      uint64_t *res_i = tempBuffer2 + i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
    }
    uint64_t r10 = c0;
    uint64_t carry = r10;
    bool less = carry == (uint64_t)1U;
    uint64_t tmp1 = (uint64_t)18446744073709551615U;
    uint32_t len32 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len32; i++)
    {
      uint64_t a_i = rAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp1;
      tmp1 = r_i & tmp0;
    }
    uint64_t f = tmp1;
    bool more = f == (uint64_t)0xffffffffffffffffU;
    bool isRCorrect = less && !more;
    uint32_t len2 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len2);
    uint64_t tempBuffer20[len2];
    memset(tempBuffer20, 0U, len2 * sizeof (uint64_t));
    uint64_t
    p[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len33 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len33 / (uint32_t)4U; i++)
    {
      uint64_t t1 = sAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer20 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      uint64_t t10 = sAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
      uint64_t t11 = sAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
      uint64_t t12 = sAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer20 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
    }
    for (uint32_t i = len33 / (uint32_t)4U * (uint32_t)4U; i < len33; i++)
    {
      uint64_t t1 = sAsFelem[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer20 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
    uint64_t r11 = c;
    uint64_t carry0 = r11;
    bool less0 = carry0 == (uint64_t)1U;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t a_i = sAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t f0 = tmp;
    bool more0 = f0 == (uint64_t)0xffffffffffffffffU;
    bool isSCorrect = less0 && !more0;
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      r1 = false;
    }
    else
    {
      uint32_t len22 = (uint32_t)4U * (uint32_t)8U;
      KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * len22);
      uint8_t tempBufferU8[(uint32_t)2U * len22];
      memset(tempBufferU8, 0U, (uint32_t)2U * len22 * sizeof (uint8_t));
      void *u1 = (void *)tempBufferU8;
      void *u2 = (void *)(tempBufferU8 + len22);
      uint32_t sz_hash = (uint32_t)64U;
      uint32_t len34 = sz_hash + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len34);
      uint8_t mHash[len34];
      memset(mHash, 0U, len34 * sizeof (uint8_t));
      uint8_t *mHashHPart = mHash;
      uint8_t *mHashRPart = mHash;
      Hacl_Hash_SHA2_hash_512(m, mLen, mHashHPart);
      toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
      reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
      bool
      r12 =
        ecdsa_verification_step45(Spec_ECC_Curves_P256,
          MontLadder,
          u1,
          u2,
          rAsFelem,
          sAsFelem,
          hashAsFelem,
          x,
          publicKeyBuffer,
          tempBuffer1);
      bool state = r12;
      if (state == false)
      {
        r1 = false;
      }
      else
      {
        r1 = cmp_felem_felem_bool_p256(x, rAsFelem);
      }
    }
  }
  bool result = r1;
  return result;
}

/*
This code is not side-channel resistant.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification.
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_verif_without_hash_ml(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tempBuffer[(uint32_t)4U * len];
  memset(tempBuffer, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  uint64_t *publicKeyAsFelem = tempBuffer;
  uint64_t *rAsFelem = tempBuffer + (uint32_t)2U * len;
  uint64_t *sAsFelem = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len1;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  toUint64ChangeEndian_p256(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian_p256(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian_p256(r, rAsFelem);
  toUint64ChangeEndian_p256(s, sAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)20U);
  uint64_t tempBuffer1[len10 * (uint32_t)20U];
  memset(tempBuffer1, 0U, len10 * (uint32_t)20U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t x[len10];
  memset(x, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)3U);
  uint64_t publicKeyBuffer[len10 * (uint32_t)3U];
  memset(publicKeyBuffer, 0U, len10 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len20 = (uint32_t)4U;
  uint32_t lengthXY = len20 * (uint32_t)2U;
  uint64_t *partPoint = publicKeyBuffer;
  uint64_t *zCoordinate = publicKeyBuffer + lengthXY;
  memcpy(partPoint, publicKeyAsFelem, lengthXY * sizeof (uint64_t));
  zCoordinate[0U] = (uint64_t)1U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len30; i++)
  {
    zCoordinate[i] = (uint64_t)0U;
  }
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(publicKeyBuffer);
  bool r1;
  if (publicKeyCorrect == false)
  {
    r1 = false;
  }
  else
  {
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len21);
    uint64_t tempBuffer2[len21];
    memset(tempBuffer2, 0U, len21 * sizeof (uint64_t));
    uint64_t
    p0[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len31 = (uint32_t)4U;
    uint64_t c0 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
    {
      uint64_t t1 = rAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p0[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer2 + (uint32_t)4U * i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
      uint64_t t10 = rAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)1U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
      uint64_t t11 = rAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)2U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
      uint64_t t12 = rAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer2 + (uint32_t)4U * i + (uint32_t)3U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
    }
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
    {
      uint64_t t1 = rAsFelem[i];
      uint64_t t2 = p0[i];
      uint64_t *res_i = tempBuffer2 + i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
    }
    uint64_t r10 = c0;
    uint64_t carry = r10;
    bool less = carry == (uint64_t)1U;
    uint64_t tmp1 = (uint64_t)18446744073709551615U;
    uint32_t len32 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len32; i++)
    {
      uint64_t a_i = rAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp1;
      tmp1 = r_i & tmp0;
    }
    uint64_t f = tmp1;
    bool more = f == (uint64_t)0xffffffffffffffffU;
    bool isRCorrect = less && !more;
    uint32_t len2 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len2);
    uint64_t tempBuffer20[len2];
    memset(tempBuffer20, 0U, len2 * sizeof (uint64_t));
    uint64_t
    p[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len33 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len33 / (uint32_t)4U; i++)
    {
      uint64_t t1 = sAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer20 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      uint64_t t10 = sAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
      uint64_t t11 = sAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
      uint64_t t12 = sAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer20 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
    }
    for (uint32_t i = len33 / (uint32_t)4U * (uint32_t)4U; i < len33; i++)
    {
      uint64_t t1 = sAsFelem[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer20 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
    uint64_t r11 = c;
    uint64_t carry0 = r11;
    bool less0 = carry0 == (uint64_t)1U;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len34 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len34; i++)
    {
      uint64_t a_i = sAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t f0 = tmp;
    bool more0 = f0 == (uint64_t)0xffffffffffffffffU;
    bool isSCorrect = less0 && !more0;
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      r1 = false;
    }
    else
    {
      uint32_t len22 = (uint32_t)4U * (uint32_t)8U;
      KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * len22);
      uint8_t tempBufferU8[(uint32_t)2U * len22];
      memset(tempBufferU8, 0U, (uint32_t)2U * len22 * sizeof (uint8_t));
      void *u1 = (void *)tempBufferU8;
      void *u2 = (void *)(tempBufferU8 + len22);
      uint32_t sz_hash = mLen;
      uint32_t len3 = sz_hash + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len3);
      uint8_t mHash[len3];
      memset(mHash, 0U, len3 * sizeof (uint8_t));
      uint8_t *mHashHPart = mHash;
      uint8_t *mHashRPart = mHash;
      memcpy(mHashHPart, m, sz_hash * sizeof (uint8_t));
      toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
      reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
      bool
      r12 =
        ecdsa_verification_step45(Spec_ECC_Curves_P256,
          MontLadder,
          u1,
          u2,
          rAsFelem,
          sAsFelem,
          hashAsFelem,
          x,
          publicKeyBuffer,
          tempBuffer1);
      bool state = r12;
      if (state == false)
      {
        r1 = false;
      }
      else
      {
        r1 = cmp_felem_felem_bool_p256(x, rAsFelem);
      }
    }
  }
  bool result = r1;
  return result;
}

/*
This code is not side-channel resistant.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification.
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_verif_without_hash_radix(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tempBuffer[(uint32_t)4U * len];
  memset(tempBuffer, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  uint64_t *publicKeyAsFelem = tempBuffer;
  uint64_t *rAsFelem = tempBuffer + (uint32_t)2U * len;
  uint64_t *sAsFelem = tempBuffer + (uint32_t)3U * len;
  uint32_t len1 = (uint32_t)4U;
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len1;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + (uint32_t)32U;
  toUint64ChangeEndian_p256(pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian_p256(pubKeyY, publicKeyFelemY);
  toUint64ChangeEndian_p256(r, rAsFelem);
  toUint64ChangeEndian_p256(s, sAsFelem);
  uint32_t len10 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)20U);
  uint64_t tempBuffer1[len10 * (uint32_t)20U];
  memset(tempBuffer1, 0U, len10 * (uint32_t)20U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t hashAsFelem[len10];
  memset(hashAsFelem, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10);
  uint64_t x[len10];
  memset(x, 0U, len10 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len10 * (uint32_t)3U);
  uint64_t publicKeyBuffer[len10 * (uint32_t)3U];
  memset(publicKeyBuffer, 0U, len10 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len20 = (uint32_t)4U;
  uint32_t lengthXY = len20 * (uint32_t)2U;
  uint64_t *partPoint = publicKeyBuffer;
  uint64_t *zCoordinate = publicKeyBuffer + lengthXY;
  memcpy(partPoint, publicKeyAsFelem, lengthXY * sizeof (uint64_t));
  zCoordinate[0U] = (uint64_t)1U;
  uint32_t len30 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len30; i++)
  {
    zCoordinate[i] = (uint64_t)0U;
  }
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(publicKeyBuffer);
  bool r1;
  if (publicKeyCorrect == false)
  {
    r1 = false;
  }
  else
  {
    uint32_t len21 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len21);
    uint64_t tempBuffer2[len21];
    memset(tempBuffer2, 0U, len21 * sizeof (uint64_t));
    uint64_t
    p0[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len31 = (uint32_t)4U;
    uint64_t c0 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len31 / (uint32_t)4U; i++)
    {
      uint64_t t1 = rAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p0[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer2 + (uint32_t)4U * i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
      uint64_t t10 = rAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)1U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
      uint64_t t11 = rAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer2 + (uint32_t)4U * i + (uint32_t)2U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
      uint64_t t12 = rAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer2 + (uint32_t)4U * i + (uint32_t)3U;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
    }
    for (uint32_t i = len31 / (uint32_t)4U * (uint32_t)4U; i < len31; i++)
    {
      uint64_t t1 = rAsFelem[i];
      uint64_t t2 = p0[i];
      uint64_t *res_i = tempBuffer2 + i;
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
    }
    uint64_t r10 = c0;
    uint64_t carry = r10;
    bool less = carry == (uint64_t)1U;
    uint64_t tmp1 = (uint64_t)18446744073709551615U;
    uint32_t len32 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len32; i++)
    {
      uint64_t a_i = rAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp1;
      tmp1 = r_i & tmp0;
    }
    uint64_t f = tmp1;
    bool more = f == (uint64_t)0xffffffffffffffffU;
    bool isRCorrect = less && !more;
    uint32_t len2 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len2);
    uint64_t tempBuffer20[len2];
    memset(tempBuffer20, 0U, len2 * sizeof (uint64_t));
    uint64_t
    p[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len33 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len33 / (uint32_t)4U; i++)
    {
      uint64_t t1 = sAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer20 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      uint64_t t10 = sAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
      uint64_t t11 = sAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer20 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
      uint64_t t12 = sAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer20 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
    }
    for (uint32_t i = len33 / (uint32_t)4U * (uint32_t)4U; i < len33; i++)
    {
      uint64_t t1 = sAsFelem[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer20 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
    uint64_t r11 = c;
    uint64_t carry0 = r11;
    bool less0 = carry0 == (uint64_t)1U;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len34 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len34; i++)
    {
      uint64_t a_i = sAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t f0 = tmp;
    bool more0 = f0 == (uint64_t)0xffffffffffffffffU;
    bool isSCorrect = less0 && !more0;
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      r1 = false;
    }
    else
    {
      uint32_t len22 = (uint32_t)4U * (uint32_t)8U;
      KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * len22);
      uint8_t tempBufferU8[(uint32_t)2U * len22];
      memset(tempBufferU8, 0U, (uint32_t)2U * len22 * sizeof (uint8_t));
      void *u1 = (void *)tempBufferU8;
      void *u2 = (void *)(tempBufferU8 + len22);
      uint32_t sz_hash = mLen;
      uint32_t len3 = sz_hash + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len3);
      uint8_t mHash[len3];
      memset(mHash, 0U, len3 * sizeof (uint8_t));
      uint8_t *mHashHPart = mHash;
      uint8_t *mHashRPart = mHash;
      memcpy(mHashHPart, m, sz_hash * sizeof (uint8_t));
      toUint64ChangeEndian_p256(mHashRPart, hashAsFelem);
      reduction_prime_2prime_order_p256(hashAsFelem, hashAsFelem);
      bool
      r12 =
        ecdsa_verification_step45(Spec_ECC_Curves_P256,
          Radix,
          u1,
          u2,
          rAsFelem,
          sAsFelem,
          hashAsFelem,
          x,
          publicKeyBuffer,
          tempBuffer1);
      bool state = r12;
      if (state == false)
      {
        r1 = false;
      }
      else
      {
        r1 = cmp_felem_felem_bool_p256(x, rAsFelem);
      }
    }
  }
  bool result = r1;
  return result;
}

/*
 Public key verification function. 
  
 This code is not side-channel resistant.
  
 Input: pub(lic)Key: uint8[64]. 
  
 Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:  
 Verify that the public key is not the “point at infinity”, represented as O. 
 Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field. 
 Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation. 
 Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  
 The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_verify_q_public(uint8_t *pubKey)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t publicKeyJ[(uint32_t)3U * len];
  memset(publicKeyJ, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p256(pubKey, publicKeyJ);
  bool r = verifyQValidCurvePoint_public_p256(publicKeyJ);
  return r;
}

/*
 Public key verification function. 
  
 Input: pub(lic)Key: uint8[64]. 
  
 Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:  
 Verify that the public key is not the “point at infinity”, represented as O. 
 Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field. 
 Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation. 
 Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  
 The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_verify_q_private(uint8_t *pubKey)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t publicKeyJ[(uint32_t)3U * len];
  memset(publicKeyJ, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p256(pubKey, publicKeyJ);
  bool r = verifyQValidCurvePoint_private_p256(publicKeyJ);
  return r;
}

/*
 There and further we introduce notions of compressed point and not compressed point. 
  
 We denote || as byte concatenation. 
  
 A compressed point is a point representaion as follows: (0x2 + y % 2) || x.
  
 A not Compressed point is a point representation as follows: 0x4 || x || y.

  
 
 Input: a point in not compressed form (uint8[65]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_not_compressed_form_p256(uint8_t *b, uint8_t *result)
{
  uint8_t compressionIdentifier = b[0U];
  bool correctIdentifier = (uint8_t)4U == compressionIdentifier;
  if (correctIdentifier)
  {
    memcpy(result, b + (uint32_t)1U, (uint32_t)64U * sizeof (uint8_t));
  }
  return correctIdentifier;
}

/*
 Input: a point in compressed form (uint8[33]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_compressed_form_p256(uint8_t *b, uint8_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t temp[(uint32_t)2U * len];
  memset(temp, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t0 = temp;
  uint64_t *t1 = temp + len;
  uint8_t compressedIdentifier = b[0U];
  uint8_t correctIdentifier2 = FStar_UInt8_eq_mask((uint8_t)2U, compressedIdentifier);
  uint8_t correctIdentifier3 = FStar_UInt8_eq_mask((uint8_t)3U, compressedIdentifier);
  uint8_t isIdentifierCorrect = correctIdentifier2 | correctIdentifier3;
  bool flag = isIdentifierCorrect == (uint8_t)255U;
  if (flag)
  {
    uint8_t *x = b + (uint32_t)1U;
    memcpy(result, x, (uint32_t)32U * sizeof (uint8_t));
    toUint64ChangeEndian_p256(x, t0);
    uint32_t len10 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len10);
    uint64_t tempBuffer[len10];
    memset(tempBuffer, 0U, len10 * sizeof (uint64_t));
    uint64_t
    p[4U] =
      {
        (uint64_t)0xffffffffffffffffU,
        (uint64_t)0xffffffffU,
        (uint64_t)0U,
        (uint64_t)0xffffffff00000001U
      };
    uint32_t len2 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len2 / (uint32_t)4U; i++)
    {
      uint64_t t11 = t0[(uint32_t)4U * i];
      uint64_t t20 = p[(uint32_t)4U * i];
      uint64_t *res_i0 = tempBuffer + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t20, res_i0);
      uint64_t t110 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = tempBuffer + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t110, t21, res_i1);
      uint64_t t111 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = tempBuffer + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t111, t22, res_i2);
      uint64_t t112 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = tempBuffer + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t112, t2, res_i);
    }
    for (uint32_t i = len2 / (uint32_t)4U * (uint32_t)4U; i < len2; i++)
    {
      uint64_t t11 = t0[i];
      uint64_t t2 = p[i];
      uint64_t *res_i = tempBuffer + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t2, res_i);
    }
    uint64_t r = c;
    uint64_t carry = r;
    bool lessThanPrimeXCoordinate = carry == (uint64_t)1U;
    if (!lessThanPrimeXCoordinate)
    {
      return false;
    }
    toDomain_p256(t0, t0);
    uint64_t identifierBit = (uint64_t)(compressedIdentifier & (uint8_t)1U);
    computeYFromX(Spec_ECC_Curves_P256, t0, t1, identifierBit);
    uint8_t *uu____0 = result + (uint32_t)32U;
    uint32_t len1 = (uint32_t)4U;
    uint32_t lenByTwo = len1 >> (uint32_t)1U;
    for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
    {
      uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
      uint64_t left = t1[i];
      uint64_t right = t1[lenRight];
      t1[i] = right;
      t1[lenRight] = left;
    }
    uint32_t len11 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len11; i++)
    {
      store64_be(uu____0 + i * (uint32_t)8U, t1[i]);
    }
    return true;
  }
  return false;
}

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[65]).
*/
void Hacl_P256_compression_not_compressed_form_p256(uint8_t *b, uint8_t *result)
{
  uint32_t lenCoordinate = (uint32_t)32U;
  uint8_t *to = result + (uint32_t)1U;
  memcpy(to, b, (uint32_t)2U * lenCoordinate * sizeof (uint8_t));
  result[0U] = (uint8_t)4U;
}

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[33]).
*/
void Hacl_P256_compression_compressed_form_p256(uint8_t *b, uint8_t *result)
{
  uint8_t *y = b + (uint32_t)32U;
  uint8_t lastWordY = y[31U];
  uint8_t lastBitY = lastWordY & (uint8_t)1U;
  uint8_t identifier = lastBitY + (uint8_t)2U;
  memcpy(result + (uint32_t)1U, b, (uint32_t)32U * sizeof (uint8_t));
  result[0U] = identifier;
}

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp256dh_i_ml(uint8_t *result, uint8_t *scalar)
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
  return flag;
}

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp256dh_i_radix(uint8_t *result, uint8_t *scalar)
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
  uint64_t *pXpY = q;
  uint32_t half0 = (uint32_t)0U;
  uint32_t word = (uint32_t)scalar[half0];
  uint32_t bitShift0 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate = bitShift0;
  uint32_t leftWord0 = word >> (uint32_t)0x4U;
  uint32_t rightWord0 = word & (uint32_t)0x0fU;
  uint32_t mask0 = (uint32_t)0U - bitShiftAsPrivate;
  uint32_t bits = leftWord0 ^ (mask0 & (leftWord0 ^ rightWord0));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits, (uint64_t)i);
    const uint64_t *lut_cmb_x = points_radix_16_p256 + (uint32_t)8U * i;
    const uint64_t *lut_cmb_y = points_radix_16_p256 + (uint32_t)8U * i + (uint32_t)4U;
    uint64_t *pointToAddX = pXpY;
    uint64_t *pointToAddY = pXpY + (uint32_t)4U;
    copy_conditional_p256_c(pointToAddX, lut_cmb_x, mask);
    copy_conditional_p256_c(pointToAddY, lut_cmb_y, mask);
  }
  uint64_t *pZ = q + (uint32_t)8U;
  uint32_t half1 = (uint32_t)0U;
  uint32_t word0 = (uint32_t)scalar[half1];
  uint32_t bitShift1 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate0 = bitShift1;
  uint32_t leftWord1 = word0 >> (uint32_t)0x4U;
  uint32_t rightWord1 = word0 & (uint32_t)0x0fU;
  uint32_t mask1 = (uint32_t)0U - bitShiftAsPrivate0;
  uint32_t bits0 = leftWord1 ^ (mask1 & (leftWord1 ^ rightWord1));
  uint64_t flag = FStar_UInt64_eq_mask((uint64_t)bits0, (uint64_t)0U);
  pZ[0U] = (uint64_t)1U;
  uint32_t len20 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len20; i++)
  {
    pZ[i] = (uint64_t)0U;
  }
  uint64_t *pz_0 = pZ;
  uint64_t out_0 = pz_0[0U];
  uint64_t r_0 = out_0 ^ (flag & (out_0 ^ (uint64_t)0U));
  pz_0[0U] = r_0;
  for (uint32_t i0 = (uint32_t)1U; i0 < (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U); i0++)
  {
    uint64_t pointToAdd[8U] = { 0U };
    uint32_t half = i0 >> (uint32_t)1U;
    uint32_t word1 = (uint32_t)scalar[half];
    uint32_t bitShift = i0 & (uint32_t)1U;
    uint32_t bitShiftAsPrivate1 = bitShift;
    uint32_t leftWord = word1 >> (uint32_t)0x4U;
    uint32_t rightWord = word1 & (uint32_t)0x0fU;
    uint32_t mask2 = (uint32_t)0U - bitShiftAsPrivate1;
    uint32_t bits1 = leftWord ^ (mask2 & (leftWord ^ rightWord));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits1, (uint64_t)i);
      const uint64_t *lut_cmb_x = points_radix_16_p256 + (uint32_t)8U * i;
      const uint64_t *lut_cmb_y = points_radix_16_p256 + (uint32_t)8U * i + (uint32_t)4U;
      uint64_t *pointToAddX = pointToAdd;
      uint64_t *pointToAddY = pointToAdd + (uint32_t)4U;
      copy_conditional_p256_c(pointToAddX, lut_cmb_x, mask);
      copy_conditional_p256_c(pointToAddY, lut_cmb_y, mask);
    }
    {
      point_double_p256(q, q, buff);
    }
    {
      point_double_p256(q, q, buff);
    }
    {
      point_double_p256(q, q, buff);
    }
    {
      point_double_p256(q, q, buff);
    }
    point_add_mixed_p256(q, pointToAdd, q, buff);
  }
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
  bool flag0 = r0 == (uint64_t)0U;
  return flag0;
}

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp256dh_i_wnaf(uint8_t *result, uint8_t *scalar)
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
  scalar_multiplication_cmb_p256(q, (void *)scalar, buff);
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
  return flag;
}

bool Hacl_P256_ecp384dh_i_ml(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len1;
  uint32_t len20 = (uint32_t)6U;
  uint64_t *x = q;
  uint64_t *y = q + len20;
  uint64_t *z = q + (uint32_t)2U * len20;
  uint32_t len3 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len3; i++)
  {
    x[i] = (uint64_t)0U;
  }
  uint32_t len30 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len30; i++)
  {
    y[i] = (uint64_t)0U;
  }
  uint32_t len31 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len31; i++)
  {
    z[i] = (uint64_t)0U;
  }
  resultBuffer[0U] = (uint64_t)0x3dd0756649c0b528U;
  resultBuffer[1U] = (uint64_t)0x20e378e2a0d6ce38U;
  resultBuffer[2U] = (uint64_t)0x879c3afc541b4d6eU;
  resultBuffer[3U] = (uint64_t)0x6454868459a30effU;
  resultBuffer[4U] = (uint64_t)0x812ff723614ede2bU;
  resultBuffer[5U] = (uint64_t)0x4d3aadc2299e1513U;
  resultBuffer[6U] = (uint64_t)0x23043dad4b03a4feU;
  resultBuffer[7U] = (uint64_t)0xa1bfa8bf7bb4a9acU;
  resultBuffer[8U] = (uint64_t)0x8bade7562e83b050U;
  resultBuffer[9U] = (uint64_t)0xc6c3521968f4ffd9U;
  resultBuffer[10U] = (uint64_t)0xdd8002263969a840U;
  resultBuffer[11U] = (uint64_t)0x2b78abc25a15c5e9U;
  resultBuffer[12U] = (uint64_t)0xffffffff00000001U;
  resultBuffer[13U] = (uint64_t)0xffffffffU;
  resultBuffer[14U] = (uint64_t)0x1U;
  resultBuffer[15U] = (uint64_t)0U;
  resultBuffer[16U] = (uint64_t)0U;
  resultBuffer[17U] = (uint64_t)0U;
  montgomery_ladderP384L(q, resultBuffer, scalar, buff);
  norm_p384(q, resultBuffer, buff);
  uint32_t len10 = (uint32_t)6U;
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = resultBuffer + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t r0 = r;
  fromFormPoint_p384(resultBuffer, result);
  bool flag = r0 == (uint64_t)0U;
  return flag;
}

bool Hacl_P256_ecp384dh_i_radix(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len1;
  uint64_t *pXpY = q;
  uint32_t half0 = (uint32_t)0U;
  uint32_t word = (uint32_t)scalar[half0];
  uint32_t bitShift0 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate = bitShift0;
  uint32_t leftWord0 = word >> (uint32_t)0x4U;
  uint32_t rightWord0 = word & (uint32_t)0x0fU;
  uint32_t mask0 = (uint32_t)0U - bitShiftAsPrivate;
  uint32_t bits = leftWord0 ^ (mask0 & (leftWord0 ^ rightWord0));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits, (uint64_t)i);
    const uint64_t *lut_cmb_x = points_radix_16_p384 + (uint32_t)12U * i;
    const uint64_t *lut_cmb_y = points_radix_16_p384 + (uint32_t)12U * i + (uint32_t)6U;
    uint64_t *pointToAddX = pXpY;
    uint64_t *pointToAddY = pXpY + (uint32_t)6U;
    copy_conditional_p384_c(pointToAddX, lut_cmb_x, mask);
    copy_conditional_p384_c(pointToAddY, lut_cmb_y, mask);
  }
  uint64_t *pZ = q + (uint32_t)12U;
  uint32_t half1 = (uint32_t)0U;
  uint32_t word0 = (uint32_t)scalar[half1];
  uint32_t bitShift1 = (uint32_t)0U;
  uint32_t bitShiftAsPrivate0 = bitShift1;
  uint32_t leftWord1 = word0 >> (uint32_t)0x4U;
  uint32_t rightWord1 = word0 & (uint32_t)0x0fU;
  uint32_t mask1 = (uint32_t)0U - bitShiftAsPrivate0;
  uint32_t bits0 = leftWord1 ^ (mask1 & (leftWord1 ^ rightWord1));
  uint64_t flag = FStar_UInt64_eq_mask((uint64_t)bits0, (uint64_t)0U);
  pZ[0U] = (uint64_t)1U;
  uint32_t len20 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)1U; i < len20; i++)
  {
    pZ[i] = (uint64_t)0U;
  }
  uint64_t *pz_0 = pZ;
  uint64_t out_0 = pz_0[0U];
  uint64_t r_0 = out_0 ^ (flag & (out_0 ^ (uint64_t)0U));
  pz_0[0U] = r_0;
  for (uint32_t i0 = (uint32_t)1U; i0 < (uint32_t)2U * ((uint32_t)6U * (uint32_t)8U); i0++)
  {
    uint64_t pointToAdd[12U] = { 0U };
    uint32_t half = i0 >> (uint32_t)1U;
    uint32_t word1 = (uint32_t)scalar[half];
    uint32_t bitShift = i0 & (uint32_t)1U;
    uint32_t bitShiftAsPrivate1 = bitShift;
    uint32_t leftWord = word1 >> (uint32_t)0x4U;
    uint32_t rightWord = word1 & (uint32_t)0x0fU;
    uint32_t mask2 = (uint32_t)0U - bitShiftAsPrivate1;
    uint32_t bits1 = leftWord ^ (mask2 & (leftWord ^ rightWord));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t mask = FStar_UInt64_eq_mask((uint64_t)bits1, (uint64_t)i);
      const uint64_t *lut_cmb_x = points_radix_16_p384 + (uint32_t)12U * i;
      const uint64_t *lut_cmb_y = points_radix_16_p384 + (uint32_t)12U * i + (uint32_t)6U;
      uint64_t *pointToAddX = pointToAdd;
      uint64_t *pointToAddY = pointToAdd + (uint32_t)6U;
      copy_conditional_p384_c(pointToAddX, lut_cmb_x, mask);
      copy_conditional_p384_c(pointToAddY, lut_cmb_y, mask);
    }
    {
      point_double_p384(q, q, buff);
    }
    {
      point_double_p384(q, q, buff);
    }
    {
      point_double_p384(q, q, buff);
    }
    {
      point_double_p384(q, q, buff);
    }
    point_add_mixed_p384(q, pointToAdd, q, buff);
  }
  norm_p384(q, resultBuffer, buff);
  uint32_t len10 = (uint32_t)6U;
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = resultBuffer + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t r0 = r;
  fromFormPoint_p384(resultBuffer, result);
  bool flag0 = r0 == (uint64_t)0U;
  return flag0;
}

bool Hacl_P256_ecp384dh_i_wnaf(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len1;
  scalar_multiplication_cmb_p384(q, (void *)scalar, buff);
  norm_p384(q, resultBuffer, buff);
  uint32_t len10 = (uint32_t)6U;
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = resultBuffer + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t r0 = r;
  fromFormPoint_p384(resultBuffer, result);
  bool flag = r0 == (uint64_t)0U;
  return flag;
}

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp256dh_r_public_ml(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
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
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)4U;
    uint64_t *q = tempBuffer;
    uint64_t *temp = tempBuffer + (uint32_t)3U * len30;
    uint32_t len4 = (uint32_t)4U;
    uint64_t *x = q;
    uint64_t *y = q + len4;
    uint64_t *z = q + (uint32_t)2U * len4;
    uint32_t len5 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len50 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len50; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len51 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len51; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len40 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len40;
    uint64_t *p_z = pkF + (uint32_t)2U * len40;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len40;
    uint64_t *r_z = rF + (uint32_t)2U * len40;
    toDomain_p256(p_x, r_x);
    toDomain_p256(p_y, r_y);
    toDomain_p256(p_z, r_z);
    montgomery_ladderP256L(q, rF, scalar, temp);
    memcpy(rF, q, (uint32_t)12U * sizeof (uint64_t));
    uint64_t *t = tempBuffer;
    norm_p256(rF, rF, t);
    uint32_t len2 = (uint32_t)4U;
    uint32_t start = len2 * (uint32_t)2U;
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
  return flag0;
}

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp256dh_r_public_radix(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
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
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len30;
    uint64_t *p_z = pkF + (uint32_t)2U * len30;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len30;
    uint64_t *r_z = rF + (uint32_t)2U * len30;
    toDomain_p256(p_x, r_x);
    toDomain_p256(p_y, r_y);
    toDomain_p256(p_z, r_z);
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * ((uint32_t)4U * (uint32_t)3U));
    uint64_t precomputedTable[(uint32_t)16U * ((uint32_t)4U * (uint32_t)3U)];
    memset(precomputedTable,
      0U,
      (uint32_t)16U * ((uint32_t)4U * (uint32_t)3U) * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)3U);
    uint64_t tempPoint[(uint32_t)4U * (uint32_t)3U];
    memset(tempPoint, 0U, (uint32_t)4U * (uint32_t)3U * sizeof (uint64_t));
    uint64_t *tempBuffer1 = tempBuffer;
    generatePrecomputedTable(Spec_ECC_Curves_P256, precomputedTable, rF, tempBuffer1);
    getPointPrecomputedTable(Spec_ECC_Curves_P256,
      (void *)scalar,
      precomputedTable,
      (uint32_t)0U,
      rF);
    for (uint32_t i = (uint32_t)1U; i < (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U); i++)
    {
      getPointPrecomputedTable(Spec_ECC_Curves_P256,
        (void *)scalar,
        precomputedTable,
        i,
        tempPoint);
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      point_add_p256(tempPoint, rF, rF, tempBuffer1);
    }
    uint64_t *t = tempBuffer;
    norm_p256(rF, rF, t);
    uint32_t len2 = (uint32_t)4U;
    uint32_t start = len2 * (uint32_t)2U;
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
  return flag0;
}

bool Hacl_P256_ecp256dh_r_private_ml(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
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
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)4U;
    uint64_t *q = tempBuffer;
    uint64_t *temp = tempBuffer + (uint32_t)3U * len30;
    uint32_t len4 = (uint32_t)4U;
    uint64_t *x = q;
    uint64_t *y = q + len4;
    uint64_t *z = q + (uint32_t)2U * len4;
    uint32_t len5 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len50 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len50; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len51 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len51; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len40 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len40;
    uint64_t *p_z = pkF + (uint32_t)2U * len40;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len40;
    uint64_t *r_z = rF + (uint32_t)2U * len40;
    toDomain_p256(p_x, r_x);
    toDomain_p256(p_y, r_y);
    toDomain_p256(p_z, r_z);
    montgomery_ladderP256L(q, rF, scalar, temp);
    memcpy(rF, q, (uint32_t)12U * sizeof (uint64_t));
    uint64_t *t = tempBuffer;
    norm_p256(rF, rF, t);
    uint32_t len2 = (uint32_t)4U;
    uint32_t start = len2 * (uint32_t)2U;
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
  return flag0;
}

bool Hacl_P256_ecp256dh_r_private_radix(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
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
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p256(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len30;
    uint64_t *p_z = pkF + (uint32_t)2U * len30;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len30;
    uint64_t *r_z = rF + (uint32_t)2U * len30;
    toDomain_p256(p_x, r_x);
    toDomain_p256(p_y, r_y);
    toDomain_p256(p_z, r_z);
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * ((uint32_t)4U * (uint32_t)3U));
    uint64_t precomputedTable[(uint32_t)16U * ((uint32_t)4U * (uint32_t)3U)];
    memset(precomputedTable,
      0U,
      (uint32_t)16U * ((uint32_t)4U * (uint32_t)3U) * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)3U);
    uint64_t tempPoint[(uint32_t)4U * (uint32_t)3U];
    memset(tempPoint, 0U, (uint32_t)4U * (uint32_t)3U * sizeof (uint64_t));
    uint64_t *tempBuffer1 = tempBuffer;
    generatePrecomputedTable(Spec_ECC_Curves_P256, precomputedTable, rF, tempBuffer1);
    getPointPrecomputedTable(Spec_ECC_Curves_P256,
      (void *)scalar,
      precomputedTable,
      (uint32_t)0U,
      rF);
    for (uint32_t i = (uint32_t)1U; i < (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U); i++)
    {
      getPointPrecomputedTable(Spec_ECC_Curves_P256,
        (void *)scalar,
        precomputedTable,
        i,
        tempPoint);
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      {
        point_double_p256(rF, rF, tempBuffer1);
      }
      point_add_p256(tempPoint, rF, rF, tempBuffer1);
    }
    uint64_t *t = tempBuffer;
    norm_p256(rF, rF, t);
    uint32_t len2 = (uint32_t)4U;
    uint32_t start = len2 * (uint32_t)2U;
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
  return flag0;
}

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp384dh_r_public_ml(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p384(pubKey, pkF);
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p384(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)6U;
    uint64_t *q = tempBuffer;
    uint64_t *temp = tempBuffer + (uint32_t)3U * len30;
    uint32_t len4 = (uint32_t)6U;
    uint64_t *x = q;
    uint64_t *y = q + len4;
    uint64_t *z = q + (uint32_t)2U * len4;
    uint32_t len5 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len50 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len50; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len51 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len51; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len40 = (uint32_t)6U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len40;
    uint64_t *p_z = pkF + (uint32_t)2U * len40;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len40;
    uint64_t *r_z = rF + (uint32_t)2U * len40;
    toDomain_p384(p_x, r_x);
    toDomain_p384(p_y, r_y);
    toDomain_p384(p_z, r_z);
    montgomery_ladderP384L(q, rF, scalar, temp);
    memcpy(rF, q, (uint32_t)18U * sizeof (uint64_t));
    uint64_t *t = tempBuffer;
    norm_p384(rF, rF, t);
    uint32_t len2 = (uint32_t)6U;
    uint32_t start = len2 * (uint32_t)2U;
    uint64_t *zCoordinate = rF + start;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)6U;
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
  fromFormPoint_p384(rF, result);
  bool flag0 = flag;
  return flag0;
}

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
bool Hacl_P256_ecp384dh_r_public_radix(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p384(pubKey, pkF);
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p384(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)6U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len30;
    uint64_t *p_z = pkF + (uint32_t)2U * len30;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len30;
    uint64_t *r_z = rF + (uint32_t)2U * len30;
    toDomain_p384(p_x, r_x);
    toDomain_p384(p_y, r_y);
    toDomain_p384(p_z, r_z);
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * ((uint32_t)6U * (uint32_t)3U));
    uint64_t precomputedTable[(uint32_t)16U * ((uint32_t)6U * (uint32_t)3U)];
    memset(precomputedTable,
      0U,
      (uint32_t)16U * ((uint32_t)6U * (uint32_t)3U) * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)6U * (uint32_t)3U);
    uint64_t tempPoint[(uint32_t)6U * (uint32_t)3U];
    memset(tempPoint, 0U, (uint32_t)6U * (uint32_t)3U * sizeof (uint64_t));
    uint64_t *tempBuffer1 = tempBuffer;
    generatePrecomputedTable(Spec_ECC_Curves_P384, precomputedTable, rF, tempBuffer1);
    getPointPrecomputedTable(Spec_ECC_Curves_P384,
      (void *)scalar,
      precomputedTable,
      (uint32_t)0U,
      rF);
    for (uint32_t i = (uint32_t)1U; i < (uint32_t)2U * ((uint32_t)6U * (uint32_t)8U); i++)
    {
      getPointPrecomputedTable(Spec_ECC_Curves_P384,
        (void *)scalar,
        precomputedTable,
        i,
        tempPoint);
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      point_add_p384(tempPoint, rF, rF, tempBuffer1);
    }
    uint64_t *t = tempBuffer;
    norm_p384(rF, rF, t);
    uint32_t len2 = (uint32_t)6U;
    uint32_t start = len2 * (uint32_t)2U;
    uint64_t *zCoordinate = rF + start;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)6U;
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
  fromFormPoint_p384(rF, result);
  bool flag0 = flag;
  return flag0;
}

bool Hacl_P256_ecp384dh_r_private_ml(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p384(pubKey, pkF);
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p384(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)6U;
    uint64_t *q = tempBuffer;
    uint64_t *temp = tempBuffer + (uint32_t)3U * len30;
    uint32_t len4 = (uint32_t)6U;
    uint64_t *x = q;
    uint64_t *y = q + len4;
    uint64_t *z = q + (uint32_t)2U * len4;
    uint32_t len5 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len50 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len50; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len51 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len51; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len40 = (uint32_t)6U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len40;
    uint64_t *p_z = pkF + (uint32_t)2U * len40;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len40;
    uint64_t *r_z = rF + (uint32_t)2U * len40;
    toDomain_p384(p_x, r_x);
    toDomain_p384(p_y, r_y);
    toDomain_p384(p_z, r_z);
    montgomery_ladderP384L(q, rF, scalar, temp);
    memcpy(rF, q, (uint32_t)18U * sizeof (uint64_t));
    uint64_t *t = tempBuffer;
    norm_p384(rF, rF, t);
    uint32_t len2 = (uint32_t)6U;
    uint32_t start = len2 * (uint32_t)2U;
    uint64_t *zCoordinate = rF + start;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)6U;
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
  fromFormPoint_p384(rF, result);
  bool flag0 = flag;
  return flag0;
}

bool Hacl_P256_ecp384dh_r_private_radix(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  toFormPoint_p384(pubKey, pkF);
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint_public_p384(pkF);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len30 = (uint32_t)6U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len30;
    uint64_t *p_z = pkF + (uint32_t)2U * len30;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len30;
    uint64_t *r_z = rF + (uint32_t)2U * len30;
    toDomain_p384(p_x, r_x);
    toDomain_p384(p_y, r_y);
    toDomain_p384(p_z, r_z);
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * ((uint32_t)6U * (uint32_t)3U));
    uint64_t precomputedTable[(uint32_t)16U * ((uint32_t)6U * (uint32_t)3U)];
    memset(precomputedTable,
      0U,
      (uint32_t)16U * ((uint32_t)6U * (uint32_t)3U) * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)6U * (uint32_t)3U);
    uint64_t tempPoint[(uint32_t)6U * (uint32_t)3U];
    memset(tempPoint, 0U, (uint32_t)6U * (uint32_t)3U * sizeof (uint64_t));
    uint64_t *tempBuffer1 = tempBuffer;
    generatePrecomputedTable(Spec_ECC_Curves_P384, precomputedTable, rF, tempBuffer1);
    getPointPrecomputedTable(Spec_ECC_Curves_P384,
      (void *)scalar,
      precomputedTable,
      (uint32_t)0U,
      rF);
    for (uint32_t i = (uint32_t)1U; i < (uint32_t)2U * ((uint32_t)6U * (uint32_t)8U); i++)
    {
      getPointPrecomputedTable(Spec_ECC_Curves_P384,
        (void *)scalar,
        precomputedTable,
        i,
        tempPoint);
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      {
        point_double_p384(rF, rF, tempBuffer1);
      }
      point_add_p384(tempPoint, rF, rF, tempBuffer1);
    }
    uint64_t *t = tempBuffer;
    norm_p384(rF, rF, t);
    uint32_t len2 = (uint32_t)6U;
    uint32_t start = len2 * (uint32_t)2U;
    uint64_t *zCoordinate = rF + start;
    uint64_t tmp = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)6U;
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
  fromFormPoint_p384(rF, result);
  bool flag0 = flag;
  return flag0;
}

/*
Other exposed primitives 
 
Complete point addition.
Not side-channel resistant
*/
void Hacl_P256_point_add_out(uint64_t *p, uint64_t *q, uint64_t *result)
{
  uint64_t tempBuffer[68U] = { 0U };
  uint32_t len0 = (uint32_t)4U;
  uint64_t *zCoordinate = p + (uint32_t)2U * len0;
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t f = tmp1;
  bool pInfinity = f == (uint64_t)0xffffffffffffffffU;
  uint32_t len = (uint32_t)4U;
  uint64_t *zCoordinate0 = q + (uint32_t)2U * len;
  uint64_t tmp2 = (uint64_t)18446744073709551615U;
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len11; i++)
  {
    uint64_t a_i = zCoordinate0[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp2;
    tmp2 = r_i & tmp0;
  }
  uint64_t f0 = tmp2;
  bool qInfinity = f0 == (uint64_t)0xffffffffffffffffU;
  if (pInfinity)
  {
    memcpy(result, q, (uint32_t)12U * sizeof (uint64_t));
    return;
  }
  uint32_t len2 = (uint32_t)4U;
  uint64_t *sq_z1 = tempBuffer;
  uint64_t *tr_z1 = tempBuffer + len2;
  uint64_t *sq_z2 = tempBuffer + (uint32_t)2U * len2;
  uint64_t *tr_z2 = tempBuffer + (uint32_t)3U * len2;
  uint64_t *x1 = p;
  uint64_t *y1 = p + len2;
  uint64_t *z1 = p + (uint32_t)2U * len2;
  uint64_t *x2 = q;
  uint64_t *y2 = q + len2;
  uint64_t *z2 = q + (uint32_t)2U * len2;
  montgomery_square_buffer_dh_p256(z1, sq_z1);
  montgomery_square_buffer_dh_p256(z2, sq_z2);
  montgomery_multiplication_buffer_dh_p256(sq_z1, z1, tr_z1);
  montgomery_multiplication_buffer_dh_p256(sq_z2, z2, tr_z2);
  montgomery_multiplication_buffer_dh_p256(sq_z1, x2, sq_z1);
  montgomery_multiplication_buffer_dh_p256(sq_z2, x1, sq_z2);
  montgomery_multiplication_buffer_dh_p256(tr_z1, y2, tr_z1);
  montgomery_multiplication_buffer_dh_p256(tr_z2, y1, tr_z2);
  uint64_t tmp3 = (uint64_t)0U;
  tmp3 = (uint64_t)18446744073709551615U;
  uint32_t len12 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len12; i++)
  {
    uint64_t a_i = sq_z1[i];
    uint64_t b_i = sq_z2[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp3;
    tmp3 = r_i & tmp0;
  }
  uint64_t equalX = tmp3;
  uint64_t tmp4 = (uint64_t)0U;
  tmp4 = (uint64_t)18446744073709551615U;
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t a_i = tr_z1[i];
    uint64_t b_i = tr_z2[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp4;
    tmp4 = r_i & tmp0;
  }
  uint64_t equalY = tmp4;
  uint64_t equal = equalX & equalY;
  bool equal_b = !(equal == (uint64_t)0U);
  if (equal_b)
  {
    uint32_t len3 = (uint32_t)4U;
    uint64_t *pY = p + len3;
    uint64_t *pZ = p + (uint32_t)2U * len3;
    uint64_t *x3 = result;
    uint64_t *y3 = result + len3;
    uint64_t *z3 = result + (uint32_t)2U * len3;
    uint64_t *delta = tempBuffer;
    uint64_t *gamma = tempBuffer + len3;
    uint64_t *beta = tempBuffer + (uint32_t)2U * len3;
    uint64_t *alpha = tempBuffer + (uint32_t)3U * len3;
    uint64_t *fourBeta = tempBuffer + (uint32_t)4U * len3;
    uint64_t *eightBeta = tempBuffer + (uint32_t)5U * len3;
    uint64_t *eightGamma = tempBuffer + (uint32_t)6U * len3;
    uint64_t *tmp = tempBuffer + (uint32_t)7U * len3;
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
    return;
  }
  point_add_p256(p, q, result, tempBuffer);
}

/*
Point inverse
*/
void Hacl_P256_point_inv(uint64_t *p, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *yP = p + len;
  uint64_t *yResult = result + len;
  felem_sub_zero(Spec_ECC_Curves_P256, yP, yResult);
  memcpy(result, p, len * sizeof (uint64_t));
  memcpy(result + (uint32_t)8U, p + (uint32_t)8U, (uint32_t)4U * sizeof (uint64_t));
}

/*
Moves a point to correct endian form + uint64
*/
void Hacl_P256_point_toForm(uint8_t *i, uint64_t *o)
{
  toFormPoint_p256(i, o);
}

/*
Moves a point from correct endian form + uint8
*/
void Hacl_P256_point_fromForm(uint64_t *i, uint8_t *o)
{
  fromFormPoint_p256(i, o);
}

/*
Moves a point to domain
*/
void Hacl_P256_point_toDomain(uint64_t *p, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  uint64_t *p_x = p;
  uint64_t *p_y = p + len;
  uint64_t *p_z = p + (uint32_t)2U * len;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len;
  uint64_t *r_z = result + (uint32_t)2U * len;
  toDomain_p256(p_x, r_x);
  toDomain_p256(p_y, r_y);
  toDomain_p256(p_z, r_z);
}

/*
From domain + to affine
*/
void Hacl_P256_point_norm(uint64_t *p, uint64_t *result)
{
  uint64_t tempBuffer[68U] = { 0U };
  norm_p256(p, result, tempBuffer);
}

