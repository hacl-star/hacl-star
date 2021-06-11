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

static inline uint64_t mod_inv_u64(uint64_t n0)
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

static const
uint8_t
prime256_inverse_buffer[32U] =
  {
    (uint8_t)253U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)1U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U
  };

static const
uint8_t
prime384_inverse_buffer[48U] =
  {
    (uint8_t)253U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)254U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U
  };

static const
uint8_t
prime256_order_[32U] =
  {
    (uint8_t)253U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)1U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U, (uint8_t)255U
  };

static void felem_add_p256(uint64_t *a, uint64_t *b, uint64_t *out)
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

static void felem_add_p384(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)6U;
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
  uint32_t len10 = (uint32_t)6U;
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
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = out[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    out[i] = r_i;
  }
}

static void felem_add_generic(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  uint32_t k = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len0; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, out + i);
  }
  uint64_t t = c;
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t carry0 = (uint64_t)0U;
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

static void felem_double_p256(uint64_t *arg1, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg1[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg1[i];
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

static void felem_double_p384(uint64_t *arg1, uint64_t *out)
{
  uint32_t len0 = (uint32_t)6U;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg1[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg1[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, out + i);
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
  uint32_t len10 = (uint32_t)6U;
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
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = out[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    out[i] = r_i;
  }
}

static void felem_sub_p256(uint64_t *a, uint64_t *b, uint64_t *out)
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

static void felem_sub_p384(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  uint32_t k0 = len / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
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
  for (uint32_t i = k0; i < len; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, out + i);
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
  uint32_t k = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t11 = out[(uint32_t)4U * i];
    uint64_t t210 = b1[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t210, out + (uint32_t)4U * i);
    uint64_t t110 = out[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t211 = b1[(uint32_t)4U * i + (uint32_t)1U];
    c0 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c0,
        t110,
        t211,
        out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = out[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t212 = b1[(uint32_t)4U * i + (uint32_t)2U];
    c0 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c0,
        t111,
        t212,
        out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = out[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t21 = b1[(uint32_t)4U * i + (uint32_t)3U];
    c0 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c0,
        t112,
        t21,
        out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < (uint32_t)6U; i++)
  {
    uint64_t t11 = out[i];
    uint64_t t21 = b1[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t21, out + i);
  }
  uint64_t r = c0;
  uint64_t r0 = r;
}

static void felem_sub_generic(uint64_t *a, uint64_t *b, uint64_t *out)
{
  uint32_t len0 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t10,
        t21,
        out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t11,
        t22,
        out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, out + i);
  }
  uint64_t t = c0;
  uint64_t
  p[4U] =
    {
      (uint64_t)0xffffffffffffffffU,
      (uint64_t)0xffffffffU,
      (uint64_t)0U,
      (uint64_t)0xffffffff00000001U
    };
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t b1[len];
  memset(b1, 0U, len * sizeof (uint64_t));
  uint32_t len10 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  uint32_t k = len10 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = p[(uint32_t)4U * i];
    uint64_t t20 = out[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, b1 + (uint32_t)4U * i);
    uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = out[(uint32_t)4U * i + (uint32_t)1U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, b1 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = out[(uint32_t)4U * i + (uint32_t)2U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, b1 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = out[(uint32_t)4U * i + (uint32_t)3U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, b1 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < len10; i++)
  {
    uint64_t t1 = p[i];
    uint64_t t2 = out[i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, b1 + i);
  }
  uint64_t carry = c;
  uint64_t mask = ~((uint64_t)0U - t);
  uint64_t mask1 = ~FStar_UInt64_eq_mask(mask, (uint64_t)0U);
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t x_i = b1[i];
    uint64_t y_i = out[i];
    uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
    out[i] = r_i;
  }
  uint64_t r = carry;
  uint64_t r0 = r;
}

static void montgomery_multiplication_buffer_by_one_dh_p256(uint64_t *a, uint64_t *result)
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

static void montgomery_multiplication_buffer_by_one_dh_p384(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, a, len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint32_t len2 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    uint128_t res = (uint128_t)t10 * k0;
    uint64_t l0 = (uint64_t)res;
    uint64_t h04 = (uint64_t)(res >> (uint32_t)64U);
    y = l0;
    temp = h04;
    uint64_t y_ = y;
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len30 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    uint32_t resLen = len30 + (uint32_t)1U;
    memset(partResult, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t uu____0 = (&bBuffer)[0U];
      uint64_t *res_ = partResult;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____0, res_ + i);
      }
      uint64_t r = c;
      partResult[len30 + (uint32_t)0U] = r;
    }
    uint32_t len31 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len31; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
  uint32_t len2 = (uint32_t)6U;
  uint64_t cin = t[len2];
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
  uint32_t len40 = (uint32_t)6U;
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
  uint32_t len4 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = x_[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    result[i] = r_i;
  }
}

static void montgomery_multiplication_buffer_by_one_dh_generic(uint64_t *a, uint64_t *result)
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
    uint64_t k0 = mod_inv_u64((uint64_t)(uint32_t)1U);
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    uint128_t res = (uint128_t)t10 * k0;
    uint64_t l0 = (uint64_t)res;
    uint64_t h04 = (uint64_t)(res >> (uint32_t)64U);
    y = l0;
    temp = h04;
    uint64_t y_ = y;
    uint64_t
    p[4U] =
      {
        (uint64_t)0xffffffffffffffffU,
        (uint64_t)0xffffffffU,
        (uint64_t)0U,
        (uint64_t)0xffffffff00000001U
      };
    uint32_t len30 = (uint32_t)4U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    uint32_t resLen = len30 + (uint32_t)1U;
    memset(partResult, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t uu____0 = (&bBuffer)[0U];
      uint64_t *res_ = partResult;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____0, res_ + i);
      }
      uint64_t r = c;
      partResult[len30 + (uint32_t)0U] = r;
    }
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len31; i++)
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
  uint64_t carry0 = (uint64_t)0U;
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

static void
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

static void
montgomery_multiplication_buffer_dh_p384(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  uint32_t resLen0 = len1 + len1;
  memset(t, 0U, resLen0 * sizeof (uint64_t));
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
  uint32_t len10 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    uint32_t len2 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    uint128_t res = (uint128_t)t10 * k0;
    uint64_t l0 = (uint64_t)res;
    uint64_t h04 = (uint64_t)(res >> (uint32_t)64U);
    y = l0;
    temp = h04;
    uint64_t y_ = y;
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len30 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    uint32_t resLen = len30 + (uint32_t)1U;
    memset(partResult, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t uu____1 = (&bBuffer)[0U];
      uint64_t *res_ = partResult;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____1, res_ + i);
      }
      uint64_t r = c;
      partResult[len30 + (uint32_t)0U] = r;
    }
    uint32_t len31 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len31; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
  uint32_t len2 = (uint32_t)6U;
  uint64_t cin = t[len2];
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
  uint32_t len40 = (uint32_t)6U;
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
  uint32_t len4 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = x_[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    result[i] = r_i;
  }
}

static void
montgomery_multiplication_buffer_dh_generic(uint64_t *a, uint64_t *b, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  uint32_t resLen0 = len1 + len1;
  memset(t, 0U, resLen0 * sizeof (uint64_t));
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
    uint64_t k0 = mod_inv_u64((uint64_t)(uint32_t)1U);
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    uint128_t res = (uint128_t)t10 * k0;
    uint64_t l0 = (uint64_t)res;
    uint64_t h04 = (uint64_t)(res >> (uint32_t)64U);
    y = l0;
    temp = h04;
    uint64_t y_ = y;
    uint64_t
    p[4U] =
      {
        (uint64_t)0xffffffffffffffffU,
        (uint64_t)0xffffffffU,
        (uint64_t)0U,
        (uint64_t)0xffffffff00000001U
      };
    uint32_t len30 = (uint32_t)4U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    uint32_t resLen = len30 + (uint32_t)1U;
    memset(partResult, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t uu____1 = (&bBuffer)[0U];
      uint64_t *res_ = partResult;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____1, res_ + i);
      }
      uint64_t r = c;
      partResult[len30 + (uint32_t)0U] = r;
    }
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len31; i++)
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
  uint64_t carry0 = (uint64_t)0U;
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

static void montgomery_square_buffer_dh_p256(uint64_t *a, uint64_t *result)
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

static void montgomery_square_buffer_dh_p384(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)6U;
  uint32_t resLen0 = len1 + len1;
  memset(t, 0U, resLen0 * sizeof (uint64_t));
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
  uint32_t k1 = resLen0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
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
  for (uint32_t i = k1; i < resLen0; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = t[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, t + i);
  }
  uint64_t uu____2 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen0);
  uint64_t tmp[resLen0];
  memset(tmp, 0U, resLen0 * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t a2 = (uint128_t)a[i] * a[i];
    tmp[(uint32_t)2U * i] = (uint64_t)a2;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
  }
  uint64_t c1 = (uint64_t)0U;
  uint32_t k2 = resLen0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
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
  for (uint32_t i = k2; i < resLen0; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = tmp[i];
    c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t + i);
  }
  uint64_t uu____3 = c1;
  uint32_t len10 = (uint32_t)6U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    uint32_t len2 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t k0 = (uint64_t)4294967297U;
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    uint128_t res = (uint128_t)t10 * k0;
    uint64_t l0 = (uint64_t)res;
    uint64_t h04 = (uint64_t)(res >> (uint32_t)64U);
    y = l0;
    temp = h04;
    uint64_t y_ = y;
    uint64_t
    p[6U] =
      {
        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
      };
    uint32_t len30 = (uint32_t)6U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    uint32_t resLen = len30 + (uint32_t)1U;
    memset(partResult, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t uu____4 = (&bBuffer)[0U];
      uint64_t *res_ = partResult;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____4, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____4,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____4,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____4,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____4, res_ + i);
      }
      uint64_t r = c;
      partResult[len30 + (uint32_t)0U] = r;
    }
    uint32_t len31 = (uint32_t)6U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len31; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
  uint32_t len2 = (uint32_t)6U;
  uint64_t cin = t[len2];
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
  uint32_t len40 = (uint32_t)6U;
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
  uint32_t len4 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = x_[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    result[i] = r_i;
  }
}

static void montgomery_square_buffer_dh_generic(uint64_t *a, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint32_t len1 = (uint32_t)4U;
  uint32_t resLen0 = len1 + len1;
  memset(t, 0U, resLen0 * sizeof (uint64_t));
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
  uint32_t k1 = resLen0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
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
  for (uint32_t i = k1; i < resLen0; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = t[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, t + i);
  }
  uint64_t uu____2 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen0);
  uint64_t tmp[resLen0];
  memset(tmp, 0U, resLen0 * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t a2 = (uint128_t)a[i] * a[i];
    tmp[(uint32_t)2U * i] = (uint64_t)a2;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
  }
  uint64_t c1 = (uint64_t)0U;
  uint32_t k2 = resLen0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
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
  for (uint32_t i = k2; i < resLen0; i++)
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
    uint64_t k0 = mod_inv_u64((uint64_t)(uint32_t)1U);
    uint64_t t10 = t[0U];
    uint64_t y = (uint64_t)0U;
    uint64_t temp = (uint64_t)0U;
    uint128_t res = (uint128_t)t10 * k0;
    uint64_t l0 = (uint64_t)res;
    uint64_t h04 = (uint64_t)(res >> (uint32_t)64U);
    y = l0;
    temp = h04;
    uint64_t y_ = y;
    uint64_t
    p[4U] =
      {
        (uint64_t)0xffffffffffffffffU,
        (uint64_t)0xffffffffU,
        (uint64_t)0U,
        (uint64_t)0xffffffff00000001U
      };
    uint32_t len30 = (uint32_t)4U;
    uint64_t bBuffer = y_;
    uint64_t *partResult = t2;
    uint32_t resLen = len30 + (uint32_t)1U;
    memset(partResult, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t uu____4 = (&bBuffer)[0U];
      uint64_t *res_ = partResult;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____4, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____4,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____4,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____4,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len30; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____4, res_ + i);
      }
      uint64_t r = c;
      partResult[len30 + (uint32_t)0U] = r;
    }
    uint32_t len31 = (uint32_t)4U * (uint32_t)2U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len31; i++)
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
  uint64_t carry0 = (uint64_t)0U;
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

static void fsquarePowN_dh_p256(uint32_t n, uint64_t *a)
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

static void fsquarePowN_dh_p384(uint32_t n, uint64_t *a)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
  {
    uint32_t len = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
    uint64_t t[(uint32_t)2U * len];
    memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
    uint32_t len1 = (uint32_t)6U;
    uint32_t resLen0 = len1 + len1;
    memset(t, 0U, resLen0 * sizeof (uint64_t));
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
    uint32_t k1 = resLen0 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
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
    for (uint32_t i = k1; i < resLen0; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t2 = t[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, t + i);
    }
    uint64_t uu____2 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen0);
    uint64_t tmp[resLen0];
    memset(tmp, 0U, resLen0 * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint128_t a2 = (uint128_t)a[i] * a[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c1 = (uint64_t)0U;
    uint32_t k2 = resLen0 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
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
    for (uint32_t i = k2; i < resLen0; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t2 = tmp[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t + i);
    }
    uint64_t uu____3 = c1;
    uint32_t len10 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len10; i1++)
    {
      uint32_t len2 = (uint32_t)6U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
      uint64_t t2[(uint32_t)2U * len2];
      memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
      uint64_t k0 = (uint64_t)4294967297U;
      uint64_t t10 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      uint128_t res = (uint128_t)t10 * k0;
      uint64_t l0 = (uint64_t)res;
      uint64_t h05 = (uint64_t)(res >> (uint32_t)64U);
      y = l0;
      temp = h05;
      uint64_t y_ = y;
      uint64_t
      p[6U] =
        {
          (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
          (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffffffffffU
        };
      uint32_t len30 = (uint32_t)6U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      uint32_t resLen = len30 + (uint32_t)1U;
      memset(partResult, 0U, resLen * sizeof (uint64_t));
      {
        uint64_t uu____4 = (&bBuffer)[0U];
        uint64_t *res_ = partResult;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len30 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____4, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              p[(uint32_t)4U * i + (uint32_t)1U],
              uu____4,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              p[(uint32_t)4U * i + (uint32_t)2U],
              uu____4,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              p[(uint32_t)4U * i + (uint32_t)3U],
              uu____4,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len30; i++)
        {
          c = mul_carry_add_u64_st(c, p[i], uu____4, res_ + i);
        }
        uint64_t r = c;
        partResult[len30 + (uint32_t)0U] = r;
      }
      uint32_t len31 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len31 / (uint32_t)4U * (uint32_t)4U;
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
      for (uint32_t i = k; i < len31; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
    uint32_t len2 = (uint32_t)6U;
    uint64_t cin = t[len2];
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
    uint32_t len40 = (uint32_t)6U;
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
    uint32_t len4 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len4; i++)
    {
      uint64_t x_i = tempBuffer[i];
      uint64_t y_i = x_[i];
      uint64_t r_i = (y_i & mask) | (x_i & ~mask);
      a[i] = r_i;
    }
  }
}

static void montgomery_ladder_power_p256(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  p[0U] = (uint64_t)1U;
  p[1U] = (uint64_t)18446744069414584320U;
  p[2U] = (uint64_t)18446744073709551615U;
  p[3U] = (uint64_t)4294967294U;
  memcpy(a, result, (uint32_t)4U * sizeof (uint64_t));
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256) - (uint32_t)1U - i0;
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
    uint32_t resLen0 = len20 + len20;
    memset(t, 0U, resLen0 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len20; i1++)
    {
      uint64_t uu____0 = a[i1];
      uint64_t *res_ = t + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len20 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len20; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____0, res_ + i);
      }
      uint64_t r = c;
      t[len20 + i1] = r;
    }
    uint32_t len21 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len21; i1++)
    {
      uint32_t len3 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len3);
      uint64_t t2[(uint32_t)2U * len3];
      memset(t2, 0U, (uint32_t)2U * len3 * sizeof (uint64_t));
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
      uint64_t h080 = (uint64_t)(res0 >> (uint32_t)64U);
      o0[0U] = l00;
      temp = h080;
      uint64_t h0 = temp;
      uint128_t res = (uint128_t)f1 * t10;
      uint64_t l01 = (uint64_t)res;
      uint64_t h081 = (uint64_t)(res >> (uint32_t)64U);
      o1[0U] = l01;
      temp = h081;
      uint64_t l = o1[0U];
      uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
      uint64_t h = temp;
      o2[0U] = h + c1;
      uint128_t res1 = (uint128_t)f3 * t10;
      uint64_t l0 = (uint64_t)res1;
      uint64_t h08 = (uint64_t)(res1 >> (uint32_t)64U);
      o3[0U] = l0;
      o4[0U] = h08;
      uint32_t len40 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
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
      for (uint32_t i = k; i < len40; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
    uint32_t len3 = (uint32_t)4U;
    uint64_t cin = t[len3];
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
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = len50 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_0[(uint32_t)4U * i];
      uint64_t t20 = p10[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, tempBuffer + (uint32_t)4U * i);
      uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)1U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t10,
          t21,
          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p10[(uint32_t)4U * i + (uint32_t)2U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t11,
          t22,
          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p10[(uint32_t)4U * i + (uint32_t)3U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t12,
          t2,
          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < len50; i++)
    {
      uint64_t t1 = x_0[i];
      uint64_t t2 = p10[i];
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, tempBuffer + i);
    }
    uint64_t r = c0;
    uint64_t carry0 = r;
    uint64_t
    carry =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow0);
    uint64_t mask0 = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
    uint32_t len51 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len51; i++)
    {
      uint64_t x_i = tempBuffer[i];
      uint64_t y_i = x_0[i];
      uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
      a[i] = r_i;
    }
    uint32_t len12 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len12);
    uint64_t t0[(uint32_t)2U * len12];
    memset(t0, 0U, (uint32_t)2U * len12 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)4U;
    uint32_t resLen = len2 + len2;
    memset(t0, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *uu____1 = p;
      uint64_t uu____2 = p[i1];
      uint64_t *res_ = t0 + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = i1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, uu____1[(uint32_t)4U * i], uu____2, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            uu____1[(uint32_t)4U * i + (uint32_t)1U],
            uu____2,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            uu____1[(uint32_t)4U * i + (uint32_t)2U],
            uu____2,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            uu____1[(uint32_t)4U * i + (uint32_t)3U],
            uu____2,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i1; i++)
      {
        c = mul_carry_add_u64_st(c, uu____1[i], uu____2, res_ + i);
      }
      uint64_t r0 = c;
      t0[i1 + i1] = r0;
    }
    uint64_t c1 = (uint64_t)0U;
    uint32_t k1 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = t0[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = t0[(uint32_t)4U * i + (uint32_t)1U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = t0[(uint32_t)4U * i + (uint32_t)2U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = t0[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < resLen; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = t0[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t0 + i);
    }
    uint64_t uu____3 = c1;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
    uint64_t tmp[resLen];
    memset(tmp, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t a2 = (uint128_t)p[i] * p[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c2 = (uint64_t)0U;
    uint32_t k2 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = tmp[(uint32_t)4U * i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k2; i < resLen; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = tmp[i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, t0 + i);
    }
    uint64_t uu____4 = c2;
    uint32_t len22 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len22; i1++)
    {
      uint32_t len30 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len30);
      uint64_t t2[(uint32_t)2U * len30];
      memset(t2, 0U, (uint32_t)2U * len30 * sizeof (uint64_t));
      uint64_t t10 = t0[0U];
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
      uint64_t h080 = (uint64_t)(res0 >> (uint32_t)64U);
      o0[0U] = l00;
      temp = h080;
      uint64_t h0 = temp;
      uint128_t res = (uint128_t)f1 * t10;
      uint64_t l01 = (uint64_t)res;
      uint64_t h081 = (uint64_t)(res >> (uint32_t)64U);
      o1[0U] = l01;
      temp = h081;
      uint64_t l = o1[0U];
      uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
      uint64_t h = temp;
      o2[0U] = h + c10;
      uint128_t res1 = (uint128_t)f3 * t10;
      uint64_t l0 = (uint64_t)res1;
      uint64_t h08 = (uint64_t)(res1 >> (uint32_t)64U);
      o3[0U] = l0;
      o4[0U] = h08;
      uint32_t len41 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len41 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t11,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t12,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len41; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
      }
      uint64_t carry1 = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry1;
    }
    uint32_t len30 = (uint32_t)4U;
    uint64_t cin0 = t0[len30];
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
    uint32_t len52 = (uint32_t)4U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len52 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t20 = p1[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer0 + (uint32_t)4U * i);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t10,
          t21,
          tempBuffer0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t11,
          t22,
          tempBuffer0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t12,
          t2,
          tempBuffer0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len52; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t2 = p1[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer0 + i);
    }
    uint64_t r0 = c;
    uint64_t carry00 = r0;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    uint64_t mask1 = ~FStar_UInt64_eq_mask(carry1, (uint64_t)0U);
    uint32_t len5 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      uint64_t x_i = tempBuffer0[i];
      uint64_t y_i = x_[i];
      uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
      p[i] = r_i;
    }
    uint64_t mask2 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask2 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)4U * sizeof (uint64_t));
}

static void montgomery_ladder_power_p384(uint64_t *a, const uint8_t *scalar, uint64_t *result)
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
  memcpy(a, result, (uint32_t)6U * sizeof (uint64_t));
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384) - (uint32_t)1U - i0;
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
    uint32_t resLen0 = len20 + len20;
    memset(t, 0U, resLen0 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len20; i1++)
    {
      uint64_t uu____0 = a[i1];
      uint64_t *res_ = t + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len20 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len20; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____0, res_ + i);
      }
      uint64_t r = c;
      t[len20 + i1] = r;
    }
    uint32_t len21 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len21; i1++)
    {
      uint32_t len3 = (uint32_t)6U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len3);
      uint64_t t2[(uint32_t)2U * len3];
      memset(t2, 0U, (uint32_t)2U * len3 * sizeof (uint64_t));
      uint64_t k0 = (uint64_t)4294967297U;
      uint64_t t10 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      uint128_t res = (uint128_t)t10 * k0;
      uint64_t l0 = (uint64_t)res;
      uint64_t h08 = (uint64_t)(res >> (uint32_t)64U);
      y = l0;
      temp = h08;
      uint64_t y_ = y;
      uint64_t
      p1[6U] =
        {
          (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
          (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffffffffffU
        };
      uint32_t len40 = (uint32_t)6U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      uint32_t resLen = len40 + (uint32_t)1U;
      memset(partResult, 0U, resLen * sizeof (uint64_t));
      {
        uint64_t uu____1 = (&bBuffer)[0U];
        uint64_t *res_ = partResult;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, p1[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)1U],
              uu____1,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)2U],
              uu____1,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)3U],
              uu____1,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len40; i++)
        {
          c = mul_carry_add_u64_st(c, p1[i], uu____1, res_ + i);
        }
        uint64_t r = c;
        partResult[len40 + (uint32_t)0U] = r;
      }
      uint32_t len41 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len41 / (uint32_t)4U * (uint32_t)4U;
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
      for (uint32_t i = k; i < len41; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
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
    uint32_t len3 = (uint32_t)6U;
    uint64_t cin = t[len3];
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
    uint64_t c0 = (uint64_t)0U;
    uint32_t k1 = len50 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_0[(uint32_t)4U * i];
      uint64_t t20 = p10[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, tempBuffer + (uint32_t)4U * i);
      uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)1U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t10,
          t21,
          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p10[(uint32_t)4U * i + (uint32_t)2U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t11,
          t22,
          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p10[(uint32_t)4U * i + (uint32_t)3U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t12,
          t2,
          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < len50; i++)
    {
      uint64_t t1 = x_0[i];
      uint64_t t2 = p10[i];
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, tempBuffer + i);
    }
    uint64_t r = c0;
    uint64_t carry0 = r;
    uint64_t
    carry =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow0);
    uint64_t mask0 = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
    uint32_t len51 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len51; i++)
    {
      uint64_t x_i = tempBuffer[i];
      uint64_t y_i = x_0[i];
      uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
      a[i] = r_i;
    }
    uint32_t len12 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len12);
    uint64_t t0[(uint32_t)2U * len12];
    memset(t0, 0U, (uint32_t)2U * len12 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)6U;
    uint32_t resLen1 = len2 + len2;
    memset(t0, 0U, resLen1 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *uu____2 = p;
      uint64_t uu____3 = p[i1];
      uint64_t *res_ = t0 + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = i1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, uu____2[(uint32_t)4U * i], uu____3, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            uu____2[(uint32_t)4U * i + (uint32_t)1U],
            uu____3,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            uu____2[(uint32_t)4U * i + (uint32_t)2U],
            uu____3,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            uu____2[(uint32_t)4U * i + (uint32_t)3U],
            uu____3,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i1; i++)
      {
        c = mul_carry_add_u64_st(c, uu____2[i], uu____3, res_ + i);
      }
      uint64_t r0 = c;
      t0[i1 + i1] = r0;
    }
    uint64_t c1 = (uint64_t)0U;
    uint32_t k2 = resLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = t0[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = t0[(uint32_t)4U * i + (uint32_t)1U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = t0[(uint32_t)4U * i + (uint32_t)2U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = t0[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k2; i < resLen1; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = t0[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t0 + i);
    }
    uint64_t uu____4 = c1;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen1);
    uint64_t tmp[resLen1];
    memset(tmp, 0U, resLen1 * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t a2 = (uint128_t)p[i] * p[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c2 = (uint64_t)0U;
    uint32_t k3 = resLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k3 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = tmp[(uint32_t)4U * i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k3; i < resLen1; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = tmp[i];
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, t0 + i);
    }
    uint64_t uu____5 = c2;
    uint32_t len22 = (uint32_t)6U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len22; i1++)
    {
      uint32_t len30 = (uint32_t)6U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len30);
      uint64_t t2[(uint32_t)2U * len30];
      memset(t2, 0U, (uint32_t)2U * len30 * sizeof (uint64_t));
      uint64_t k0 = (uint64_t)4294967297U;
      uint64_t t10 = t0[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      uint128_t res = (uint128_t)t10 * k0;
      uint64_t l0 = (uint64_t)res;
      uint64_t h08 = (uint64_t)(res >> (uint32_t)64U);
      y = l0;
      temp = h08;
      uint64_t y_ = y;
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
      uint32_t resLen = len41 + (uint32_t)1U;
      memset(partResult, 0U, resLen * sizeof (uint64_t));
      {
        uint64_t uu____6 = (&bBuffer)[0U];
        uint64_t *res_ = partResult;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len41 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, p1[(uint32_t)4U * i], uu____6, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)1U],
              uu____6,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)2U],
              uu____6,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)3U],
              uu____6,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len41; i++)
        {
          c = mul_carry_add_u64_st(c, p1[i], uu____6, res_ + i);
        }
        uint64_t r0 = c;
        partResult[len41 + (uint32_t)0U] = r0;
      }
      uint32_t len42 = (uint32_t)6U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len42 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t11,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t12,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len42; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
      }
      uint64_t carry1 = c;
      uint32_t len4 = (uint32_t)11U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry1;
    }
    uint32_t len30 = (uint32_t)6U;
    uint64_t cin0 = t0[len30];
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
    uint32_t len52 = (uint32_t)6U;
    uint64_t c = (uint64_t)0U;
    uint32_t k = len52 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = x_[(uint32_t)4U * i];
      uint64_t t20 = p1[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer0 + (uint32_t)4U * i);
      uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t10,
          t21,
          tempBuffer0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t11,
          t22,
          tempBuffer0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t12,
          t2,
          tempBuffer0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len52; i++)
    {
      uint64_t t1 = x_[i];
      uint64_t t2 = p1[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer0 + i);
    }
    uint64_t r0 = c;
    uint64_t carry00 = r0;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    uint64_t mask1 = ~FStar_UInt64_eq_mask(carry1, (uint64_t)0U);
    uint32_t len5 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      uint64_t x_i = tempBuffer0[i];
      uint64_t y_i = x_[i];
      uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
      p[i] = r_i;
    }
    uint64_t mask2 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask2 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)6U * sizeof (uint64_t));
}

static void
montgomery_ladder_power_generic(uint64_t *a, const uint8_t *scalar, uint64_t *result)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    p[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t tempBuffer[len11];
  memset(tempBuffer, 0U, len11 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow0 = (uint64_t)0U;
  uint64_t carry00 = (uint64_t)0U;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
      (uint64_t)1U,
      (uint64_t)0U,
      &tempBufferForSubborrow0);
  uint64_t mask0 = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
  uint32_t len20 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    uint64_t x_i = tempBuffer[i];
    uint64_t y_i = p[i];
    uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
    p[i] = r_i;
  }
  memcpy(a, result, (uint32_t)4U * sizeof (uint64_t));
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default);
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default) - (uint32_t)1U - i0;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len12 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len12; i++)
    {
      uint64_t dummy = mask & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
    uint32_t len13 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len13);
    uint64_t t[(uint32_t)2U * len13];
    memset(t, 0U, (uint32_t)2U * len13 * sizeof (uint64_t));
    uint32_t len21 = (uint32_t)4U;
    uint32_t resLen0 = len21 + len21;
    memset(t, 0U, resLen0 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len21; i1++)
    {
      uint64_t uu____0 = a[i1];
      uint64_t *res_ = t + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len21 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len21; i++)
      {
        c = mul_carry_add_u64_st(c, p[i], uu____0, res_ + i);
      }
      uint64_t r = c;
      t[len21 + i1] = r;
    }
    uint32_t len22 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len22; i1++)
    {
      uint32_t len3 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len3);
      uint64_t t2[(uint32_t)2U * len3];
      memset(t2, 0U, (uint32_t)2U * len3 * sizeof (uint64_t));
      uint64_t k0 = mod_inv_u64((uint64_t)(uint32_t)1U);
      uint64_t t10 = t[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      uint128_t res = (uint128_t)t10 * k0;
      uint64_t l0 = (uint64_t)res;
      uint64_t h08 = (uint64_t)(res >> (uint32_t)64U);
      y = l0;
      temp = h08;
      uint64_t y_ = y;
      uint64_t
      p1[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len40 = (uint32_t)4U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      uint32_t resLen = len40 + (uint32_t)1U;
      memset(partResult, 0U, resLen * sizeof (uint64_t));
      {
        uint64_t uu____1 = (&bBuffer)[0U];
        uint64_t *res_ = partResult;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len40 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, p1[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)1U],
              uu____1,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)2U],
              uu____1,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)3U],
              uu____1,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len40; i++)
        {
          c = mul_carry_add_u64_st(c, p1[i], uu____1, res_ + i);
        }
        uint64_t r = c;
        partResult[len40 + (uint32_t)0U] = r;
      }
      uint32_t len41 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len41 / (uint32_t)4U * (uint32_t)4U;
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
      for (uint32_t i = k; i < len41; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
      }
      uint64_t carry0 = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t[i] = elem;
      }
      t[len4] = carry0;
    }
    uint32_t len3 = (uint32_t)4U;
    uint64_t cin = t[len3];
    uint64_t *x_0 = t;
    uint32_t len40 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len40);
    uint64_t tempBuffer0[len40];
    memset(tempBuffer0, 0U, len40 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow1 = (uint64_t)0U;
    uint64_t carry01 = (uint64_t)0U;
    uint64_t
    carry1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry01,
        cin,
        (uint64_t)0U,
        &tempBufferForSubborrow1);
    uint64_t mask1 = ~FStar_UInt64_eq_mask(carry1, (uint64_t)0U);
    uint32_t len50 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len50; i++)
    {
      uint64_t x_i = tempBuffer0[i];
      uint64_t y_i = x_0[i];
      uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
      a[i] = r_i;
    }
    uint32_t len14 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len14);
    uint64_t t0[(uint32_t)2U * len14];
    memset(t0, 0U, (uint32_t)2U * len14 * sizeof (uint64_t));
    uint32_t len2 = (uint32_t)4U;
    uint32_t resLen1 = len2 + len2;
    memset(t0, 0U, resLen1 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *uu____2 = p;
      uint64_t uu____3 = p[i1];
      uint64_t *res_ = t0 + i1;
      uint64_t c = (uint64_t)0U;
      uint32_t k = i1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c = mul_carry_add_u64_st(c, uu____2[(uint32_t)4U * i], uu____3, res_ + (uint32_t)4U * i);
        c =
          mul_carry_add_u64_st(c,
            uu____2[(uint32_t)4U * i + (uint32_t)1U],
            uu____3,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          mul_carry_add_u64_st(c,
            uu____2[(uint32_t)4U * i + (uint32_t)2U],
            uu____3,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          mul_carry_add_u64_st(c,
            uu____2[(uint32_t)4U * i + (uint32_t)3U],
            uu____3,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i1; i++)
      {
        c = mul_carry_add_u64_st(c, uu____2[i], uu____3, res_ + i);
      }
      uint64_t r = c;
      t0[i1 + i1] = r;
    }
    uint64_t c0 = (uint64_t)0U;
    uint32_t k1 = resLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = t0[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = t0[(uint32_t)4U * i + (uint32_t)1U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = t0[(uint32_t)4U * i + (uint32_t)2U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = t0[(uint32_t)4U * i + (uint32_t)3U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < resLen1; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = t0[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, t0 + i);
    }
    uint64_t uu____4 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen1);
    uint64_t tmp[resLen1];
    memset(tmp, 0U, resLen1 * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t a2 = (uint128_t)p[i] * p[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c1 = (uint64_t)0U;
    uint32_t k2 = resLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = tmp[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k2; i < resLen1; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = tmp[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, t0 + i);
    }
    uint64_t uu____5 = c1;
    uint32_t len23 = (uint32_t)4U;
    for (uint32_t i1 = (uint32_t)0U; i1 < len23; i1++)
    {
      uint32_t len30 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len30);
      uint64_t t2[(uint32_t)2U * len30];
      memset(t2, 0U, (uint32_t)2U * len30 * sizeof (uint64_t));
      uint64_t k0 = mod_inv_u64((uint64_t)(uint32_t)1U);
      uint64_t t10 = t0[0U];
      uint64_t y = (uint64_t)0U;
      uint64_t temp = (uint64_t)0U;
      uint128_t res = (uint128_t)t10 * k0;
      uint64_t l0 = (uint64_t)res;
      uint64_t h08 = (uint64_t)(res >> (uint32_t)64U);
      y = l0;
      temp = h08;
      uint64_t y_ = y;
      uint64_t
      p1[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len41 = (uint32_t)4U;
      uint64_t bBuffer = y_;
      uint64_t *partResult = t2;
      uint32_t resLen = len41 + (uint32_t)1U;
      memset(partResult, 0U, resLen * sizeof (uint64_t));
      {
        uint64_t uu____6 = (&bBuffer)[0U];
        uint64_t *res_ = partResult;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len41 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, p1[(uint32_t)4U * i], uu____6, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)1U],
              uu____6,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)2U],
              uu____6,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              p1[(uint32_t)4U * i + (uint32_t)3U],
              uu____6,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len41; i++)
        {
          c = mul_carry_add_u64_st(c, p1[i], uu____6, res_ + i);
        }
        uint64_t r = c;
        partResult[len41 + (uint32_t)0U] = r;
      }
      uint32_t len42 = (uint32_t)4U * (uint32_t)2U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len42 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t11,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c =
          Lib_IntTypes_Intrinsics_add_carry_u64(c,
            t12,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t13, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len42; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t2[i];
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
      }
      uint64_t carry0 = c;
      uint32_t len4 = (uint32_t)7U;
      for (uint32_t i = (uint32_t)0U; i < len4; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len4] = carry0;
    }
    uint32_t len30 = (uint32_t)4U;
    uint64_t cin0 = t0[len30];
    uint64_t *x_ = t0;
    uint32_t len4 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len4);
    uint64_t tempBuffer1[len4];
    memset(tempBuffer1, 0U, len4 * sizeof (uint64_t));
    uint64_t tempBufferForSubborrow = (uint64_t)0U;
    uint64_t carry0 = (uint64_t)0U;
    uint64_t
    carry2 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
        cin0,
        (uint64_t)0U,
        &tempBufferForSubborrow);
    uint64_t mask2 = ~FStar_UInt64_eq_mask(carry2, (uint64_t)0U);
    uint32_t len5 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len5; i++)
    {
      uint64_t x_i = tempBuffer1[i];
      uint64_t y_i = x_[i];
      uint64_t r_i = (y_i & mask2) | (x_i & ~mask2);
      p[i] = r_i;
    }
    uint64_t mask3 = (uint64_t)0U - bit;
    uint32_t len1 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = mask3 & (p[i] ^ a[i]);
      p[i] = p[i] ^ dummy;
      a[i] = a[i] ^ dummy;
    }
  }
  memcpy(result, p, (uint32_t)4U * sizeof (uint64_t));
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
  fsquarePowN_dh_p384((uint32_t)2U, t1);
  montgomery_multiplication_buffer_dh_p384(t0, t1, t1);
  montgomery_square_buffer_dh_p384(t1, t2);
  fsquarePowN_dh_p384((uint32_t)5U, t2);
  montgomery_multiplication_buffer_dh_p384(t2, t1, t2);
  montgomery_square_buffer_dh_p384(t2, t3);
  fsquarePowN_dh_p384((uint32_t)11U, t3);
  montgomery_multiplication_buffer_dh_p384(t2, t3, t2);
  fsquarePowN_dh_p384((uint32_t)6U, t2);
  montgomery_multiplication_buffer_dh_p384(t2, t1, t1);
  montgomery_square_buffer_dh_p384(t1, t2);
  montgomery_multiplication_buffer_dh_p384(t2, t, t2);
  montgomery_square_buffer_dh_p384(t2, t3);
  montgomery_multiplication_buffer_dh_p384(t, t3, t3);
  montgomery_square_buffer_dh_p384(t3, t4);
  fsquarePowN_dh_p384((uint32_t)30U, t4);
  montgomery_multiplication_buffer_dh_p384(t4, t2, t4);
  montgomery_square_buffer_dh_p384(t4, t5);
  fsquarePowN_dh_p384((uint32_t)62U, t5);
  montgomery_multiplication_buffer_dh_p384(t4, t5, t4);
  montgomery_square_buffer_dh_p384(t4, t5);
  fsquarePowN_dh_p384((uint32_t)125U, t5);
  montgomery_multiplication_buffer_dh_p384(t4, t5, t4);
  fsquarePowN_dh_p384((uint32_t)3U, t4);
  montgomery_multiplication_buffer_dh_p384(t4, t0, t4);
  fsquarePowN_dh_p384((uint32_t)33U, t4);
  montgomery_multiplication_buffer_dh_p384(t4, t3, t4);
  fsquarePowN_dh_p384((uint32_t)94U, t4);
  montgomery_multiplication_buffer_dh_p384(t4, t1, t4);
  fsquarePowN_dh_p384((uint32_t)2U, t4);
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

static void point_double_p256(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
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

static void point_double_p384(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
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

static void point_double_generic(uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
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
  uint64_t *alpha0 = tmp + (uint32_t)2U * coordinateLen;
  montgomery_square_buffer_dh_generic(pZ1, delta);
  montgomery_square_buffer_dh_generic(pY1, gamma);
  montgomery_multiplication_buffer_dh_generic(pX1, gamma, beta);
  alpha0[0U] = (uint64_t)18446744073709551612U;
  alpha0[1U] = (uint64_t)17179869183U;
  alpha0[2U] = (uint64_t)0U;
  alpha0[3U] = (uint64_t)18446744056529682436U;
  montgomery_square_buffer_dh_generic(delta, a0);
  montgomery_multiplication_buffer_dh_generic(alpha0, a0, a0);
  montgomery_square_buffer_dh_generic(pX1, alpha0);
  felem_add_generic(alpha0, alpha0, alpha);
  felem_add_generic(alpha0, alpha, alpha);
  felem_add_generic(alpha, a0, alpha);
  montgomery_square_buffer_dh_generic(alpha, x3);
  felem_add_generic(beta, beta, fourBeta);
  felem_add_generic(fourBeta, fourBeta, fourBeta);
  felem_add_generic(fourBeta, fourBeta, eightBeta);
  felem_sub_generic(x3, eightBeta, x3);
  felem_add_generic(pY, pZ, z3);
  montgomery_square_buffer_dh_generic(z3, z3);
  felem_sub_generic(z3, gamma, z3);
  felem_sub_generic(z3, delta, z3);
  felem_sub_generic(fourBeta, x3, y3);
  montgomery_multiplication_buffer_dh_generic(alpha, y3, y3);
  montgomery_square_buffer_dh_generic(gamma, gamma);
  felem_add_generic(gamma, gamma, eightGamma);
  felem_add_generic(eightGamma, eightGamma, eightGamma);
  felem_add_generic(eightGamma, eightGamma, eightGamma);
  felem_sub_generic(y3, eightGamma, y3);
}

static void point_add_p256(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
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

static void point_add_p384(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
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
  uint64_t *t40 = t12;
  uint64_t *u1 = t12 + (uint32_t)24U;
  uint64_t *u2 = t12 + (uint32_t)30U;
  uint64_t *s11 = t12 + (uint32_t)36U;
  uint64_t *s2 = t12 + (uint32_t)42U;
  uint64_t *h0 = t12 + (uint32_t)48U;
  uint64_t *r0 = t12 + (uint32_t)54U;
  uint64_t *uh0 = t12 + (uint32_t)60U;
  uint64_t *hCube0 = t12 + (uint32_t)66U;
  uint64_t *temp = t40;
  felem_sub_p384(u2, u1, h0);
  felem_sub_p384(s2, s11, r0);
  montgomery_square_buffer_dh_p384(h0, temp);
  montgomery_multiplication_buffer_dh_p384(temp, u1, uh0);
  montgomery_multiplication_buffer_dh_p384(temp, h0, hCube0);
  uint64_t *x3y3z3u1u2s1s2 = t12;
  uint64_t *rhuhhCube = t12 + (uint32_t)48U;
  uint64_t *h = rhuhhCube;
  uint64_t *r = rhuhhCube + (uint32_t)6U;
  uint64_t *uh = rhuhhCube + (uint32_t)12U;
  uint64_t *hCube = rhuhhCube + (uint32_t)18U;
  uint64_t *s1 = x3y3z3u1u2s1s2 + (uint32_t)36U;
  uint64_t *x3 = t5;
  uint64_t *tempBuffer30 = t5 + (uint32_t)6U;
  uint64_t *rSquare = tempBuffer30;
  uint64_t *rH = tempBuffer30 + (uint32_t)6U;
  uint64_t *twoUh = tempBuffer30 + (uint32_t)12U;
  montgomery_square_buffer_dh_p384(r, rSquare);
  felem_sub_p384(rSquare, hCube, rH);
  felem_add_p384(uh, uh, twoUh);
  felem_sub_p384(rH, twoUh, x3);
  uint64_t *x30 = t5;
  uint64_t *y3 = t5 + (uint32_t)6U;
  uint64_t *tempBuffer3 = t5 + (uint32_t)12U;
  uint64_t *s1hCube = tempBuffer3;
  uint64_t *u1hx3 = tempBuffer3 + (uint32_t)6U;
  uint64_t *ru1hx3 = tempBuffer3 + (uint32_t)12U;
  montgomery_multiplication_buffer_dh_p384(s1, hCube, s1hCube);
  felem_sub_p384(uh, x30, u1hx3);
  montgomery_multiplication_buffer_dh_p384(u1hx3, r, ru1hx3);
  felem_sub_p384(ru1hx3, s1hCube, y3);
  uint64_t *z1 = p + (uint32_t)12U;
  uint64_t *z2 = q + (uint32_t)12U;
  uint64_t *z3 = t5 + (uint32_t)12U;
  uint64_t *t1 = t5 + (uint32_t)18U;
  uint64_t *z1z2 = t1;
  montgomery_multiplication_buffer_dh_p384(z1, z2, z1z2);
  montgomery_multiplication_buffer_dh_p384(z1z2, h, z3);
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
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint64_t x_i = p_x0[i];
    uint64_t out_i = x3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    x3_out[i] = r_i;
  }
  uint32_t len2 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t x_i = p_y0[i];
    uint64_t out_i = y3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    y3_out[i] = r_i;
  }
  uint32_t len3 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len3; i++)
  {
    uint64_t x_i = p_z0[i];
    uint64_t out_i = z3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    z3_out[i] = r_i;
  }
  uint64_t *z0 = q + (uint32_t)12U;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len4 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
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
  uint32_t len = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t x_i = p_x[i];
    uint64_t out_i = x3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    x3_out[i] = r_i;
  }
  uint32_t len5 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len5; i++)
  {
    uint64_t x_i = p_y[i];
    uint64_t out_i = y3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    y3_out[i] = r_i;
  }
  uint32_t len6 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len6; i++)
  {
    uint64_t x_i = p_z[i];
    uint64_t out_i = z3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    z3_out[i] = r_i;
  }
  memcpy(result, x3_out, (uint32_t)6U * sizeof (uint64_t));
  memcpy(result + (uint32_t)6U, y3_out, (uint32_t)6U * sizeof (uint64_t));
  memcpy(result + (uint32_t)12U, z3_out, (uint32_t)6U * sizeof (uint64_t));
}

static void point_add_generic(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer)
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
  montgomery_square_buffer_dh_generic(qZ, z2Square);
  montgomery_square_buffer_dh_generic(pZ, z1Square);
  montgomery_multiplication_buffer_dh_generic(z2Square, qZ, z2Cube);
  montgomery_multiplication_buffer_dh_generic(z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer_dh_generic(z2Square, pX, u10);
  montgomery_multiplication_buffer_dh_generic(z1Square, qX, u20);
  montgomery_multiplication_buffer_dh_generic(z2Cube, pY, s10);
  montgomery_multiplication_buffer_dh_generic(z1Cube, qY, s20);
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
  felem_sub_generic(u2, u1, h0);
  felem_sub_generic(s2, s11, r0);
  montgomery_square_buffer_dh_generic(h0, temp);
  montgomery_multiplication_buffer_dh_generic(temp, u1, uh0);
  montgomery_multiplication_buffer_dh_generic(temp, h0, hCube0);
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
  montgomery_square_buffer_dh_generic(r, rSquare);
  felem_sub_generic(rSquare, hCube, rH);
  felem_add_generic(uh, uh, twoUh);
  felem_sub_generic(rH, twoUh, x3);
  uint64_t *x30 = t5;
  uint64_t *y3 = t5 + (uint32_t)4U;
  uint64_t *tempBuffer3 = t5 + (uint32_t)8U;
  uint64_t *s1hCube = tempBuffer3;
  uint64_t *u1hx3 = tempBuffer3 + (uint32_t)4U;
  uint64_t *ru1hx3 = tempBuffer3 + (uint32_t)8U;
  montgomery_multiplication_buffer_dh_generic(s1, hCube, s1hCube);
  felem_sub_generic(uh, x30, u1hx3);
  montgomery_multiplication_buffer_dh_generic(u1hx3, r, ru1hx3);
  felem_sub_generic(ru1hx3, s1hCube, y3);
  uint64_t *z1 = p + (uint32_t)8U;
  uint64_t *z2 = q + (uint32_t)8U;
  uint64_t *z3 = t5 + (uint32_t)8U;
  uint64_t *t1 = t5 + (uint32_t)12U;
  uint64_t *z1z2 = t1;
  montgomery_multiplication_buffer_dh_generic(z1, z2, z1z2);
  montgomery_multiplication_buffer_dh_generic(z1z2, h, z3);
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

static void reduction_p521(uint64_t *i)
{
  uint64_t a0[9U] = { 0U };
  uint64_t a1[9U] = { 0U };
  uint64_t a2[9U] = { 0U };
  uint64_t a3[27U] = { 0U };
  uint64_t *a3Part = a3;
  memcpy(a3Part, i, (uint32_t)18U * sizeof (uint64_t));
  uint64_t *iCopy = a3;
  uint64_t *oCopy = a0;
  memcpy(oCopy, iCopy, (uint32_t)8U * sizeof (uint64_t));
  uint64_t o8 = a3[8U];
  uint64_t o8Updated = o8 & (uint64_t)0x1ffU;
  a0[8U] = o8Updated;
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)0U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)0U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[0U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)1U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)1U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[1U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)2U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)2U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[2U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)3U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)3U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[3U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)4U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)4U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[4U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)5U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)5U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[5U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)6U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)6U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[6U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)7U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)7U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[7U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)8U + (uint32_t)8U];
    uint64_t i11 = a3[(uint32_t)9U + (uint32_t)8U];
    uint64_t i01 = i0 >> (uint32_t)9U;
    uint64_t i1U = i11 << (uint32_t)55U;
    uint64_t o0 = i01 ^ i1U;
    a1[8U] = o0;
  }
  uint64_t o80 = a1[8U];
  uint64_t o8Updated0 = o80 & (uint64_t)0x1ffU;
  a1[8U] = o8Updated0;
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)0U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)0U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[0U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)1U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)1U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[1U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)2U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)2U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[2U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)3U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)3U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[3U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)4U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)4U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[4U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)5U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)5U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[5U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)6U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)6U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[6U] = o0;
  }
  {
    uint64_t i0 = a3[(uint32_t)16U + (uint32_t)7U];
    uint64_t i11 = a3[(uint32_t)17U + (uint32_t)7U];
    uint64_t i01 = i0 >> (uint32_t)18U;
    uint64_t i1U = i11 << (uint32_t)46U;
    uint64_t o0 = i01 ^ i1U;
    a2[7U] = o0;
  }
  uint64_t o81 = a2[8U];
  uint64_t o8Updated1 = o81 & (uint64_t)0x1ffU;
  a2[8U] = o8Updated1;
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
  uint32_t k0 = len10 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k0 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t01[(uint32_t)4U * i8];
    uint64_t t220 = p0[(uint32_t)4U * i8];
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t12, t220, tempBuffer1 + (uint32_t)4U * i8);
    uint64_t t120 = t01[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p0[(uint32_t)4U * i8 + (uint32_t)1U];
    c16 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c16,
        t120,
        t221,
        tempBuffer1 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t01[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p0[(uint32_t)4U * i8 + (uint32_t)2U];
    c16 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c16,
        t121,
        t222,
        tempBuffer1 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t01[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p0[(uint32_t)4U * i8 + (uint32_t)3U];
    c16 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c16,
        t122,
        t22,
        tempBuffer1 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k0; i8 < len10; i8++)
  {
    uint64_t t12 = t01[i8];
    uint64_t t22 = p0[i8];
    c16 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c16, t12, t22, tempBuffer1 + i8);
  }
  uint64_t r = c16;
  uint64_t r0 = r;
  uint64_t mask = ~FStar_UInt64_eq_mask(r0, (uint64_t)0U);
  uint32_t len11 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len11; i8++)
  {
    uint64_t x_i = tempBuffer1[i8];
    uint64_t y_i = t01[i8];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    t01[i8] = r_i;
  }
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
  uint32_t len12 = (uint32_t)4U;
  uint64_t c17 = (uint64_t)0U;
  uint32_t k1 = len12 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k1 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t110[(uint32_t)4U * i8];
    uint64_t t220 = p1[(uint32_t)4U * i8];
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t12, t220, tempBuffer10 + (uint32_t)4U * i8);
    uint64_t t120 = t110[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p1[(uint32_t)4U * i8 + (uint32_t)1U];
    c17 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c17,
        t120,
        t221,
        tempBuffer10 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t110[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p1[(uint32_t)4U * i8 + (uint32_t)2U];
    c17 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c17,
        t121,
        t222,
        tempBuffer10 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t110[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p1[(uint32_t)4U * i8 + (uint32_t)3U];
    c17 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c17,
        t122,
        t22,
        tempBuffer10 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k1; i8 < len12; i8++)
  {
    uint64_t t12 = t110[i8];
    uint64_t t22 = p1[i8];
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t12, t22, tempBuffer10 + i8);
  }
  uint64_t r1 = c17;
  uint64_t r2 = r1;
  uint64_t mask0 = ~FStar_UInt64_eq_mask(r2, (uint64_t)0U);
  uint32_t len13 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len13; i8++)
  {
    uint64_t x_i = tempBuffer10[i8];
    uint64_t y_i = t110[i8];
    uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
    t110[i8] = r_i;
  }
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
  uint32_t len14 = (uint32_t)4U;
  uint64_t c18 = (uint64_t)0U;
  uint32_t k2 = len14 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k2 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t310[(uint32_t)4U * i8];
    uint64_t t220 = p2[(uint32_t)4U * i8];
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t12, t220, tempBuffer11 + (uint32_t)4U * i8);
    uint64_t t120 = t310[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p2[(uint32_t)4U * i8 + (uint32_t)1U];
    c18 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c18,
        t120,
        t221,
        tempBuffer11 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t310[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p2[(uint32_t)4U * i8 + (uint32_t)2U];
    c18 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c18,
        t121,
        t222,
        tempBuffer11 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t310[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p2[(uint32_t)4U * i8 + (uint32_t)3U];
    c18 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c18,
        t122,
        t22,
        tempBuffer11 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k2; i8 < len14; i8++)
  {
    uint64_t t12 = t310[i8];
    uint64_t t22 = p2[i8];
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t12, t22, tempBuffer11 + i8);
  }
  uint64_t r3 = c18;
  uint64_t r4 = r3;
  uint64_t mask1 = ~FStar_UInt64_eq_mask(r4, (uint64_t)0U);
  uint32_t len15 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len15; i8++)
  {
    uint64_t x_i = tempBuffer11[i8];
    uint64_t y_i = t310[i8];
    uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
    t310[i8] = r_i;
  }
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
  uint32_t len16 = (uint32_t)4U;
  uint64_t c19 = (uint64_t)0U;
  uint32_t k3 = len16 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k3 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t410[(uint32_t)4U * i8];
    uint64_t t220 = p3[(uint32_t)4U * i8];
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t12, t220, tempBuffer12 + (uint32_t)4U * i8);
    uint64_t t120 = t410[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p3[(uint32_t)4U * i8 + (uint32_t)1U];
    c19 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c19,
        t120,
        t221,
        tempBuffer12 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t410[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p3[(uint32_t)4U * i8 + (uint32_t)2U];
    c19 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c19,
        t121,
        t222,
        tempBuffer12 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t410[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p3[(uint32_t)4U * i8 + (uint32_t)3U];
    c19 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c19,
        t122,
        t22,
        tempBuffer12 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k3; i8 < len16; i8++)
  {
    uint64_t t12 = t410[i8];
    uint64_t t22 = p3[i8];
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t12, t22, tempBuffer12 + i8);
  }
  uint64_t r5 = c19;
  uint64_t r6 = r5;
  uint64_t mask2 = ~FStar_UInt64_eq_mask(r6, (uint64_t)0U);
  uint32_t len17 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len17; i8++)
  {
    uint64_t x_i = tempBuffer12[i8];
    uint64_t y_i = t410[i8];
    uint64_t r_i = (y_i & mask2) | (x_i & ~mask2);
    t410[i8] = r_i;
  }
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
  uint32_t len18 = (uint32_t)4U;
  uint64_t c20 = (uint64_t)0U;
  uint32_t k4 = len18 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k4 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t510[(uint32_t)4U * i8];
    uint64_t t220 = p4[(uint32_t)4U * i8];
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t12, t220, tempBuffer13 + (uint32_t)4U * i8);
    uint64_t t120 = t510[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p4[(uint32_t)4U * i8 + (uint32_t)1U];
    c20 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c20,
        t120,
        t221,
        tempBuffer13 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t510[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p4[(uint32_t)4U * i8 + (uint32_t)2U];
    c20 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c20,
        t121,
        t222,
        tempBuffer13 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t510[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p4[(uint32_t)4U * i8 + (uint32_t)3U];
    c20 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c20,
        t122,
        t22,
        tempBuffer13 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k4; i8 < len18; i8++)
  {
    uint64_t t12 = t510[i8];
    uint64_t t22 = p4[i8];
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t12, t22, tempBuffer13 + i8);
  }
  uint64_t r7 = c20;
  uint64_t r8 = r7;
  uint64_t mask3 = ~FStar_UInt64_eq_mask(r8, (uint64_t)0U);
  uint32_t len19 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len19; i8++)
  {
    uint64_t x_i = tempBuffer13[i8];
    uint64_t y_i = t510[i8];
    uint64_t r_i = (y_i & mask3) | (x_i & ~mask3);
    t510[i8] = r_i;
  }
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
  uint32_t len110 = (uint32_t)4U;
  uint64_t c21 = (uint64_t)0U;
  uint32_t k5 = len110 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k5 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t610[(uint32_t)4U * i8];
    uint64_t t220 = p5[(uint32_t)4U * i8];
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t12, t220, tempBuffer14 + (uint32_t)4U * i8);
    uint64_t t120 = t610[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p5[(uint32_t)4U * i8 + (uint32_t)1U];
    c21 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c21,
        t120,
        t221,
        tempBuffer14 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t610[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p5[(uint32_t)4U * i8 + (uint32_t)2U];
    c21 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c21,
        t121,
        t222,
        tempBuffer14 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t610[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p5[(uint32_t)4U * i8 + (uint32_t)3U];
    c21 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c21,
        t122,
        t22,
        tempBuffer14 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k5; i8 < len110; i8++)
  {
    uint64_t t12 = t610[i8];
    uint64_t t22 = p5[i8];
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t12, t22, tempBuffer14 + i8);
  }
  uint64_t r9 = c21;
  uint64_t r10 = r9;
  uint64_t mask4 = ~FStar_UInt64_eq_mask(r10, (uint64_t)0U);
  uint32_t len111 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len111; i8++)
  {
    uint64_t x_i = tempBuffer14[i8];
    uint64_t y_i = t610[i8];
    uint64_t r_i = (y_i & mask4) | (x_i & ~mask4);
    t610[i8] = r_i;
  }
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
  uint32_t len112 = (uint32_t)4U;
  uint64_t c22 = (uint64_t)0U;
  uint32_t k6 = len112 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k6 / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t710[(uint32_t)4U * i8];
    uint64_t t220 = p6[(uint32_t)4U * i8];
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t12, t220, tempBuffer15 + (uint32_t)4U * i8);
    uint64_t t120 = t710[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p6[(uint32_t)4U * i8 + (uint32_t)1U];
    c22 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c22,
        t120,
        t221,
        tempBuffer15 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t710[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p6[(uint32_t)4U * i8 + (uint32_t)2U];
    c22 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c22,
        t121,
        t222,
        tempBuffer15 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t710[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p6[(uint32_t)4U * i8 + (uint32_t)3U];
    c22 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c22,
        t122,
        t22,
        tempBuffer15 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k6; i8 < len112; i8++)
  {
    uint64_t t12 = t710[i8];
    uint64_t t22 = p6[i8];
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t12, t22, tempBuffer15 + i8);
  }
  uint64_t r11 = c22;
  uint64_t r12 = r11;
  uint64_t mask5 = ~FStar_UInt64_eq_mask(r12, (uint64_t)0U);
  uint32_t len113 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len113; i8++)
  {
    uint64_t x_i = tempBuffer15[i8];
    uint64_t y_i = t710[i8];
    uint64_t r_i = (y_i & mask5) | (x_i & ~mask5);
    t710[i8] = r_i;
  }
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
  uint32_t len114 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  uint32_t k = len114 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < k / (uint32_t)4U; i8++)
  {
    uint64_t t12 = t810[(uint32_t)4U * i8];
    uint64_t t220 = p[(uint32_t)4U * i8];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t220, tempBuffer16 + (uint32_t)4U * i8);
    uint64_t t120 = t810[(uint32_t)4U * i8 + (uint32_t)1U];
    uint64_t t221 = p[(uint32_t)4U * i8 + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t120,
        t221,
        tempBuffer16 + (uint32_t)4U * i8 + (uint32_t)1U);
    uint64_t t121 = t810[(uint32_t)4U * i8 + (uint32_t)2U];
    uint64_t t222 = p[(uint32_t)4U * i8 + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t121,
        t222,
        tempBuffer16 + (uint32_t)4U * i8 + (uint32_t)2U);
    uint64_t t122 = t810[(uint32_t)4U * i8 + (uint32_t)3U];
    uint64_t t22 = p[(uint32_t)4U * i8 + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t122,
        t22,
        tempBuffer16 + (uint32_t)4U * i8 + (uint32_t)3U);
  }
  for (uint32_t i8 = k; i8 < len114; i8++)
  {
    uint64_t t12 = t810[i8];
    uint64_t t22 = p[i8];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t22, tempBuffer16 + i8);
  }
  uint64_t r13 = c;
  uint64_t r14 = r13;
  uint64_t mask6 = ~FStar_UInt64_eq_mask(r14, (uint64_t)0U);
  uint32_t len1 = (uint32_t)4U;
  for (uint32_t i8 = (uint32_t)0U; i8 < len1; i8++)
  {
    uint64_t x_i = tempBuffer16[i8];
    uint64_t y_i = t810[i8];
    uint64_t r_i = (y_i & mask6) | (x_i & ~mask6);
    t810[i8] = r_i;
  }
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
  uint32_t k0 = len10 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k0 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t01[(uint32_t)4U * i12];
    uint64_t t220 = p0[(uint32_t)4U * i12];
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t12, t220, tempBuffer1 + (uint32_t)4U * i12);
    uint64_t t120 = t01[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p0[(uint32_t)4U * i12 + (uint32_t)1U];
    c24 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c24,
        t120,
        t221,
        tempBuffer1 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t01[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p0[(uint32_t)4U * i12 + (uint32_t)2U];
    c24 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c24,
        t121,
        t222,
        tempBuffer1 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t01[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p0[(uint32_t)4U * i12 + (uint32_t)3U];
    c24 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c24,
        t122,
        t22,
        tempBuffer1 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k0; i12 < len10; i12++)
  {
    uint64_t t12 = t01[i12];
    uint64_t t22 = p0[i12];
    c24 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c24, t12, t22, tempBuffer1 + i12);
  }
  uint64_t r = c24;
  uint64_t r0 = r;
  uint64_t mask = ~FStar_UInt64_eq_mask(r0, (uint64_t)0U);
  uint32_t len11 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len11; i12++)
  {
    uint64_t x_i = tempBuffer1[i12];
    uint64_t y_i = t01[i12];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    t01[i12] = r_i;
  }
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
  uint32_t len12 = (uint32_t)6U;
  uint64_t c25 = (uint64_t)0U;
  uint32_t k1 = len12 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k1 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t210[(uint32_t)4U * i12];
    uint64_t t220 = p1[(uint32_t)4U * i12];
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t12, t220, tempBuffer10 + (uint32_t)4U * i12);
    uint64_t t120 = t210[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p1[(uint32_t)4U * i12 + (uint32_t)1U];
    c25 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c25,
        t120,
        t221,
        tempBuffer10 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t210[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p1[(uint32_t)4U * i12 + (uint32_t)2U];
    c25 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c25,
        t121,
        t222,
        tempBuffer10 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t210[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p1[(uint32_t)4U * i12 + (uint32_t)3U];
    c25 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c25,
        t122,
        t22,
        tempBuffer10 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k1; i12 < len12; i12++)
  {
    uint64_t t12 = t210[i12];
    uint64_t t22 = p1[i12];
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t12, t22, tempBuffer10 + i12);
  }
  uint64_t r1 = c25;
  uint64_t r2 = r1;
  uint64_t mask0 = ~FStar_UInt64_eq_mask(r2, (uint64_t)0U);
  uint32_t len13 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len13; i12++)
  {
    uint64_t x_i = tempBuffer10[i12];
    uint64_t y_i = t210[i12];
    uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
    t210[i12] = r_i;
  }
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
  uint32_t len14 = (uint32_t)6U;
  uint64_t c26 = (uint64_t)0U;
  uint32_t k2 = len14 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k2 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t310[(uint32_t)4U * i12];
    uint64_t t220 = p2[(uint32_t)4U * i12];
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t12, t220, tempBuffer11 + (uint32_t)4U * i12);
    uint64_t t120 = t310[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p2[(uint32_t)4U * i12 + (uint32_t)1U];
    c26 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c26,
        t120,
        t221,
        tempBuffer11 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t310[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p2[(uint32_t)4U * i12 + (uint32_t)2U];
    c26 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c26,
        t121,
        t222,
        tempBuffer11 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t310[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p2[(uint32_t)4U * i12 + (uint32_t)3U];
    c26 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c26,
        t122,
        t22,
        tempBuffer11 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k2; i12 < len14; i12++)
  {
    uint64_t t12 = t310[i12];
    uint64_t t22 = p2[i12];
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t12, t22, tempBuffer11 + i12);
  }
  uint64_t r3 = c26;
  uint64_t r4 = r3;
  uint64_t mask1 = ~FStar_UInt64_eq_mask(r4, (uint64_t)0U);
  uint32_t len15 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len15; i12++)
  {
    uint64_t x_i = tempBuffer11[i12];
    uint64_t y_i = t310[i12];
    uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
    t310[i12] = r_i;
  }
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
  uint32_t len16 = (uint32_t)6U;
  uint64_t c27 = (uint64_t)0U;
  uint32_t k3 = len16 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k3 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t410[(uint32_t)4U * i12];
    uint64_t t220 = p3[(uint32_t)4U * i12];
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t12, t220, tempBuffer12 + (uint32_t)4U * i12);
    uint64_t t120 = t410[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p3[(uint32_t)4U * i12 + (uint32_t)1U];
    c27 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c27,
        t120,
        t221,
        tempBuffer12 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t410[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p3[(uint32_t)4U * i12 + (uint32_t)2U];
    c27 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c27,
        t121,
        t222,
        tempBuffer12 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t410[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p3[(uint32_t)4U * i12 + (uint32_t)3U];
    c27 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c27,
        t122,
        t22,
        tempBuffer12 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k3; i12 < len16; i12++)
  {
    uint64_t t12 = t410[i12];
    uint64_t t22 = p3[i12];
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t12, t22, tempBuffer12 + i12);
  }
  uint64_t r5 = c27;
  uint64_t r6 = r5;
  uint64_t mask2 = ~FStar_UInt64_eq_mask(r6, (uint64_t)0U);
  uint32_t len17 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len17; i12++)
  {
    uint64_t x_i = tempBuffer12[i12];
    uint64_t y_i = t410[i12];
    uint64_t r_i = (y_i & mask2) | (x_i & ~mask2);
    t410[i12] = r_i;
  }
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
  uint32_t len18 = (uint32_t)6U;
  uint64_t c28 = (uint64_t)0U;
  uint32_t k4 = len18 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k4 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t510[(uint32_t)4U * i12];
    uint64_t t220 = p4[(uint32_t)4U * i12];
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t12, t220, tempBuffer13 + (uint32_t)4U * i12);
    uint64_t t120 = t510[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p4[(uint32_t)4U * i12 + (uint32_t)1U];
    c28 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c28,
        t120,
        t221,
        tempBuffer13 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t510[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p4[(uint32_t)4U * i12 + (uint32_t)2U];
    c28 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c28,
        t121,
        t222,
        tempBuffer13 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t510[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p4[(uint32_t)4U * i12 + (uint32_t)3U];
    c28 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c28,
        t122,
        t22,
        tempBuffer13 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k4; i12 < len18; i12++)
  {
    uint64_t t12 = t510[i12];
    uint64_t t22 = p4[i12];
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t12, t22, tempBuffer13 + i12);
  }
  uint64_t r7 = c28;
  uint64_t r8 = r7;
  uint64_t mask3 = ~FStar_UInt64_eq_mask(r8, (uint64_t)0U);
  uint32_t len19 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len19; i12++)
  {
    uint64_t x_i = tempBuffer13[i12];
    uint64_t y_i = t510[i12];
    uint64_t r_i = (y_i & mask3) | (x_i & ~mask3);
    t510[i12] = r_i;
  }
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
  uint32_t len110 = (uint32_t)6U;
  uint64_t c29 = (uint64_t)0U;
  uint32_t k5 = len110 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k5 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t610[(uint32_t)4U * i12];
    uint64_t t220 = p5[(uint32_t)4U * i12];
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t12, t220, tempBuffer14 + (uint32_t)4U * i12);
    uint64_t t120 = t610[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p5[(uint32_t)4U * i12 + (uint32_t)1U];
    c29 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c29,
        t120,
        t221,
        tempBuffer14 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t610[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p5[(uint32_t)4U * i12 + (uint32_t)2U];
    c29 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c29,
        t121,
        t222,
        tempBuffer14 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t610[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p5[(uint32_t)4U * i12 + (uint32_t)3U];
    c29 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c29,
        t122,
        t22,
        tempBuffer14 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k5; i12 < len110; i12++)
  {
    uint64_t t12 = t610[i12];
    uint64_t t22 = p5[i12];
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t12, t22, tempBuffer14 + i12);
  }
  uint64_t r9 = c29;
  uint64_t r10 = r9;
  uint64_t mask4 = ~FStar_UInt64_eq_mask(r10, (uint64_t)0U);
  uint32_t len111 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len111; i12++)
  {
    uint64_t x_i = tempBuffer14[i12];
    uint64_t y_i = t610[i12];
    uint64_t r_i = (y_i & mask4) | (x_i & ~mask4);
    t610[i12] = r_i;
  }
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
  uint32_t len112 = (uint32_t)6U;
  uint64_t c30 = (uint64_t)0U;
  uint32_t k6 = len112 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k6 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t710[(uint32_t)4U * i12];
    uint64_t t220 = p6[(uint32_t)4U * i12];
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t12, t220, tempBuffer15 + (uint32_t)4U * i12);
    uint64_t t120 = t710[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p6[(uint32_t)4U * i12 + (uint32_t)1U];
    c30 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c30,
        t120,
        t221,
        tempBuffer15 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t710[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p6[(uint32_t)4U * i12 + (uint32_t)2U];
    c30 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c30,
        t121,
        t222,
        tempBuffer15 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t710[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p6[(uint32_t)4U * i12 + (uint32_t)3U];
    c30 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c30,
        t122,
        t22,
        tempBuffer15 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k6; i12 < len112; i12++)
  {
    uint64_t t12 = t710[i12];
    uint64_t t22 = p6[i12];
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t12, t22, tempBuffer15 + i12);
  }
  uint64_t r11 = c30;
  uint64_t r12 = r11;
  uint64_t mask5 = ~FStar_UInt64_eq_mask(r12, (uint64_t)0U);
  uint32_t len113 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len113; i12++)
  {
    uint64_t x_i = tempBuffer15[i12];
    uint64_t y_i = t710[i12];
    uint64_t r_i = (y_i & mask5) | (x_i & ~mask5);
    t710[i12] = r_i;
  }
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
  uint32_t len114 = (uint32_t)6U;
  uint64_t c31 = (uint64_t)0U;
  uint32_t k7 = len114 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k7 / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t810[(uint32_t)4U * i12];
    uint64_t t220 = p7[(uint32_t)4U * i12];
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t12, t220, tempBuffer16 + (uint32_t)4U * i12);
    uint64_t t120 = t810[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p7[(uint32_t)4U * i12 + (uint32_t)1U];
    c31 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c31,
        t120,
        t221,
        tempBuffer16 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t810[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p7[(uint32_t)4U * i12 + (uint32_t)2U];
    c31 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c31,
        t121,
        t222,
        tempBuffer16 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t810[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p7[(uint32_t)4U * i12 + (uint32_t)3U];
    c31 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c31,
        t122,
        t22,
        tempBuffer16 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k7; i12 < len114; i12++)
  {
    uint64_t t12 = t810[i12];
    uint64_t t22 = p7[i12];
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t12, t22, tempBuffer16 + i12);
  }
  uint64_t r13 = c31;
  uint64_t r14 = r13;
  uint64_t mask6 = ~FStar_UInt64_eq_mask(r14, (uint64_t)0U);
  uint32_t len115 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len115; i12++)
  {
    uint64_t x_i = tempBuffer16[i12];
    uint64_t y_i = t810[i12];
    uint64_t r_i = (y_i & mask6) | (x_i & ~mask6);
    t810[i12] = r_i;
  }
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
  uint32_t len116 = (uint32_t)6U;
  uint64_t c = (uint64_t)0U;
  uint32_t k = len116 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i12 = (uint32_t)0U; i12 < k / (uint32_t)4U; i12++)
  {
    uint64_t t12 = t910[(uint32_t)4U * i12];
    uint64_t t220 = p[(uint32_t)4U * i12];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t220, tempBuffer17 + (uint32_t)4U * i12);
    uint64_t t120 = t910[(uint32_t)4U * i12 + (uint32_t)1U];
    uint64_t t221 = p[(uint32_t)4U * i12 + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t120,
        t221,
        tempBuffer17 + (uint32_t)4U * i12 + (uint32_t)1U);
    uint64_t t121 = t910[(uint32_t)4U * i12 + (uint32_t)2U];
    uint64_t t222 = p[(uint32_t)4U * i12 + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t121,
        t222,
        tempBuffer17 + (uint32_t)4U * i12 + (uint32_t)2U);
    uint64_t t122 = t910[(uint32_t)4U * i12 + (uint32_t)3U];
    uint64_t t22 = p[(uint32_t)4U * i12 + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t122,
        t22,
        tempBuffer17 + (uint32_t)4U * i12 + (uint32_t)3U);
  }
  for (uint32_t i12 = k; i12 < len116; i12++)
  {
    uint64_t t12 = t910[i12];
    uint64_t t22 = p[i12];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t22, tempBuffer17 + i12);
  }
  uint64_t r15 = c;
  uint64_t r16 = r15;
  uint64_t mask7 = ~FStar_UInt64_eq_mask(r16, (uint64_t)0U);
  uint32_t len1 = (uint32_t)6U;
  for (uint32_t i12 = (uint32_t)0U; i12 < len1; i12++)
  {
    uint64_t x_i = tempBuffer17[i12];
    uint64_t y_i = t910[i12];
    uint64_t r_i = (y_i & mask7) | (x_i & ~mask7);
    t910[i12] = r_i;
  }
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

static inline void reduction(Spec_ECC_Curves_curve c, uint64_t *i, uint64_t *o)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        solinas_reduction_impl_p256(i, o);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        solinas_reduction_impl_p384(i, o);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        reduction_p521(i);
        break;
      }
    default:
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
        uint64_t t[len];
        memset(t, 0U, len * sizeof (uint64_t));
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
          KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len3);
          uint64_t t2[(uint32_t)2U * len3];
          memset(t2, 0U, (uint32_t)2U * len3 * sizeof (uint64_t));
          uint64_t sw0;
          switch (c)
          {
            case Spec_ECC_Curves_P256:
              {
                sw0 = (uint64_t)(void *)(uint64_t)0xffffffffffffffffU;
                break;
              }
            case Spec_ECC_Curves_P384:
              {
                sw0 = (uint64_t)(void *)(uint64_t)0xffffffffU;
                break;
              }
            default:
              {
                sw0 = (uint64_t)(void *)(uint32_t)1U;
              }
          }
          if (FStar_UInt64_v(sw0) == (krml_checked_int_t)18446744073709551615)
          {
            uint64_t t1 = i[0U];
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
                  uint128_t res0 = (uint128_t)f0 * t1;
                  uint64_t l00 = (uint64_t)res0;
                  uint64_t h040 = (uint64_t)(res0 >> (uint32_t)64U);
                  o0[0U] = l00;
                  temp = h040;
                  uint64_t h0 = temp;
                  uint128_t res = (uint128_t)f1 * t1;
                  uint64_t l01 = (uint64_t)res;
                  uint64_t h041 = (uint64_t)(res >> (uint32_t)64U);
                  o1[0U] = l01;
                  temp = h041;
                  uint64_t l = o1[0U];
                  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
                  uint64_t h = temp;
                  o2[0U] = h + c1;
                  uint128_t res1 = (uint128_t)f3 * t1;
                  uint64_t l0 = (uint64_t)res1;
                  uint64_t h04 = (uint64_t)(res1 >> (uint32_t)64U);
                  o3[0U] = l0;
                  o4[0U] = h04;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  uint64_t
                  p[6U] =
                    {
                      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U,
                      (uint64_t)0xfffffffffffffffeU, (uint64_t)0xffffffffffffffffU,
                      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
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
                  uint64_t bBuffer = t1;
                  uint64_t *partResult = t2;
                  uint32_t resLen = len4 + (uint32_t)1U;
                  memset(partResult, 0U, resLen * sizeof (uint64_t));
                  {
                    uint64_t uu____0 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i1 = (uint32_t)0U; i1 < k / (uint32_t)4U; i1++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1],
                          uu____0,
                          res_ + (uint32_t)4U * i1);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)1U],
                          uu____0,
                          res_ + (uint32_t)4U * i1 + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)2U],
                          uu____0,
                          res_ + (uint32_t)4U * i1 + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)3U],
                          uu____0,
                          res_ + (uint32_t)4U * i1 + (uint32_t)3U);
                    }
                    for (uint32_t i1 = k; i1 < len4; i1++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p[i1], uu____0, res_ + i1);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                  break;
                }
              default:
                {
                  uint64_t
                  p[4U] =
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
                  uint64_t bBuffer = t1;
                  uint64_t *partResult = t2;
                  uint32_t resLen = len4 + (uint32_t)1U;
                  memset(partResult, 0U, resLen * sizeof (uint64_t));
                  {
                    uint64_t uu____1 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i1 = (uint32_t)0U; i1 < k / (uint32_t)4U; i1++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1],
                          uu____1,
                          res_ + (uint32_t)4U * i1);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)1U],
                          uu____1,
                          res_ + (uint32_t)4U * i1 + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)2U],
                          uu____1,
                          res_ + (uint32_t)4U * i1 + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)3U],
                          uu____1,
                          res_ + (uint32_t)4U * i1 + (uint32_t)3U);
                    }
                    for (uint32_t i1 = k; i1 < len4; i1++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p[i1], uu____1, res_ + i1);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
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
              case Spec_ECC_Curves_Default:
                {
                  uint64_t sw;
                  switch (c)
                  {
                    case Spec_ECC_Curves_P256:
                      {
                        sw = (uint64_t)(void *)(uint64_t)0xffffffffffffffffU;
                        break;
                      }
                    case Spec_ECC_Curves_P384:
                      {
                        sw = (uint64_t)(void *)(uint64_t)0xffffffffU;
                        break;
                      }
                    default:
                      {
                        sw = (uint64_t)(void *)(uint32_t)1U;
                      }
                  }
                  k0 = mod_inv_u64(sw);
                  break;
                }
              default:
                {
                  KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                  KRML_HOST_EXIT(253U);
                }
            }
            uint64_t t1 = i[0U];
            uint64_t y = (uint64_t)0U;
            uint64_t temp = (uint64_t)0U;
            uint128_t res0 = (uint128_t)t1 * k0;
            uint64_t l00 = (uint64_t)res0;
            uint64_t h04 = (uint64_t)(res0 >> (uint32_t)64U);
            y = l00;
            temp = h04;
            uint64_t y_ = y;
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
                  uint128_t res1 = (uint128_t)f0 * y_;
                  uint64_t l01 = (uint64_t)res1;
                  uint64_t h050 = (uint64_t)(res1 >> (uint32_t)64U);
                  o0[0U] = l01;
                  temp1 = h050;
                  uint64_t h2 = temp1;
                  uint128_t res = (uint128_t)f1 * y_;
                  uint64_t l02 = (uint64_t)res;
                  uint64_t h051 = (uint64_t)(res >> (uint32_t)64U);
                  o1[0U] = l02;
                  temp1 = h051;
                  uint64_t l = o1[0U];
                  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h2, o1);
                  uint64_t h3 = temp1;
                  o2[0U] = h3 + c1;
                  uint128_t res2 = (uint128_t)f3 * y_;
                  uint64_t l0 = (uint64_t)res2;
                  uint64_t h05 = (uint64_t)(res2 >> (uint32_t)64U);
                  o3[0U] = l0;
                  o4[0U] = h05;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  uint64_t
                  p[6U] =
                    {
                      (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U,
                      (uint64_t)0xfffffffffffffffeU, (uint64_t)0xffffffffffffffffU,
                      (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
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
                  uint64_t bBuffer = y_;
                  uint64_t *partResult = t2;
                  uint32_t resLen = len4 + (uint32_t)1U;
                  memset(partResult, 0U, resLen * sizeof (uint64_t));
                  {
                    uint64_t uu____2 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i1 = (uint32_t)0U; i1 < k / (uint32_t)4U; i1++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1],
                          uu____2,
                          res_ + (uint32_t)4U * i1);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)1U],
                          uu____2,
                          res_ + (uint32_t)4U * i1 + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)2U],
                          uu____2,
                          res_ + (uint32_t)4U * i1 + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)3U],
                          uu____2,
                          res_ + (uint32_t)4U * i1 + (uint32_t)3U);
                    }
                    for (uint32_t i1 = k; i1 < len4; i1++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p[i1], uu____2, res_ + i1);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                  break;
                }
              default:
                {
                  uint64_t
                  p[4U] =
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
                  uint64_t bBuffer = y_;
                  uint64_t *partResult = t2;
                  uint32_t resLen = len4 + (uint32_t)1U;
                  memset(partResult, 0U, resLen * sizeof (uint64_t));
                  {
                    uint64_t uu____3 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i1 = (uint32_t)0U; i1 < k / (uint32_t)4U; i1++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1],
                          uu____3,
                          res_ + (uint32_t)4U * i1);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)1U],
                          uu____3,
                          res_ + (uint32_t)4U * i1 + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)2U],
                          uu____3,
                          res_ + (uint32_t)4U * i1 + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p[(uint32_t)4U * i1 + (uint32_t)3U],
                          uu____3,
                          res_ + (uint32_t)4U * i1 + (uint32_t)3U);
                    }
                    for (uint32_t i1 = k; i1 < len4; i1++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p[i1], uu____3, res_ + i1);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                }
            }
          }
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
          uint32_t len4 = sw1 * (uint32_t)2U;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i1 = (uint32_t)0U; i1 < k / (uint32_t)4U; i1++)
          {
            uint64_t t1 = i[(uint32_t)4U * i1];
            uint64_t t210 = t2[(uint32_t)4U * i1];
            c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i1);
            uint64_t t10 = i[(uint32_t)4U * i1 + (uint32_t)1U];
            uint64_t t211 = t2[(uint32_t)4U * i1 + (uint32_t)1U];
            c1 =
              Lib_IntTypes_Intrinsics_add_carry_u64(c1,
                t10,
                t211,
                t2 + (uint32_t)4U * i1 + (uint32_t)1U);
            uint64_t t11 = i[(uint32_t)4U * i1 + (uint32_t)2U];
            uint64_t t212 = t2[(uint32_t)4U * i1 + (uint32_t)2U];
            c1 =
              Lib_IntTypes_Intrinsics_add_carry_u64(c1,
                t11,
                t212,
                t2 + (uint32_t)4U * i1 + (uint32_t)2U);
            uint64_t t12 = i[(uint32_t)4U * i1 + (uint32_t)3U];
            uint64_t t21 = t2[(uint32_t)4U * i1 + (uint32_t)3U];
            c1 =
              Lib_IntTypes_Intrinsics_add_carry_u64(c1,
                t12,
                t21,
                t2 + (uint32_t)4U * i1 + (uint32_t)3U);
          }
          for (uint32_t i1 = k; i1 < len4; i1++)
          {
            uint64_t t1 = i[i1];
            uint64_t t21 = t2[i1];
            c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i1);
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
          uint32_t len40 = sw * (uint32_t)2U - (uint32_t)1U;
          for (uint32_t i1 = (uint32_t)0U; i1 < len40; i1++)
          {
            uint64_t elem = t2[(uint32_t)1U + i1];
            i[i1] = elem;
          }
          i[len40] = carry;
        }
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
        uint64_t cin = i[len3];
        uint64_t *x_ = i;
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
        KRML_CHECK_SIZE(sizeof (uint64_t), len4);
        uint64_t tempBuffer[len4];
        memset(tempBuffer, 0U, len4 * sizeof (uint64_t));
        uint64_t tempBufferForSubborrow = (uint64_t)0U;
        uint64_t carry0;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              uint64_t
              p[4U] =
                {
                  (uint64_t)0xffffffffffffffffU,
                  (uint64_t)0xffffffffU,
                  (uint64_t)0U,
                  (uint64_t)0xffffffff00000001U
                };
              uint32_t len5;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    len5 = (uint32_t)4U;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    len5 = (uint32_t)6U;
                    break;
                  }
                default:
                  {
                    len5 = (uint32_t)4U;
                  }
              }
              uint64_t c1 = (uint64_t)0U;
              uint32_t k = len5 / (uint32_t)4U * (uint32_t)4U;
              for (uint32_t i0 = (uint32_t)0U; i0 < k / (uint32_t)4U; i0++)
              {
                uint64_t t1 = x_[(uint32_t)4U * i0];
                uint64_t t20 = p[(uint32_t)4U * i0];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t1,
                    t20,
                    tempBuffer + (uint32_t)4U * i0);
                uint64_t t10 = x_[(uint32_t)4U * i0 + (uint32_t)1U];
                uint64_t t21 = p[(uint32_t)4U * i0 + (uint32_t)1U];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t10,
                    t21,
                    tempBuffer + (uint32_t)4U * i0 + (uint32_t)1U);
                uint64_t t11 = x_[(uint32_t)4U * i0 + (uint32_t)2U];
                uint64_t t22 = p[(uint32_t)4U * i0 + (uint32_t)2U];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t11,
                    t22,
                    tempBuffer + (uint32_t)4U * i0 + (uint32_t)2U);
                uint64_t t12 = x_[(uint32_t)4U * i0 + (uint32_t)3U];
                uint64_t t2 = p[(uint32_t)4U * i0 + (uint32_t)3U];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t12,
                    t2,
                    tempBuffer + (uint32_t)4U * i0 + (uint32_t)3U);
              }
              for (uint32_t i0 = k; i0 < len5; i0++)
              {
                uint64_t t1 = x_[i0];
                uint64_t t2 = p[i0];
                c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i0);
              }
              uint64_t r = c1;
              carry0 = r;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              uint64_t
              p[6U] =
                {
                  (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U,
                  (uint64_t)0xfffffffffffffffeU, (uint64_t)0xffffffffffffffffU,
                  (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
                };
              uint32_t len5;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    len5 = (uint32_t)4U;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    len5 = (uint32_t)6U;
                    break;
                  }
                default:
                  {
                    len5 = (uint32_t)4U;
                  }
              }
              uint64_t c1 = (uint64_t)0U;
              uint32_t k = len5 / (uint32_t)4U * (uint32_t)4U;
              for (uint32_t i0 = (uint32_t)0U; i0 < k / (uint32_t)4U; i0++)
              {
                uint64_t t1 = x_[(uint32_t)4U * i0];
                uint64_t t20 = p[(uint32_t)4U * i0];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t1,
                    t20,
                    tempBuffer + (uint32_t)4U * i0);
                uint64_t t10 = x_[(uint32_t)4U * i0 + (uint32_t)1U];
                uint64_t t21 = p[(uint32_t)4U * i0 + (uint32_t)1U];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t10,
                    t21,
                    tempBuffer + (uint32_t)4U * i0 + (uint32_t)1U);
                uint64_t t11 = x_[(uint32_t)4U * i0 + (uint32_t)2U];
                uint64_t t22 = p[(uint32_t)4U * i0 + (uint32_t)2U];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t11,
                    t22,
                    tempBuffer + (uint32_t)4U * i0 + (uint32_t)2U);
                uint64_t t12 = x_[(uint32_t)4U * i0 + (uint32_t)3U];
                uint64_t t2 = p[(uint32_t)4U * i0 + (uint32_t)3U];
                c1 =
                  Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                    t12,
                    t2,
                    tempBuffer + (uint32_t)4U * i0 + (uint32_t)3U);
              }
              for (uint32_t i0 = k; i0 < len5; i0++)
              {
                uint64_t t1 = x_[i0];
                uint64_t t2 = p[i0];
                c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i0);
              }
              uint64_t r = c1;
              carry0 = r;
              break;
            }
          default:
            {
              carry0 = (uint64_t)0U;
            }
        }
        uint64_t
        carry =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
            cin,
            (uint64_t)0U,
            &tempBufferForSubborrow);
        uint64_t mask = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
        uint32_t len5;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              len5 = (uint32_t)4U;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              len5 = (uint32_t)6U;
              break;
            }
          default:
            {
              len5 = (uint32_t)4U;
            }
        }
        for (uint32_t i0 = (uint32_t)0U; i0 < len5; i0++)
        {
          uint64_t x_i = tempBuffer[i0];
          uint64_t y_i = x_[i0];
          uint64_t r_i = (y_i & mask) | (x_i & ~mask);
          o[i0] = r_i;
        }
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              montgomery_multiplication_buffer_dh_p256(t, o, o);
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              montgomery_multiplication_buffer_dh_p384(t, o, o);
              break;
            }
          case Spec_ECC_Curves_Default:
            {
              montgomery_multiplication_buffer_dh_generic(t, o, o);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
      }
  }
}

static inline void
norm(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *resultPoint, uint64_t *tempBuffer)
{
  uint64_t *xf = p;
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
  uint64_t *yf = p + sw0;
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
  uint64_t *zf = p + (uint32_t)2U * sw1;
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
  uint64_t *z2f = tempBuffer + sw2;
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
  uint64_t *z3f = tempBuffer + (uint32_t)2U * sw3;
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
  uint64_t *t8 = tempBuffer + (uint32_t)3U * sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_square_buffer_dh_p256(zf, z2f);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_square_buffer_dh_p384(zf, z2f);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_square_buffer_dh_generic(zf, z2f);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(z2f, zf, z3f);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(z2f, zf, z3f);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_multiplication_buffer_dh_generic(z2f, zf, z3f);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        exponent_p256(z2f, z2f, t8);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        exponent_p384(z2f, z2f, t8);
        break;
      }
    default:
      {
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              const uint8_t *sw4;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw4 = prime256_inverse_buffer;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw4 = prime384_inverse_buffer;
                    break;
                  }
                default:
                  {
                    sw4 = prime256_inverse_buffer;
                  }
              }
              montgomery_ladder_power_p256(z2f, sw4, z2f);
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              const uint8_t *sw4;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw4 = prime256_inverse_buffer;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw4 = prime384_inverse_buffer;
                    break;
                  }
                default:
                  {
                    sw4 = prime256_inverse_buffer;
                  }
              }
              montgomery_ladder_power_p384(z2f, sw4, z2f);
              break;
            }
          case Spec_ECC_Curves_Default:
            {
              const uint8_t *sw4;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw4 = prime256_inverse_buffer;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw4 = prime384_inverse_buffer;
                    break;
                  }
                default:
                  {
                    sw4 = prime256_inverse_buffer;
                  }
              }
              montgomery_ladder_power_generic(z2f, sw4, z2f);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        exponent_p256(z3f, z3f, t8);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        exponent_p384(z3f, z3f, t8);
        break;
      }
    default:
      {
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              const uint8_t *sw4;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw4 = prime256_inverse_buffer;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw4 = prime384_inverse_buffer;
                    break;
                  }
                default:
                  {
                    sw4 = prime256_inverse_buffer;
                  }
              }
              montgomery_ladder_power_p256(z3f, sw4, z3f);
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              const uint8_t *sw4;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw4 = prime256_inverse_buffer;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw4 = prime384_inverse_buffer;
                    break;
                  }
                default:
                  {
                    sw4 = prime256_inverse_buffer;
                  }
              }
              montgomery_ladder_power_p384(z3f, sw4, z3f);
              break;
            }
          case Spec_ECC_Curves_Default:
            {
              const uint8_t *sw4;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw4 = prime256_inverse_buffer;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw4 = prime384_inverse_buffer;
                    break;
                  }
                default:
                  {
                    sw4 = prime256_inverse_buffer;
                  }
              }
              montgomery_ladder_power_generic(z3f, sw4, z3f);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(xf, z2f, z2f);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(xf, z2f, z2f);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_multiplication_buffer_dh_generic(xf, z2f, z2f);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(yf, z3f, z3f);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(yf, z3f, z3f);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_multiplication_buffer_dh_generic(yf, z3f, z3f);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
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
  uint64_t zeroBuffer[len];
  memset(zeroBuffer, 0U, len * sizeof (uint64_t));
  uint64_t *resultX = resultPoint;
  uint64_t *resultY = resultPoint + len;
  uint64_t *resultZ = resultPoint + (uint32_t)2U * len;
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
  uint32_t start = len10 * (uint32_t)2U;
  uint64_t *zCoordinate = p + start;
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
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t bit = r;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_by_one_dh_p256(z2f, resultX);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_by_one_dh_p384(z2f, resultX);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_multiplication_buffer_by_one_dh_generic(z2f, resultX);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_by_one_dh_p256(z3f, resultY);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_by_one_dh_p384(z3f, resultY);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_multiplication_buffer_by_one_dh_generic(z3f, resultY);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  resultZ[0U] = (uint64_t)1U;
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
  for (uint32_t i = (uint32_t)1U; i < len1; i++)
  {
    resultZ[i] = (uint64_t)0U;
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
    uint64_t x_i = zeroBuffer[i];
    uint64_t out_i = resultZ[i];
    uint64_t r_i = out_i ^ (bit & (out_i ^ x_i));
    resultZ[i] = r_i;
  }
}

static inline void
scalarMultiplicationWithoutNorm(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *result,
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
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
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
  uint64_t *x = q;
  uint64_t *y = q + len10;
  uint64_t *z = q + (uint32_t)2U * len10;
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
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    x[i] = (uint64_t)0U;
  }
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
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    y[i] = (uint64_t)0U;
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
  for (uint32_t i = (uint32_t)0U; i < len22; i++)
  {
    z[i] = (uint64_t)0U;
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
  uint64_t *p_x = p;
  uint64_t *p_y = p + len11;
  uint64_t *p_z = p + (uint32_t)2U * len11;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len11;
  uint64_t *r_z = result + (uint32_t)2U * len11;
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
  uint64_t multBuffer[(uint32_t)2U * len2];
  memset(multBuffer, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
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
  uint64_t *oToZero0 = multBuffer;
  uint64_t *oToCopy0 = multBuffer + len30;
  memcpy(oToCopy0, p_x, len30 * sizeof (uint64_t));
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
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    oToZero0[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer, r_x);
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len23);
  uint64_t multBuffer0[(uint32_t)2U * len23];
  memset(multBuffer0, 0U, (uint32_t)2U * len23 * sizeof (uint64_t));
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
  uint64_t *oToZero1 = multBuffer0;
  uint64_t *oToCopy1 = multBuffer0 + len31;
  memcpy(oToCopy1, p_y, len31 * sizeof (uint64_t));
  uint32_t len40;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len40 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len40 = (uint32_t)6U;
        break;
      }
    default:
      {
        len40 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len40; i++)
  {
    oToZero1[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer0, r_y);
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len24);
  uint64_t multBuffer1[(uint32_t)2U * len24];
  memset(multBuffer1, 0U, (uint32_t)2U * len24 * sizeof (uint64_t));
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
  uint64_t *oToZero = multBuffer1;
  uint64_t *oToCopy = multBuffer1 + len3;
  memcpy(oToCopy, p_z, len3 * sizeof (uint64_t));
  uint32_t len41;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len41 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len41 = (uint32_t)6U;
        break;
      }
    default:
      {
        len41 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len41; i++)
  {
    oToZero[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer1, r_z);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
        for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
        {
          uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256) - (uint32_t)1U - i0;
          uint64_t
          bit =
            (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
            * (uint32_t)8U
            - (uint32_t)1U
            - bit0 / (uint32_t)8U]
            >> bit0 % (uint32_t)8U
            & (uint8_t)1U);
          uint64_t mask = (uint64_t)0U - bit;
          uint32_t len12 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len12; i++)
          {
            uint64_t dummy = mask & (q[i] ^ result[i]);
            q[i] = q[i] ^ dummy;
            result[i] = result[i] ^ dummy;
          }
          point_add_p256(q, result, result, buff);
          point_double_p256(q, q, buff);
          uint64_t mask0 = (uint64_t)0U - bit;
          uint32_t len1 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len1; i++)
          {
            uint64_t dummy = mask0 & (q[i] ^ result[i]);
            q[i] = q[i] ^ dummy;
            result[i] = result[i] ^ dummy;
          }
        }
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
        for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
        {
          uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384) - (uint32_t)1U - i0;
          uint64_t
          bit =
            (uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
            * (uint32_t)8U
            - (uint32_t)1U
            - bit0 / (uint32_t)8U]
            >> bit0 % (uint32_t)8U
            & (uint8_t)1U);
          uint64_t mask = (uint64_t)0U - bit;
          uint32_t len12 = (uint32_t)18U;
          for (uint32_t i = (uint32_t)0U; i < len12; i++)
          {
            uint64_t dummy = mask & (q[i] ^ result[i]);
            q[i] = q[i] ^ dummy;
            result[i] = result[i] ^ dummy;
          }
          point_add_p384(q, result, result, buff);
          point_double_p384(q, q, buff);
          uint64_t mask0 = (uint64_t)0U - bit;
          uint32_t len1 = (uint32_t)18U;
          for (uint32_t i = (uint32_t)0U; i < len1; i++)
          {
            uint64_t dummy = mask0 & (q[i] ^ result[i]);
            q[i] = q[i] ^ dummy;
            result[i] = result[i] ^ dummy;
          }
        }
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default);
        for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
        {
          uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default) - (uint32_t)1U - i0;
          uint64_t
          bit =
            (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
            * (uint32_t)8U
            - (uint32_t)1U
            - bit0 / (uint32_t)8U]
            >> bit0 % (uint32_t)8U
            & (uint8_t)1U);
          uint64_t mask = (uint64_t)0U - bit;
          uint32_t len12 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len12; i++)
          {
            uint64_t dummy = mask & (q[i] ^ result[i]);
            q[i] = q[i] ^ dummy;
            result[i] = result[i] ^ dummy;
          }
          point_add_generic(q, result, result, buff);
          point_double_generic(q, q, buff);
          uint64_t mask0 = (uint64_t)0U - bit;
          uint32_t len1 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len1; i++)
          {
            uint64_t dummy = mask0 & (q[i] ^ result[i]);
            q[i] = q[i] ^ dummy;
            result[i] = result[i] ^ dummy;
          }
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
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
  memcpy(result, q, sw * (uint32_t)3U * sizeof (uint64_t));
}

static void
secretToPublicWithoutNorm(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
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
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
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
  uint64_t *x = result;
  uint64_t *y = result + len10;
  uint64_t *z = result + (uint32_t)2U * len10;
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
    x[i] = (uint64_t)0U;
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
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    y[i] = (uint64_t)0U;
  }
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
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    z[i] = (uint64_t)0U;
  }
  switch (c)
  {
    case Spec_ECC_Curves_P384:
      {
        q[0U] = (uint64_t)0x3dd0756649c0b528U;
        q[1U] = (uint64_t)0x20e378e2a0d6ce38U;
        q[2U] = (uint64_t)0x879c3afc541b4d6eU;
        q[3U] = (uint64_t)0x6454868459a30effU;
        q[4U] = (uint64_t)0x812ff723614ede2bU;
        q[5U] = (uint64_t)0x4d3aadc2299e1513U;
        q[6U] = (uint64_t)0x23043dad4b03a4feU;
        q[7U] = (uint64_t)0xa1bfa8bf7bb4a9acU;
        q[8U] = (uint64_t)0x8bade7562e83b050U;
        q[9U] = (uint64_t)0xc6c3521968f4ffd9U;
        q[10U] = (uint64_t)0xdd8002263969a840U;
        q[11U] = (uint64_t)0x2b78abc25a15c5e9U;
        q[12U] = (uint64_t)0xffffffff00000001U;
        q[13U] = (uint64_t)0xffffffffU;
        q[14U] = (uint64_t)0x1U;
        q[15U] = (uint64_t)0U;
        q[16U] = (uint64_t)0U;
        q[17U] = (uint64_t)0U;
        break;
      }
    case Spec_ECC_Curves_P256:
      {
        q[0U] = (uint64_t)0x79e730d418a9143cU;
        q[1U] = (uint64_t)0x75ba95fc5fedb601U;
        q[2U] = (uint64_t)0x79fb732b77622510U;
        q[3U] = (uint64_t)0x18905f76a53755c6U;
        q[4U] = (uint64_t)0xddf25357ce95560aU;
        q[5U] = (uint64_t)0x8b4ab8e4ba19e45cU;
        q[6U] = (uint64_t)0xd2e88688dd21f325U;
        q[7U] = (uint64_t)0x8571ff1825885d85U;
        q[8U] = (uint64_t)0x1U;
        q[9U] = (uint64_t)0xffffffff00000000U;
        q[10U] = (uint64_t)0xffffffffffffffffU;
        q[11U] = (uint64_t)0xfffffffeU;
        break;
      }
    default:
      {
        
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
        for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
        {
          uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256) - (uint32_t)1U - i0;
          uint64_t
          bit =
            (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
            * (uint32_t)8U
            - (uint32_t)1U
            - bit0 / (uint32_t)8U]
            >> bit0 % (uint32_t)8U
            & (uint8_t)1U);
          uint64_t mask = (uint64_t)0U - bit;
          uint32_t len11 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len11; i++)
          {
            uint64_t dummy = mask & (result[i] ^ q[i]);
            result[i] = result[i] ^ dummy;
            q[i] = q[i] ^ dummy;
          }
          point_add_p256(result, q, q, buff);
          point_double_p256(result, result, buff);
          uint64_t mask0 = (uint64_t)0U - bit;
          uint32_t len1 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len1; i++)
          {
            uint64_t dummy = mask0 & (result[i] ^ q[i]);
            result[i] = result[i] ^ dummy;
            q[i] = q[i] ^ dummy;
          }
        }
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
        for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
        {
          uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384) - (uint32_t)1U - i0;
          uint64_t
          bit =
            (uint64_t)(((uint8_t *)scalar)[(uint32_t)6U
            * (uint32_t)8U
            - (uint32_t)1U
            - bit0 / (uint32_t)8U]
            >> bit0 % (uint32_t)8U
            & (uint8_t)1U);
          uint64_t mask = (uint64_t)0U - bit;
          uint32_t len11 = (uint32_t)18U;
          for (uint32_t i = (uint32_t)0U; i < len11; i++)
          {
            uint64_t dummy = mask & (result[i] ^ q[i]);
            result[i] = result[i] ^ dummy;
            q[i] = q[i] ^ dummy;
          }
          point_add_p384(result, q, q, buff);
          point_double_p384(result, result, buff);
          uint64_t mask0 = (uint64_t)0U - bit;
          uint32_t len1 = (uint32_t)18U;
          for (uint32_t i = (uint32_t)0U; i < len1; i++)
          {
            uint64_t dummy = mask0 & (result[i] ^ q[i]);
            result[i] = result[i] ^ dummy;
            q[i] = q[i] ^ dummy;
          }
        }
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default);
        for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
        {
          uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default) - (uint32_t)1U - i0;
          uint64_t
          bit =
            (uint64_t)(((uint8_t *)scalar)[(uint32_t)4U
            * (uint32_t)8U
            - (uint32_t)1U
            - bit0 / (uint32_t)8U]
            >> bit0 % (uint32_t)8U
            & (uint8_t)1U);
          uint64_t mask = (uint64_t)0U - bit;
          uint32_t len11 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len11; i++)
          {
            uint64_t dummy = mask & (result[i] ^ q[i]);
            result[i] = result[i] ^ dummy;
            q[i] = q[i] ^ dummy;
          }
          point_add_generic(result, q, q, buff);
          point_double_generic(result, result, buff);
          uint64_t mask0 = (uint64_t)0U - bit;
          uint32_t len1 = (uint32_t)12U;
          for (uint32_t i = (uint32_t)0U; i < len1; i++)
          {
            uint64_t dummy = mask0 & (result[i] ^ q[i]);
            result[i] = result[i] ^ dummy;
            q[i] = q[i] ^ dummy;
          }
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline bool
verifyQValidCurvePoint(Spec_ECC_Curves_curve c, uint64_t *pubKey, uint64_t *tempBuffer)
{
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
  KRML_CHECK_SIZE(sizeof (uint64_t), len0);
  uint64_t tempBuffer1[len0];
  memset(tempBuffer1, 0U, len0 * sizeof (uint64_t));
  uint64_t *x0 = pubKey;
  uint64_t *y0 = pubKey + len0;
  uint64_t carryX;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint64_t
        p[4U] =
          {
            (uint64_t)0xffffffffffffffffU,
            (uint64_t)0xffffffffU,
            (uint64_t)0U,
            (uint64_t)0xffffffff00000001U
          };
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x0[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer1 + (uint32_t)4U * i);
          uint64_t t10 = x0[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x0[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x0[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = x0[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer1 + i);
        }
        uint64_t r = c1;
        carryX = r;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t
        p[6U] =
          {
            (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
            (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
            (uint64_t)0xffffffffffffffffU
          };
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x0[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer1 + (uint32_t)4U * i);
          uint64_t t10 = x0[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x0[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x0[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = x0[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer1 + i);
        }
        uint64_t r = c1;
        carryX = r;
        break;
      }
    default:
      {
        carryX = (uint64_t)0U;
      }
  }
  uint64_t carryY;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint64_t
        p[4U] =
          {
            (uint64_t)0xffffffffffffffffU,
            (uint64_t)0xffffffffU,
            (uint64_t)0U,
            (uint64_t)0xffffffff00000001U
          };
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = y0[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer1 + (uint32_t)4U * i);
          uint64_t t10 = y0[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = y0[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = y0[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = y0[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer1 + i);
        }
        uint64_t r = c1;
        carryY = r;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t
        p[6U] =
          {
            (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
            (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU,
            (uint64_t)0xffffffffffffffffU
          };
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = y0[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer1 + (uint32_t)4U * i);
          uint64_t t10 = y0[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = y0[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = y0[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = y0[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer1 + i);
        }
        uint64_t r = c1;
        carryY = r;
        break;
      }
    default:
      {
        carryY = (uint64_t)0U;
      }
  }
  bool lessX = carryX == (uint64_t)1U;
  bool lessY = carryY == (uint64_t)1U;
  bool coordinatesValid = lessX && lessY;
  if (!coordinatesValid)
  {
    return false;
  }
  uint32_t sz;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sz = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sz = (uint32_t)6U;
        break;
      }
    default:
      {
        sz = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t y2Buffer[sz];
  memset(y2Buffer, 0U, sz * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz);
  uint64_t xBuffer[sz];
  memset(xBuffer, 0U, sz * sizeof (uint64_t));
  uint64_t *x1 = pubKey;
  uint64_t *y1 = pubKey + sz;
  uint32_t len6;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len6 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len6 = (uint32_t)6U;
        break;
      }
    default:
      {
        len6 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len6);
  uint64_t multBuffer[(uint32_t)2U * len6];
  memset(multBuffer, 0U, (uint32_t)2U * len6 * sizeof (uint64_t));
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
  uint64_t *oToZero0 = multBuffer;
  uint64_t *oToCopy0 = multBuffer + len10;
  memcpy(oToCopy0, y1, len10 * sizeof (uint64_t));
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
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    oToZero0[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer, y2Buffer);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_square_buffer_dh_p256(y2Buffer, y2Buffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_square_buffer_dh_p384(y2Buffer, y2Buffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_square_buffer_dh_generic(y2Buffer, y2Buffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t sz1;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sz1 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sz1 = (uint32_t)6U;
        break;
      }
    default:
      {
        sz1 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t xToDomainBuffer[sz1];
  memset(xToDomainBuffer, 0U, sz1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t minusThreeXBuffer[sz1];
  memset(minusThreeXBuffer, 0U, sz1 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), sz1);
  uint64_t b_constant[sz1];
  memset(b_constant, 0U, sz1 * sizeof (uint64_t));
  uint32_t len7;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len7 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len7 = (uint32_t)6U;
        break;
      }
    default:
      {
        len7 = (uint32_t)4U;
      }
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len7);
  uint64_t multBuffer0[(uint32_t)2U * len7];
  memset(multBuffer0, 0U, (uint32_t)2U * len7 * sizeof (uint64_t));
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
  uint64_t *oToZero1 = multBuffer0;
  uint64_t *oToCopy1 = multBuffer0 + len11;
  memcpy(oToCopy1, x1, len11 * sizeof (uint64_t));
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
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    oToZero1[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer0, xToDomainBuffer);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_square_buffer_dh_p256(xToDomainBuffer, xBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_square_buffer_dh_p384(xToDomainBuffer, xBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_square_buffer_dh_generic(xToDomainBuffer, xBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        montgomery_multiplication_buffer_dh_p256(xBuffer, xToDomainBuffer, xBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        montgomery_multiplication_buffer_dh_p384(xBuffer, xToDomainBuffer, xBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        montgomery_multiplication_buffer_dh_generic(xBuffer, xToDomainBuffer, xBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_add_p256(xToDomainBuffer, xToDomainBuffer, minusThreeXBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_add_p384(xToDomainBuffer, xToDomainBuffer, minusThreeXBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        felem_add_generic(xToDomainBuffer, xToDomainBuffer, minusThreeXBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_add_p256(xToDomainBuffer, minusThreeXBuffer, minusThreeXBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_add_p384(xToDomainBuffer, minusThreeXBuffer, minusThreeXBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        felem_add_generic(xToDomainBuffer, minusThreeXBuffer, minusThreeXBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_sub_p256(xBuffer, minusThreeXBuffer, xBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_sub_p384(xBuffer, minusThreeXBuffer, xBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        felem_sub_generic(xBuffer, minusThreeXBuffer, xBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        b_constant[0U] = (uint64_t)15608596021259845087U;
        b_constant[1U] = (uint64_t)12461466548982526096U;
        b_constant[2U] = (uint64_t)16546823903870267094U;
        b_constant[3U] = (uint64_t)15866188208926050356U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        b_constant[0U] = (uint64_t)581395848458481100U;
        b_constant[1U] = (uint64_t)17809957346689692396U;
        b_constant[2U] = (uint64_t)8643006485390950958U;
        b_constant[3U] = (uint64_t)16372638458395724514U;
        b_constant[4U] = (uint64_t)13126622871277412500U;
        b_constant[5U] = (uint64_t)14774077593024970745U;
        break;
      }
    default:
      {
        
      }
  }
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        felem_add_p256(xBuffer, b_constant, xBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        felem_add_p384(xBuffer, b_constant, xBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        felem_add_generic(xBuffer, b_constant, xBuffer);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t tmp1 = (uint64_t)0U;
  tmp1 = (uint64_t)18446744073709551615U;
  uint32_t len8;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len8 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len8 = (uint32_t)6U;
        break;
      }
    default:
      {
        len8 = (uint32_t)4U;
      }
  }
  for (uint32_t i = (uint32_t)0U; i < len8; i++)
  {
    uint64_t a_i = y2Buffer[i];
    uint64_t b_i = xBuffer[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t r = tmp1;
  bool belongsToCurve = !(r == (uint64_t)0U);
  bool orderCorrect;
  if (!Spec_ECC_Curves_isPrimeGroup(c))
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
    uint64_t multResult[(uint32_t)3U * len];
    memset(multResult, 0U, (uint32_t)3U * len * sizeof (uint64_t));
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len1);
    uint64_t pBuffer[(uint32_t)3U * len1];
    memset(pBuffer, 0U, (uint32_t)3U * len1 * sizeof (uint64_t));
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
    memcpy(pBuffer, pubKey, sw * (uint32_t)3U * sizeof (uint64_t));
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
    uint64_t *q = tempBuffer;
    uint64_t *buff = tempBuffer + (uint32_t)3U * len22;
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
    uint64_t *x = q;
    uint64_t *y = q + len30;
    uint64_t *z = q + (uint32_t)2U * len30;
    uint32_t len40;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len40 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len40 = (uint32_t)6U;
          break;
        }
      default:
        {
          len40 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len40; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len41;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len41 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len41 = (uint32_t)6U;
          break;
        }
      default:
        {
          len41 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len41; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len42;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len42 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len42 = (uint32_t)6U;
          break;
        }
      default:
        {
          len42 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len42; i++)
    {
      z[i] = (uint64_t)0U;
    }
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
    uint64_t *p_x = pBuffer;
    uint64_t *p_y = pBuffer + len31;
    uint64_t *p_z = pBuffer + (uint32_t)2U * len31;
    uint64_t *r_x = multResult;
    uint64_t *r_y = multResult + len31;
    uint64_t *r_z = multResult + (uint32_t)2U * len31;
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len4);
    uint64_t multBuffer1[(uint32_t)2U * len4];
    memset(multBuffer1, 0U, (uint32_t)2U * len4 * sizeof (uint64_t));
    uint32_t len50;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len50 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len50 = (uint32_t)6U;
          break;
        }
      default:
        {
          len50 = (uint32_t)4U;
        }
    }
    uint64_t *oToZero2 = multBuffer1;
    uint64_t *oToCopy2 = multBuffer1 + len50;
    memcpy(oToCopy2, p_x, len50 * sizeof (uint64_t));
    uint32_t len60;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len60 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len60 = (uint32_t)6U;
          break;
        }
      default:
        {
          len60 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len60; i++)
    {
      oToZero2[i] = (uint64_t)0U;
    }
    reduction(c, multBuffer1, r_x);
    uint32_t len43;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len43 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len43 = (uint32_t)6U;
          break;
        }
      default:
        {
          len43 = (uint32_t)4U;
        }
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len43);
    uint64_t multBuffer2[(uint32_t)2U * len43];
    memset(multBuffer2, 0U, (uint32_t)2U * len43 * sizeof (uint64_t));
    uint32_t len51;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len51 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len51 = (uint32_t)6U;
          break;
        }
      default:
        {
          len51 = (uint32_t)4U;
        }
    }
    uint64_t *oToZero3 = multBuffer2;
    uint64_t *oToCopy3 = multBuffer2 + len51;
    memcpy(oToCopy3, p_y, len51 * sizeof (uint64_t));
    uint32_t len61;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len61 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len61 = (uint32_t)6U;
          break;
        }
      default:
        {
          len61 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len61; i++)
    {
      oToZero3[i] = (uint64_t)0U;
    }
    reduction(c, multBuffer2, r_y);
    uint32_t len44;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len44 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len44 = (uint32_t)6U;
          break;
        }
      default:
        {
          len44 = (uint32_t)4U;
        }
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len44);
    uint64_t multBuffer3[(uint32_t)2U * len44];
    memset(multBuffer3, 0U, (uint32_t)2U * len44 * sizeof (uint64_t));
    uint32_t len5;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len5 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len5 = (uint32_t)6U;
          break;
        }
      default:
        {
          len5 = (uint32_t)4U;
        }
    }
    uint64_t *oToZero = multBuffer3;
    uint64_t *oToCopy = multBuffer3 + len5;
    memcpy(oToCopy, p_z, len5 * sizeof (uint64_t));
    uint32_t len62;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          len62 = (uint32_t)4U;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          len62 = (uint32_t)6U;
          break;
        }
      default:
        {
          len62 = (uint32_t)4U;
        }
    }
    for (uint32_t i = (uint32_t)0U; i < len62; i++)
    {
      oToZero[i] = (uint64_t)0U;
    }
    reduction(c, multBuffer3, r_z);
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
          for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
          {
            uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256) - (uint32_t)1U - i0;
            uint64_t
            bit =
              (uint64_t)(prime256_order_[(uint32_t)4U
              * (uint32_t)8U
              - (uint32_t)1U
              - bit0 / (uint32_t)8U]
              >> bit0 % (uint32_t)8U
              & (uint8_t)1U);
            uint64_t mask = (uint64_t)0U - bit;
            uint32_t len32 = (uint32_t)12U;
            for (uint32_t i = (uint32_t)0U; i < len32; i++)
            {
              uint64_t dummy = mask & (q[i] ^ multResult[i]);
              q[i] = q[i] ^ dummy;
              multResult[i] = multResult[i] ^ dummy;
            }
            point_add_p256(q, multResult, multResult, buff);
            point_double_p256(q, q, buff);
            uint64_t mask0 = (uint64_t)0U - bit;
            uint32_t len3 = (uint32_t)12U;
            for (uint32_t i = (uint32_t)0U; i < len3; i++)
            {
              uint64_t dummy = mask0 & (q[i] ^ multResult[i]);
              q[i] = q[i] ^ dummy;
              multResult[i] = multResult[i] ^ dummy;
            }
          }
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
          for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
          {
            uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384) - (uint32_t)1U - i0;
            uint64_t
            bit =
              (uint64_t)(prime256_order_[(uint32_t)6U
              * (uint32_t)8U
              - (uint32_t)1U
              - bit0 / (uint32_t)8U]
              >> bit0 % (uint32_t)8U
              & (uint8_t)1U);
            uint64_t mask = (uint64_t)0U - bit;
            uint32_t len32 = (uint32_t)18U;
            for (uint32_t i = (uint32_t)0U; i < len32; i++)
            {
              uint64_t dummy = mask & (q[i] ^ multResult[i]);
              q[i] = q[i] ^ dummy;
              multResult[i] = multResult[i] ^ dummy;
            }
            point_add_p384(q, multResult, multResult, buff);
            point_double_p384(q, q, buff);
            uint64_t mask0 = (uint64_t)0U - bit;
            uint32_t len3 = (uint32_t)18U;
            for (uint32_t i = (uint32_t)0U; i < len3; i++)
            {
              uint64_t dummy = mask0 & (q[i] ^ multResult[i]);
              q[i] = q[i] ^ dummy;
              multResult[i] = multResult[i] ^ dummy;
            }
          }
          break;
        }
      case Spec_ECC_Curves_Default:
        {
          uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default);
          for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
          {
            uint32_t
            bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_Default) - (uint32_t)1U - i0;
            uint64_t
            bit =
              (uint64_t)(prime256_order_[(uint32_t)4U
              * (uint32_t)8U
              - (uint32_t)1U
              - bit0 / (uint32_t)8U]
              >> bit0 % (uint32_t)8U
              & (uint8_t)1U);
            uint64_t mask = (uint64_t)0U - bit;
            uint32_t len32 = (uint32_t)12U;
            for (uint32_t i = (uint32_t)0U; i < len32; i++)
            {
              uint64_t dummy = mask & (q[i] ^ multResult[i]);
              q[i] = q[i] ^ dummy;
              multResult[i] = multResult[i] ^ dummy;
            }
            point_add_generic(q, multResult, multResult, buff);
            point_double_generic(q, q, buff);
            uint64_t mask0 = (uint64_t)0U - bit;
            uint32_t len3 = (uint32_t)12U;
            for (uint32_t i = (uint32_t)0U; i < len3; i++)
            {
              uint64_t dummy = mask0 & (q[i] ^ multResult[i]);
              q[i] = q[i] ^ dummy;
              multResult[i] = multResult[i] ^ dummy;
            }
          }
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    norm(c, q, multResult, buff);
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
    uint64_t *zCoordinate = multResult + (uint32_t)2U * len12;
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
      uint64_t a_i = zCoordinate[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp;
      tmp = r_i & tmp0;
    }
    uint64_t f = tmp;
    bool result = f == (uint64_t)0xffffffffffffffffU;
    bool orderCorrect0 = result;
    orderCorrect = orderCorrect0;
  }
  else
  {
    orderCorrect = true;
  }
  return coordinatesValid && belongsToCurve && orderCorrect;
}

static uint32_t
k224_256[64U] =
  {
    (uint32_t)0x428a2f98U, (uint32_t)0x71374491U, (uint32_t)0xb5c0fbcfU, (uint32_t)0xe9b5dba5U,
    (uint32_t)0x3956c25bU, (uint32_t)0x59f111f1U, (uint32_t)0x923f82a4U, (uint32_t)0xab1c5ed5U,
    (uint32_t)0xd807aa98U, (uint32_t)0x12835b01U, (uint32_t)0x243185beU, (uint32_t)0x550c7dc3U,
    (uint32_t)0x72be5d74U, (uint32_t)0x80deb1feU, (uint32_t)0x9bdc06a7U, (uint32_t)0xc19bf174U,
    (uint32_t)0xe49b69c1U, (uint32_t)0xefbe4786U, (uint32_t)0x0fc19dc6U, (uint32_t)0x240ca1ccU,
    (uint32_t)0x2de92c6fU, (uint32_t)0x4a7484aaU, (uint32_t)0x5cb0a9dcU, (uint32_t)0x76f988daU,
    (uint32_t)0x983e5152U, (uint32_t)0xa831c66dU, (uint32_t)0xb00327c8U, (uint32_t)0xbf597fc7U,
    (uint32_t)0xc6e00bf3U, (uint32_t)0xd5a79147U, (uint32_t)0x06ca6351U, (uint32_t)0x14292967U,
    (uint32_t)0x27b70a85U, (uint32_t)0x2e1b2138U, (uint32_t)0x4d2c6dfcU, (uint32_t)0x53380d13U,
    (uint32_t)0x650a7354U, (uint32_t)0x766a0abbU, (uint32_t)0x81c2c92eU, (uint32_t)0x92722c85U,
    (uint32_t)0xa2bfe8a1U, (uint32_t)0xa81a664bU, (uint32_t)0xc24b8b70U, (uint32_t)0xc76c51a3U,
    (uint32_t)0xd192e819U, (uint32_t)0xd6990624U, (uint32_t)0xf40e3585U, (uint32_t)0x106aa070U,
    (uint32_t)0x19a4c116U, (uint32_t)0x1e376c08U, (uint32_t)0x2748774cU, (uint32_t)0x34b0bcb5U,
    (uint32_t)0x391c0cb3U, (uint32_t)0x4ed8aa4aU, (uint32_t)0x5b9cca4fU, (uint32_t)0x682e6ff3U,
    (uint32_t)0x748f82eeU, (uint32_t)0x78a5636fU, (uint32_t)0x84c87814U, (uint32_t)0x8cc70208U,
    (uint32_t)0x90befffaU, (uint32_t)0xa4506cebU, (uint32_t)0xbef9a3f7U, (uint32_t)0xc67178f2U
  };

static void update_256(uint32_t *hash, uint8_t *block)
{
  uint32_t hash1[8U] = { 0U };
  uint32_t computed_ws[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    if (i < (uint32_t)16U)
    {
      uint8_t *b = block + i * (uint32_t)4U;
      uint32_t u = load32_be(b);
      computed_ws[i] = u;
    }
    else
    {
      uint32_t t16 = computed_ws[i - (uint32_t)16U];
      uint32_t t15 = computed_ws[i - (uint32_t)15U];
      uint32_t t7 = computed_ws[i - (uint32_t)7U];
      uint32_t t2 = computed_ws[i - (uint32_t)2U];
      uint32_t
      s1 =
        (t2 >> (uint32_t)17U | t2 << (uint32_t)15U)
        ^ ((t2 >> (uint32_t)19U | t2 << (uint32_t)13U) ^ t2 >> (uint32_t)10U);
      uint32_t
      s0 =
        (t15 >> (uint32_t)7U | t15 << (uint32_t)25U)
        ^ ((t15 >> (uint32_t)18U | t15 << (uint32_t)14U) ^ t15 >> (uint32_t)3U);
      uint32_t w = s1 + t7 + s0 + t16;
      computed_ws[i] = w;
    }
  }
  memcpy(hash1, hash, (uint32_t)8U * sizeof (uint32_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint32_t a0 = hash1[0U];
    uint32_t b0 = hash1[1U];
    uint32_t c0 = hash1[2U];
    uint32_t d0 = hash1[3U];
    uint32_t e0 = hash1[4U];
    uint32_t f0 = hash1[5U];
    uint32_t g0 = hash1[6U];
    uint32_t h02 = hash1[7U];
    uint32_t w = computed_ws[i];
    uint32_t
    t1 =
      h02
      +
        ((e0 >> (uint32_t)6U | e0 << (uint32_t)26U)
        ^ ((e0 >> (uint32_t)11U | e0 << (uint32_t)21U) ^ (e0 >> (uint32_t)25U | e0 << (uint32_t)7U)))
      + ((e0 & f0) ^ (~e0 & g0))
      + k224_256[i]
      + w;
    uint32_t
    t2 =
      ((a0 >> (uint32_t)2U | a0 << (uint32_t)30U)
      ^ ((a0 >> (uint32_t)13U | a0 << (uint32_t)19U) ^ (a0 >> (uint32_t)22U | a0 << (uint32_t)10U)))
      + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
    hash1[0U] = t1 + t2;
    hash1[1U] = a0;
    hash1[2U] = b0;
    hash1[3U] = c0;
    hash1[4U] = d0 + t1;
    hash1[5U] = e0;
    hash1[6U] = f0;
    hash1[7U] = g0;
  }
  {
    uint32_t xi = hash[0U];
    uint32_t yi = hash1[0U];
    hash[0U] = xi + yi;
  }
  {
    uint32_t xi = hash[1U];
    uint32_t yi = hash1[1U];
    hash[1U] = xi + yi;
  }
  {
    uint32_t xi = hash[2U];
    uint32_t yi = hash1[2U];
    hash[2U] = xi + yi;
  }
  {
    uint32_t xi = hash[3U];
    uint32_t yi = hash1[3U];
    hash[3U] = xi + yi;
  }
  {
    uint32_t xi = hash[4U];
    uint32_t yi = hash1[4U];
    hash[4U] = xi + yi;
  }
  {
    uint32_t xi = hash[5U];
    uint32_t yi = hash1[5U];
    hash[5U] = xi + yi;
  }
  {
    uint32_t xi = hash[6U];
    uint32_t yi = hash1[6U];
    hash[6U] = xi + yi;
  }
  {
    uint32_t xi = hash[7U];
    uint32_t yi = hash1[7U];
    hash[7U] = xi + yi;
  }
}

static void pad_256(uint64_t len, uint8_t *dst)
{
  uint8_t *dst1 = dst;
  dst1[0U] = (uint8_t)0x80U;
  uint8_t *dst2 = dst + (uint32_t)1U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U))) % (uint32_t)64U;
    i++)
  {
    dst2[i] = (uint8_t)0U;
  }
  uint8_t
  *dst3 =
    dst
    +
      (uint32_t)1U
      +
        ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(len % (uint64_t)(uint32_t)64U)))
        % (uint32_t)64U;
  store64_be(dst3, len << (uint32_t)3U);
}

static void finish_256(uint32_t *s, uint8_t *dst)
{
  uint32_t *uu____0 = s;
  {
    store32_be(dst + (uint32_t)0U * (uint32_t)4U, uu____0[0U]);
  }
  {
    store32_be(dst + (uint32_t)1U * (uint32_t)4U, uu____0[1U]);
  }
  {
    store32_be(dst + (uint32_t)2U * (uint32_t)4U, uu____0[2U]);
  }
  {
    store32_be(dst + (uint32_t)3U * (uint32_t)4U, uu____0[3U]);
  }
  {
    store32_be(dst + (uint32_t)4U * (uint32_t)4U, uu____0[4U]);
  }
  {
    store32_be(dst + (uint32_t)5U * (uint32_t)4U, uu____0[5U]);
  }
  {
    store32_be(dst + (uint32_t)6U * (uint32_t)4U, uu____0[6U]);
  }
  {
    store32_be(dst + (uint32_t)7U * (uint32_t)4U, uu____0[7U]);
  }
}

static void update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n_blocks)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    update_256(s, block);
  }
}

static void update_last_256(uint32_t *s, uint64_t prev_len, uint8_t *input, uint32_t input_len)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi_256(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  pad_256(total_input_len, tmp_pad);
  update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
}

static void hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  update_multi_256(s, blocks, blocks_n);
  update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  finish_256(s, dst);
}

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
uint64_t
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
  uint32_t len10 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len10; i++)
  {
    uint64_t *os = privKeyAsFelem;
    uint8_t *bj = privKey + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len20 = (uint32_t)4U;
  uint32_t lenByTwo = len20 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = privKeyAsFelem[i];
    uint64_t right = privKeyAsFelem[lenRight];
    privKeyAsFelem[i] = right;
    privKeyAsFelem[lenRight] = left;
  }
  uint32_t len11 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t hashAsFelem[len11];
  memset(hashAsFelem, 0U, len11 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len11);
  uint64_t tempBuffer[(uint32_t)20U * len11];
  memset(tempBuffer, 0U, (uint32_t)20U * len11 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t kAsFelem[len11];
  memset(kAsFelem, 0U, len11 * sizeof (uint64_t));
  uint32_t len21 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    uint64_t *os = kAsFelem;
    uint8_t *bj = k + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len30 = (uint32_t)4U;
  uint32_t lenByTwo0 = len30 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = kAsFelem[i];
    uint64_t right = kAsFelem[lenRight];
    kAsFelem[i] = right;
    kAsFelem[lenRight] = left;
  }
  uint32_t sz_hash = (uint32_t)32U;
  uint32_t len22 = sz_hash + (uint32_t)32U;
  KRML_CHECK_SIZE(sizeof (uint8_t), len22);
  uint8_t mHash[len22];
  memset(mHash, 0U, len22 * sizeof (uint8_t));
  uint8_t *mHashHPart = mHash;
  uint8_t *mHashRPart = mHash;
  hash_256(m, mLen, mHashHPart);
  uint32_t len31 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len31; i++)
  {
    uint64_t *os = hashAsFelem;
    uint8_t *bj = mHashRPart + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len40 = (uint32_t)4U;
  uint32_t lenByTwo1 = len40 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo1; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = hashAsFelem[i];
    uint64_t right = hashAsFelem[lenRight];
    hashAsFelem[i] = right;
    hashAsFelem[lenRight] = left;
  }
  uint32_t len32 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len32);
  uint64_t tempBuffer1[len32];
  memset(tempBuffer1, 0U, len32 * sizeof (uint64_t));
  uint64_t
  p0[4U] =
    {
      (uint64_t)17562291160714782033U,
      (uint64_t)13611842547513532036U,
      (uint64_t)18446744073709551615U,
      (uint64_t)18446744069414584320U
    };
  uint32_t len41 = (uint32_t)4U;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k10 = len41 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k10 / (uint32_t)4U; i++)
  {
    uint64_t t1 = hashAsFelem[(uint32_t)4U * i];
    uint64_t t20 = p0[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, tempBuffer1 + (uint32_t)4U * i);
    uint64_t t10 = hashAsFelem[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t10,
        t21,
        tempBuffer1 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = hashAsFelem[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t11,
        t22,
        tempBuffer1 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = hashAsFelem[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t12,
        t2,
        tempBuffer1 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k10; i < len41; i++)
  {
    uint64_t t1 = hashAsFelem[i];
    uint64_t t2 = p0[i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, tempBuffer1 + i);
  }
  uint64_t r1 = c0;
  uint64_t r10 = r1;
  uint64_t mask = ~FStar_UInt64_eq_mask(r10, (uint64_t)0U);
  uint32_t len42 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len42; i++)
  {
    uint64_t x_i = tempBuffer1[i];
    uint64_t y_i = hashAsFelem[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    hashAsFelem[i] = r_i;
  }
  uint32_t len23 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len23);
  uint64_t result1[(uint32_t)3U * len23];
  memset(result1, 0U, (uint32_t)3U * len23 * sizeof (uint64_t));
  uint64_t *tempForNorm = tempBuffer;
  secretToPublicWithoutNorm(Spec_ECC_Curves_P256, result1, (void *)k, tempBuffer);
  uint64_t *xf = result1;
  uint64_t *zf = result1 + (uint32_t)8U;
  uint64_t *z2f = tempForNorm + (uint32_t)4U;
  uint64_t *t8 = tempForNorm + (uint32_t)3U * (uint32_t)4U;
  montgomery_square_buffer_dh_p256(zf, z2f);
  exponent_p256(z2f, z2f, t8);
  montgomery_multiplication_buffer_dh_p256(z2f, xf, z2f);
  montgomery_multiplication_buffer_by_one_dh_p256(z2f, r);
  uint32_t len33 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len33);
  uint64_t tempBuffer10[len33];
  memset(tempBuffer10, 0U, len33 * sizeof (uint64_t));
  uint64_t
  p1[4U] =
    {
      (uint64_t)17562291160714782033U,
      (uint64_t)13611842547513532036U,
      (uint64_t)18446744073709551615U,
      (uint64_t)18446744069414584320U
    };
  uint32_t len43 = (uint32_t)4U;
  uint64_t c1 = (uint64_t)0U;
  uint32_t k11 = len43 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k11 / (uint32_t)4U; i++)
  {
    uint64_t t1 = r[(uint32_t)4U * i];
    uint64_t t20 = p1[(uint32_t)4U * i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer10 + (uint32_t)4U * i);
    uint64_t t10 = r[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t10,
        t21,
        tempBuffer10 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = r[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t11,
        t22,
        tempBuffer10 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = r[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t12,
        t2,
        tempBuffer10 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k11; i < len43; i++)
  {
    uint64_t t1 = r[i];
    uint64_t t2 = p1[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer10 + i);
  }
  uint64_t r11 = c1;
  uint64_t r12 = r11;
  uint64_t mask0 = ~FStar_UInt64_eq_mask(r12, (uint64_t)0U);
  uint32_t len44 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len44; i++)
  {
    uint64_t x_i = tempBuffer10[i];
    uint64_t y_i = r[i];
    uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
    r[i] = r_i;
  }
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len34 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len34; i++)
  {
    uint64_t a_i = r[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t step5Flag = tmp;
  uint32_t len24 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len24);
  uint64_t rda[len24];
  memset(rda, 0U, len24 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len24);
  uint64_t zBuffer[len24];
  memset(zBuffer, 0U, len24 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len24);
  uint64_t kInv[len24];
  memset(kInv, 0U, len24 * sizeof (uint64_t));
  montgomery_multiplication_buffer_dh_p256(r, privKeyAsFelem, rda);
  uint32_t len35 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len35);
  uint64_t one[len35];
  memset(one, 0U, len35 * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint32_t len45 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len45; i++)
  {
    one[i] = (uint64_t)0U;
  }
  montgomery_multiplication_buffer_dh_p256(one, hashAsFelem, zBuffer);
  uint32_t len36 = (uint32_t)4U;
  uint64_t c2 = (uint64_t)0U;
  uint32_t k12 = len36 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k12 / (uint32_t)4U; i++)
  {
    uint64_t t1 = rda[(uint32_t)4U * i];
    uint64_t t20 = zBuffer[(uint32_t)4U * i];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t20, zBuffer + (uint32_t)4U * i);
    uint64_t t10 = rda[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = zBuffer[(uint32_t)4U * i + (uint32_t)1U];
    c2 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c2,
        t10,
        t21,
        zBuffer + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = rda[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = zBuffer[(uint32_t)4U * i + (uint32_t)2U];
    c2 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c2,
        t11,
        t22,
        zBuffer + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = rda[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = zBuffer[(uint32_t)4U * i + (uint32_t)3U];
    c2 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c2,
        t12,
        t2,
        zBuffer + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k12; i < len36; i++)
  {
    uint64_t t1 = rda[i];
    uint64_t t2 = zBuffer[i];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, zBuffer + i);
  }
  uint64_t t = c2;
  uint32_t len3 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len3);
  uint64_t tempBuffer11[len3];
  memset(tempBuffer11, 0U, len3 * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  uint64_t
  p[4U] =
    {
      (uint64_t)17562291160714782033U,
      (uint64_t)13611842547513532036U,
      (uint64_t)18446744073709551615U,
      (uint64_t)18446744069414584320U
    };
  uint32_t len46 = (uint32_t)4U;
  uint64_t c = (uint64_t)0U;
  uint32_t k1 = len46 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = zBuffer[(uint32_t)4U * i];
    uint64_t t20 = p[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer11 + (uint32_t)4U * i);
    uint64_t t10 = zBuffer[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t10,
        t21,
        tempBuffer11 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = zBuffer[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t11,
        t22,
        tempBuffer11 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = zBuffer[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
    c =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
        t12,
        t2,
        tempBuffer11 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k1; i < len46; i++)
  {
    uint64_t t1 = zBuffer[i];
    uint64_t t2 = p[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer11 + i);
  }
  uint64_t r13 = c;
  uint64_t carry0 = r13;
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      t,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  uint64_t mask1 = ~FStar_UInt64_eq_mask(carry, (uint64_t)0U);
  uint32_t len4 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    uint64_t x_i = tempBuffer11[i];
    uint64_t y_i = zBuffer[i];
    uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
    zBuffer[i] = r_i;
  }
  memcpy(kInv, kAsFelem, len24 * sizeof (uint64_t));
  montgomery_ladder_power_p256(kInv, Hacl_Spec_ECDSA_Definition_prime256order_buffer, kInv);
  montgomery_multiplication_buffer_dh_p256(zBuffer, kInv, s);
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
  uint32_t lenByTwo2 = len1 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo2; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = r[i];
    uint64_t right = r[lenRight];
    r[i] = right;
    r[lenRight] = left;
  }
  uint32_t len12 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len12; i++)
  {
    store64_be(resultR + i * (uint32_t)8U, r[i]);
  }
  uint32_t len13 = (uint32_t)4U;
  uint32_t lenByTwo3 = len13 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo3; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = s[i];
    uint64_t right = s[lenRight];
    s[i] = right;
    s[lenRight] = left;
  }
  uint32_t len14 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len14; i++)
  {
    store64_be(resultS + i * (uint32_t)8U, s[i]);
  }
  return (uint64_t)flag;
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
  uint32_t len20 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    uint64_t *os = publicKeyFelemX;
    uint8_t *bj = pubKeyX + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len30 = (uint32_t)4U;
  uint32_t lenByTwo = len30 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = publicKeyFelemX[i];
    uint64_t right = publicKeyFelemX[lenRight];
    publicKeyFelemX[i] = right;
    publicKeyFelemX[lenRight] = left;
  }
  uint32_t len21 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    uint64_t *os = publicKeyFelemY;
    uint8_t *bj = pubKeyY + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len31 = (uint32_t)4U;
  uint32_t lenByTwo0 = len31 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = publicKeyFelemY[i];
    uint64_t right = publicKeyFelemY[lenRight];
    publicKeyFelemY[i] = right;
    publicKeyFelemY[lenRight] = left;
  }
  uint32_t len22 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len22; i++)
  {
    uint64_t *os = rAsFelem;
    uint8_t *bj = r + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len32 = (uint32_t)4U;
  uint32_t lenByTwo1 = len32 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo1; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = rAsFelem[i];
    uint64_t right = rAsFelem[lenRight];
    rAsFelem[i] = right;
    rAsFelem[lenRight] = left;
  }
  uint32_t len23 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len23; i++)
  {
    uint64_t *os = sAsFelem;
    uint8_t *bj = s + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  uint32_t len33 = (uint32_t)4U;
  uint32_t lenByTwo2 = len33 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo2; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = sAsFelem[i];
    uint64_t right = sAsFelem[lenRight];
    sAsFelem[i] = right;
    sAsFelem[lenRight] = left;
  }
  uint32_t len11 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), len11 * (uint32_t)20U);
  uint64_t tempBuffer1[len11 * (uint32_t)20U];
  memset(tempBuffer1, 0U, len11 * (uint32_t)20U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t hashAsFelem[len11];
  memset(hashAsFelem, 0U, len11 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len11);
  uint64_t x[len11];
  memset(x, 0U, len11 * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len11 * (uint32_t)3U);
  uint64_t publicKeyBuffer[len11 * (uint32_t)3U];
  memset(publicKeyBuffer, 0U, len11 * (uint32_t)3U * sizeof (uint64_t));
  uint32_t len24 = (uint32_t)4U;
  uint32_t lengthXY = len24 * (uint32_t)2U;
  uint64_t *partPoint = publicKeyBuffer;
  uint64_t *zCoordinate = publicKeyBuffer + lengthXY;
  memcpy(partPoint, publicKeyAsFelem, lengthXY * sizeof (uint64_t));
  zCoordinate[0U] = (uint64_t)1U;
  uint32_t len34 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len34; i++)
  {
    zCoordinate[i] = (uint64_t)0U;
  }
  bool
  publicKeyCorrect = verifyQValidCurvePoint(Spec_ECC_Curves_P256, publicKeyBuffer, tempBuffer1);
  bool r1;
  if (publicKeyCorrect == false)
  {
    r1 = false;
  }
  else
  {
    uint32_t len25 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len25);
    uint64_t tempBuffer20[len25];
    memset(tempBuffer20, 0U, len25 * sizeof (uint64_t));
    uint64_t
    p0[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len35 = (uint32_t)4U;
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = len35 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = rAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p0[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, tempBuffer20 + (uint32_t)4U * i);
      uint64_t t10 = rAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p0[(uint32_t)4U * i + (uint32_t)1U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t10,
          t21,
          tempBuffer20 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = rAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p0[(uint32_t)4U * i + (uint32_t)2U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t11,
          t22,
          tempBuffer20 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = rAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p0[(uint32_t)4U * i + (uint32_t)3U];
      c0 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
          t12,
          t2,
          tempBuffer20 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < len35; i++)
    {
      uint64_t t1 = rAsFelem[i];
      uint64_t t2 = p0[i];
      c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, tempBuffer20 + i);
    }
    uint64_t r10 = c0;
    uint64_t carry = r10;
    bool less = carry == (uint64_t)1U;
    uint64_t tmp1 = (uint64_t)18446744073709551615U;
    uint32_t len36 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len36; i++)
    {
      uint64_t a_i = rAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp1;
      tmp1 = r_i & tmp0;
    }
    uint64_t f = tmp1;
    bool more = f == (uint64_t)0xffffffffffffffffU;
    bool isRCorrect = less && !more;
    uint32_t len26 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), len26);
    uint64_t tempBuffer21[len26];
    memset(tempBuffer21, 0U, len26 * sizeof (uint64_t));
    uint64_t
    p2[4U] =
      {
        (uint64_t)17562291160714782033U,
        (uint64_t)13611842547513532036U,
        (uint64_t)18446744073709551615U,
        (uint64_t)18446744069414584320U
      };
    uint32_t len37 = (uint32_t)4U;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k1 = len37 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = sAsFelem[(uint32_t)4U * i];
      uint64_t t20 = p2[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer21 + (uint32_t)4U * i);
      uint64_t t10 = sAsFelem[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = p2[(uint32_t)4U * i + (uint32_t)1U];
      c1 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
          t10,
          t21,
          tempBuffer21 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = sAsFelem[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = p2[(uint32_t)4U * i + (uint32_t)2U];
      c1 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
          t11,
          t22,
          tempBuffer21 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = sAsFelem[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = p2[(uint32_t)4U * i + (uint32_t)3U];
      c1 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
          t12,
          t2,
          tempBuffer21 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < len37; i++)
    {
      uint64_t t1 = sAsFelem[i];
      uint64_t t2 = p2[i];
      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer21 + i);
    }
    uint64_t r11 = c1;
    uint64_t carry0 = r11;
    bool less0 = carry0 == (uint64_t)1U;
    uint64_t tmp2 = (uint64_t)18446744073709551615U;
    uint32_t len3 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len3; i++)
    {
      uint64_t a_i = sAsFelem[i];
      uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
      uint64_t tmp0 = tmp2;
      tmp2 = r_i & tmp0;
    }
    uint64_t f2 = tmp2;
    bool more0 = f2 == (uint64_t)0xffffffffffffffffU;
    bool isSCorrect = less0 && !more0;
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      r1 = false;
    }
    else
    {
      uint32_t len27 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)2U * len27);
      uint8_t tempBufferU8[(uint32_t)2U * len27];
      memset(tempBufferU8, 0U, (uint32_t)2U * len27 * sizeof (uint8_t));
      uint8_t *u1 = tempBufferU8;
      uint8_t *u2 = tempBufferU8 + (uint32_t)32U;
      uint32_t sz_hash = (uint32_t)32U;
      uint32_t len38 = sz_hash + (uint32_t)32U;
      KRML_CHECK_SIZE(sizeof (uint8_t), len38);
      uint8_t mHash[len38];
      memset(mHash, 0U, len38 * sizeof (uint8_t));
      uint8_t *mHashHPart = mHash;
      uint8_t *mHashRPart = mHash;
      hash_256(m, mLen, mHashHPart);
      uint32_t len40 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        uint64_t *os = hashAsFelem;
        uint8_t *bj = mHashRPart + i * (uint32_t)8U;
        uint64_t u = load64_be(bj);
        uint64_t r12 = u;
        uint64_t x1 = r12;
        os[i] = x1;
      }
      uint32_t len50 = (uint32_t)4U;
      uint32_t lenByTwo3 = len50 >> (uint32_t)1U;
      for (uint32_t i = (uint32_t)0U; i < lenByTwo3; i++)
      {
        uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
        uint64_t left = hashAsFelem[i];
        uint64_t right = hashAsFelem[lenRight];
        hashAsFelem[i] = right;
        hashAsFelem[lenRight] = left;
      }
      uint32_t len41 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len41);
      uint64_t tempBuffer22[len41];
      memset(tempBuffer22, 0U, len41 * sizeof (uint64_t));
      uint64_t
      p3[4U] =
        {
          (uint64_t)17562291160714782033U,
          (uint64_t)13611842547513532036U,
          (uint64_t)18446744073709551615U,
          (uint64_t)18446744069414584320U
        };
      uint32_t len51 = (uint32_t)4U;
      uint64_t c2 = (uint64_t)0U;
      uint32_t k2 = len51 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
      {
        uint64_t t1 = hashAsFelem[(uint32_t)4U * i];
        uint64_t t20 = p3[(uint32_t)4U * i];
        c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t1, t20, tempBuffer22 + (uint32_t)4U * i);
        uint64_t t10 = hashAsFelem[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p3[(uint32_t)4U * i + (uint32_t)1U];
        c2 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c2,
            t10,
            t21,
            tempBuffer22 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = hashAsFelem[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p3[(uint32_t)4U * i + (uint32_t)2U];
        c2 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c2,
            t11,
            t22,
            tempBuffer22 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = hashAsFelem[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p3[(uint32_t)4U * i + (uint32_t)3U];
        c2 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c2,
            t12,
            t2,
            tempBuffer22 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k2; i < len51; i++)
      {
        uint64_t t1 = hashAsFelem[i];
        uint64_t t2 = p3[i];
        c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t1, t2, tempBuffer22 + i);
      }
      uint64_t r12 = c2;
      uint64_t r13 = r12;
      uint64_t mask = ~FStar_UInt64_eq_mask(r13, (uint64_t)0U);
      uint32_t len52 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len52; i++)
      {
        uint64_t x_i = tempBuffer22[i];
        uint64_t y_i = hashAsFelem[i];
        uint64_t r_i = (y_i & mask) | (x_i & ~mask);
        hashAsFelem[i] = r_i;
      }
      uint32_t len39 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len39);
      uint64_t tempBuffer2[(uint32_t)3U * len39];
      memset(tempBuffer2, 0U, (uint32_t)3U * len39 * sizeof (uint64_t));
      uint64_t *inverseS = tempBuffer2;
      uint64_t *u11 = tempBuffer2 + len39;
      uint64_t *u21 = tempBuffer2 + (uint32_t)2U * len39;
      uint32_t len42 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len42);
      uint64_t one[len42];
      memset(one, 0U, len42 * sizeof (uint64_t));
      one[0U] = (uint64_t)1U;
      uint32_t len53 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)1U; i < len53; i++)
      {
        one[i] = (uint64_t)0U;
      }
      montgomery_multiplication_buffer_dh_p256(one, sAsFelem, inverseS);
      montgomery_ladder_power_p256(inverseS,
        Hacl_Spec_ECDSA_Definition_prime256order_buffer,
        inverseS);
      uint32_t len43 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len43);
      uint64_t buffFromDB[len43];
      memset(buffFromDB, 0U, len43 * sizeof (uint64_t));
      uint32_t len54 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len54);
      uint64_t one0[len54];
      memset(one0, 0U, len54 * sizeof (uint64_t));
      one0[0U] = (uint64_t)1U;
      uint32_t len60 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)1U; i < len60; i++)
      {
        one0[i] = (uint64_t)0U;
      }
      montgomery_multiplication_buffer_dh_p256(one0, hashAsFelem, buffFromDB);
      uint32_t len55 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len55);
      uint64_t one1[len55];
      memset(one1, 0U, len55 * sizeof (uint64_t));
      one1[0U] = (uint64_t)1U;
      uint32_t len61 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)1U; i < len61; i++)
      {
        one1[i] = (uint64_t)0U;
      }
      montgomery_multiplication_buffer_dh_p256(one1, buffFromDB, buffFromDB);
      montgomery_multiplication_buffer_dh_p256(inverseS, buffFromDB, u11);
      uint32_t len44 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len44);
      uint64_t buffFromDB0[len44];
      memset(buffFromDB0, 0U, len44 * sizeof (uint64_t));
      uint32_t len56 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len56);
      uint64_t one2[len56];
      memset(one2, 0U, len56 * sizeof (uint64_t));
      one2[0U] = (uint64_t)1U;
      uint32_t len62 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)1U; i < len62; i++)
      {
        one2[i] = (uint64_t)0U;
      }
      montgomery_multiplication_buffer_dh_p256(one2, rAsFelem, buffFromDB0);
      uint32_t len57 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len57);
      uint64_t one3[len57];
      memset(one3, 0U, len57 * sizeof (uint64_t));
      one3[0U] = (uint64_t)1U;
      uint32_t len63 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)1U; i < len63; i++)
      {
        one3[i] = (uint64_t)0U;
      }
      montgomery_multiplication_buffer_dh_p256(one3, buffFromDB0, buffFromDB0);
      montgomery_multiplication_buffer_dh_p256(inverseS, buffFromDB0, u21);
      uint32_t len45 = (uint32_t)4U;
      uint32_t lenByTwo4 = len45 >> (uint32_t)1U;
      for (uint32_t i = (uint32_t)0U; i < lenByTwo4; i++)
      {
        uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
        uint64_t left = u11[i];
        uint64_t right = u11[lenRight];
        u11[i] = right;
        u11[lenRight] = left;
      }
      uint32_t len46 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len46; i++)
      {
        store64_be(u1 + i * (uint32_t)8U, u11[i]);
      }
      uint32_t len47 = (uint32_t)4U;
      uint32_t lenByTwo5 = len47 >> (uint32_t)1U;
      for (uint32_t i = (uint32_t)0U; i < lenByTwo5; i++)
      {
        uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
        uint64_t left = u21[i];
        uint64_t right = u21[lenRight];
        u21[i] = right;
        u21[lenRight] = left;
      }
      uint32_t len48 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len48; i++)
      {
        store64_be(u2 + i * (uint32_t)8U, u21[i]);
      }
      uint32_t len310 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len310 * (uint32_t)3U);
      uint64_t result[len310 * (uint32_t)3U];
      memset(result, 0U, len310 * (uint32_t)3U * sizeof (uint64_t));
      uint32_t len4 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len4 * (uint32_t)6U);
      uint64_t points[len4 * (uint32_t)6U];
      memset(points, 0U, len4 * (uint32_t)6U * sizeof (uint64_t));
      uint64_t *pointU1G = points;
      uint64_t *pointU2Q = points + (uint32_t)12U;
      secretToPublicWithoutNorm(Spec_ECC_Curves_P256, pointU1G, (void *)u1, tempBuffer1);
      scalarMultiplicationWithoutNorm(Spec_ECC_Curves_P256,
        publicKeyBuffer,
        pointU2Q,
        (void *)u2,
        tempBuffer1);
      uint64_t *tempBuffer17 = tempBuffer1;
      uint64_t *p4 = points;
      uint64_t *q = points + (uint32_t)12U;
      uint32_t len58 = (uint32_t)4U;
      uint64_t *sq_z1 = tempBuffer17;
      uint64_t *tr_z1 = tempBuffer17 + len58;
      uint64_t *sq_z2 = tempBuffer17 + (uint32_t)2U * len58;
      uint64_t *tr_z2 = tempBuffer17 + (uint32_t)3U * len58;
      uint64_t *x1 = p4;
      uint64_t *y1 = p4 + len58;
      uint64_t *z1 = p4 + (uint32_t)2U * len58;
      uint64_t *x2 = q;
      uint64_t *y2 = q + len58;
      uint64_t *z2 = q + (uint32_t)2U * len58;
      uint32_t len64 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len64);
      uint64_t t[(uint32_t)2U * len64];
      memset(t, 0U, (uint32_t)2U * len64 * sizeof (uint64_t));
      uint32_t len70 = (uint32_t)4U;
      uint32_t resLen0 = len70 + len70;
      memset(t, 0U, resLen0 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len70; i0++)
      {
        uint64_t *uu____0 = z1;
        uint64_t uu____1 = z1[i0];
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
        uint64_t r14 = c;
        t[i0 + i0] = r14;
      }
      uint64_t c3 = (uint64_t)0U;
      uint32_t k3 = resLen0 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k3 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t[(uint32_t)4U * i];
        uint64_t t20 = t[(uint32_t)4U * i];
        c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, t20, t + (uint32_t)4U * i);
        uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = t[(uint32_t)4U * i + (uint32_t)1U];
        c3 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c3,
            t10,
            t21,
            t + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = t[(uint32_t)4U * i + (uint32_t)2U];
        c3 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c3,
            t11,
            t22,
            t + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = t[(uint32_t)4U * i + (uint32_t)3U];
        c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k3; i < resLen0; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t2 = t[i];
        c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, t2, t + i);
      }
      uint64_t uu____2 = c3;
      KRML_CHECK_SIZE(sizeof (uint64_t), resLen0);
      uint64_t tmp3[resLen0];
      memset(tmp3, 0U, resLen0 * sizeof (uint64_t));
      for (uint32_t i = (uint32_t)0U; i < len70; i++)
      {
        uint128_t a2 = (uint128_t)z1[i] * z1[i];
        tmp3[(uint32_t)2U * i] = (uint64_t)a2;
        tmp3[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
      }
      uint64_t c4 = (uint64_t)0U;
      uint32_t k4 = resLen0 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k4 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t[(uint32_t)4U * i];
        uint64_t t20 = tmp3[(uint32_t)4U * i];
        c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t1, t20, t + (uint32_t)4U * i);
        uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = tmp3[(uint32_t)4U * i + (uint32_t)1U];
        c4 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c4,
            t10,
            t21,
            t + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = tmp3[(uint32_t)4U * i + (uint32_t)2U];
        c4 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c4,
            t11,
            t22,
            t + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = tmp3[(uint32_t)4U * i + (uint32_t)3U];
        c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k4; i < resLen0; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t2 = tmp3[i];
        c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t1, t2, t + i);
      }
      uint64_t uu____3 = c4;
      uint32_t len71 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len71; i0++)
      {
        uint32_t len8 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len8);
        uint64_t t2[(uint32_t)2U * len8];
        memset(t2, 0U, (uint32_t)2U * len8 * sizeof (uint64_t));
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c10;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len90 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len90 / (uint32_t)4U * (uint32_t)4U;
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
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len90; i++)
        {
          uint64_t t1 = t[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry1 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t[i] = elem;
        }
        t[len9] = carry1;
      }
      uint32_t len8 = (uint32_t)4U;
      uint64_t cin = t[len8];
      uint64_t *x_0 = t;
      uint32_t len90 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len90);
      uint64_t tempBuffer23[len90];
      memset(tempBuffer23, 0U, len90 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow0 = (uint64_t)0U;
      uint64_t
      p10[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len100 = (uint32_t)4U;
      uint64_t c5 = (uint64_t)0U;
      uint32_t k5 = len100 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k5 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_0[(uint32_t)4U * i];
        uint64_t t20 = p10[(uint32_t)4U * i];
        c5 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c5, t1, t20, tempBuffer23 + (uint32_t)4U * i);
        uint64_t t10 = x_0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p10[(uint32_t)4U * i + (uint32_t)1U];
        c5 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c5,
            t10,
            t21,
            tempBuffer23 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p10[(uint32_t)4U * i + (uint32_t)2U];
        c5 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c5,
            t11,
            t22,
            tempBuffer23 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p10[(uint32_t)4U * i + (uint32_t)3U];
        c5 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c5,
            t12,
            t2,
            tempBuffer23 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k5; i < len100; i++)
      {
        uint64_t t1 = x_0[i];
        uint64_t t2 = p10[i];
        c5 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c5, t1, t2, tempBuffer23 + i);
      }
      uint64_t r14 = c5;
      uint64_t carry00 = r14;
      uint64_t
      carry1 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry00,
          cin,
          (uint64_t)0U,
          &tempBufferForSubborrow0);
      uint64_t mask0 = ~FStar_UInt64_eq_mask(carry1, (uint64_t)0U);
      uint32_t len101 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len101; i++)
      {
        uint64_t x_i = tempBuffer23[i];
        uint64_t y_i = x_0[i];
        uint64_t r_i = (y_i & mask0) | (x_i & ~mask0);
        sq_z1[i] = r_i;
      }
      uint32_t len65 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len65);
      uint64_t t0[(uint32_t)2U * len65];
      memset(t0, 0U, (uint32_t)2U * len65 * sizeof (uint64_t));
      uint32_t len72 = (uint32_t)4U;
      uint32_t resLen1 = len72 + len72;
      memset(t0, 0U, resLen1 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len72; i0++)
      {
        uint64_t *uu____4 = z2;
        uint64_t uu____5 = z2[i0];
        uint64_t *res_ = t0 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = i0 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, uu____4[(uint32_t)4U * i], uu____5, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              uu____4[(uint32_t)4U * i + (uint32_t)1U],
              uu____5,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              uu____4[(uint32_t)4U * i + (uint32_t)2U],
              uu____5,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              uu____4[(uint32_t)4U * i + (uint32_t)3U],
              uu____5,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < i0; i++)
        {
          c = mul_carry_add_u64_st(c, uu____4[i], uu____5, res_ + i);
        }
        uint64_t r15 = c;
        t0[i0 + i0] = r15;
      }
      uint64_t c6 = (uint64_t)0U;
      uint32_t k6 = resLen1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k6 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t20 = t0[(uint32_t)4U * i];
        c6 = Lib_IntTypes_Intrinsics_add_carry_u64(c6, t1, t20, t0 + (uint32_t)4U * i);
        uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = t0[(uint32_t)4U * i + (uint32_t)1U];
        c6 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c6,
            t10,
            t21,
            t0 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = t0[(uint32_t)4U * i + (uint32_t)2U];
        c6 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c6,
            t11,
            t22,
            t0 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = t0[(uint32_t)4U * i + (uint32_t)3U];
        c6 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c6,
            t12,
            t2,
            t0 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k6; i < resLen1; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t2 = t0[i];
        c6 = Lib_IntTypes_Intrinsics_add_carry_u64(c6, t1, t2, t0 + i);
      }
      uint64_t uu____6 = c6;
      KRML_CHECK_SIZE(sizeof (uint64_t), resLen1);
      uint64_t tmp4[resLen1];
      memset(tmp4, 0U, resLen1 * sizeof (uint64_t));
      for (uint32_t i = (uint32_t)0U; i < len72; i++)
      {
        uint128_t a2 = (uint128_t)z2[i] * z2[i];
        tmp4[(uint32_t)2U * i] = (uint64_t)a2;
        tmp4[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
      }
      uint64_t c7 = (uint64_t)0U;
      uint32_t k7 = resLen1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k7 / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t20 = tmp4[(uint32_t)4U * i];
        c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t1, t20, t0 + (uint32_t)4U * i);
        uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = tmp4[(uint32_t)4U * i + (uint32_t)1U];
        c7 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c7,
            t10,
            t21,
            t0 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = tmp4[(uint32_t)4U * i + (uint32_t)2U];
        c7 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c7,
            t11,
            t22,
            t0 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = tmp4[(uint32_t)4U * i + (uint32_t)3U];
        c7 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c7,
            t12,
            t2,
            t0 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k7; i < resLen1; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t2 = tmp4[i];
        c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t1, t2, t0 + i);
      }
      uint64_t uu____7 = c7;
      uint32_t len73 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len73; i0++)
      {
        uint32_t len80 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len80);
        uint64_t t2[(uint32_t)2U * len80];
        memset(t2, 0U, (uint32_t)2U * len80 * sizeof (uint64_t));
        uint64_t t10 = t0[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c10;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len91 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len91 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t0[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t0[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len91; i++)
        {
          uint64_t t1 = t0[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry2 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t0[i] = elem;
        }
        t0[len9] = carry2;
      }
      uint32_t len80 = (uint32_t)4U;
      uint64_t cin0 = t0[len80];
      uint64_t *x_1 = t0;
      uint32_t len91 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len91);
      uint64_t tempBuffer24[len91];
      memset(tempBuffer24, 0U, len91 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow1 = (uint64_t)0U;
      uint64_t
      p11[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len102 = (uint32_t)4U;
      uint64_t c8 = (uint64_t)0U;
      uint32_t k8 = len102 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k8 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_1[(uint32_t)4U * i];
        uint64_t t20 = p11[(uint32_t)4U * i];
        c8 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c8, t1, t20, tempBuffer24 + (uint32_t)4U * i);
        uint64_t t10 = x_1[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p11[(uint32_t)4U * i + (uint32_t)1U];
        c8 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c8,
            t10,
            t21,
            tempBuffer24 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_1[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p11[(uint32_t)4U * i + (uint32_t)2U];
        c8 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c8,
            t11,
            t22,
            tempBuffer24 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_1[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p11[(uint32_t)4U * i + (uint32_t)3U];
        c8 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c8,
            t12,
            t2,
            tempBuffer24 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k8; i < len102; i++)
      {
        uint64_t t1 = x_1[i];
        uint64_t t2 = p11[i];
        c8 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c8, t1, t2, tempBuffer24 + i);
      }
      uint64_t r15 = c8;
      uint64_t carry01 = r15;
      uint64_t
      carry2 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry01,
          cin0,
          (uint64_t)0U,
          &tempBufferForSubborrow1);
      uint64_t mask1 = ~FStar_UInt64_eq_mask(carry2, (uint64_t)0U);
      uint32_t len103 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len103; i++)
      {
        uint64_t x_i = tempBuffer24[i];
        uint64_t y_i = x_1[i];
        uint64_t r_i = (y_i & mask1) | (x_i & ~mask1);
        sq_z2[i] = r_i;
      }
      uint32_t len66 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len66);
      uint64_t t3[(uint32_t)2U * len66];
      memset(t3, 0U, (uint32_t)2U * len66 * sizeof (uint64_t));
      uint32_t len74 = (uint32_t)4U;
      uint32_t resLen2 = len74 + len74;
      memset(t3, 0U, resLen2 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len74; i0++)
      {
        uint64_t uu____8 = z1[i0];
        uint64_t *res_ = t3 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len74 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z1[(uint32_t)4U * i], uu____8, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              sq_z1[(uint32_t)4U * i + (uint32_t)1U],
              uu____8,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              sq_z1[(uint32_t)4U * i + (uint32_t)2U],
              uu____8,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              sq_z1[(uint32_t)4U * i + (uint32_t)3U],
              uu____8,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len74; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z1[i], uu____8, res_ + i);
        }
        uint64_t r16 = c;
        t3[len74 + i0] = r16;
      }
      uint32_t len75 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len75; i0++)
      {
        uint32_t len81 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len81);
        uint64_t t2[(uint32_t)2U * len81];
        memset(t2, 0U, (uint32_t)2U * len81 * sizeof (uint64_t));
        uint64_t t10 = t3[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c10;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len92 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len92 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t3[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t3[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t3[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t3[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len92; i++)
        {
          uint64_t t1 = t3[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry3 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t3[i] = elem;
        }
        t3[len9] = carry3;
      }
      uint32_t len81 = (uint32_t)4U;
      uint64_t cin1 = t3[len81];
      uint64_t *x_2 = t3;
      uint32_t len92 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len92);
      uint64_t tempBuffer25[len92];
      memset(tempBuffer25, 0U, len92 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow2 = (uint64_t)0U;
      uint64_t
      p12[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len104 = (uint32_t)4U;
      uint64_t c9 = (uint64_t)0U;
      uint32_t k9 = len104 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k9 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_2[(uint32_t)4U * i];
        uint64_t t20 = p12[(uint32_t)4U * i];
        c9 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c9, t1, t20, tempBuffer25 + (uint32_t)4U * i);
        uint64_t t10 = x_2[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p12[(uint32_t)4U * i + (uint32_t)1U];
        c9 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c9,
            t10,
            t21,
            tempBuffer25 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_2[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p12[(uint32_t)4U * i + (uint32_t)2U];
        c9 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c9,
            t11,
            t22,
            tempBuffer25 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_2[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p12[(uint32_t)4U * i + (uint32_t)3U];
        c9 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c9,
            t12,
            t2,
            tempBuffer25 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k9; i < len104; i++)
      {
        uint64_t t1 = x_2[i];
        uint64_t t2 = p12[i];
        c9 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c9, t1, t2, tempBuffer25 + i);
      }
      uint64_t r16 = c9;
      uint64_t carry02 = r16;
      uint64_t
      carry3 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry02,
          cin1,
          (uint64_t)0U,
          &tempBufferForSubborrow2);
      uint64_t mask2 = ~FStar_UInt64_eq_mask(carry3, (uint64_t)0U);
      uint32_t len105 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len105; i++)
      {
        uint64_t x_i = tempBuffer25[i];
        uint64_t y_i = x_2[i];
        uint64_t r_i = (y_i & mask2) | (x_i & ~mask2);
        tr_z1[i] = r_i;
      }
      uint32_t len67 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len67);
      uint64_t t4[(uint32_t)2U * len67];
      memset(t4, 0U, (uint32_t)2U * len67 * sizeof (uint64_t));
      uint32_t len76 = (uint32_t)4U;
      uint32_t resLen3 = len76 + len76;
      memset(t4, 0U, resLen3 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len76; i0++)
      {
        uint64_t uu____9 = z2[i0];
        uint64_t *res_ = t4 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len76 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z2[(uint32_t)4U * i], uu____9, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              sq_z2[(uint32_t)4U * i + (uint32_t)1U],
              uu____9,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              sq_z2[(uint32_t)4U * i + (uint32_t)2U],
              uu____9,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              sq_z2[(uint32_t)4U * i + (uint32_t)3U],
              uu____9,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len76; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z2[i], uu____9, res_ + i);
        }
        uint64_t r17 = c;
        t4[len76 + i0] = r17;
      }
      uint32_t len77 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len77; i0++)
      {
        uint32_t len82 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len82);
        uint64_t t2[(uint32_t)2U * len82];
        memset(t2, 0U, (uint32_t)2U * len82 * sizeof (uint64_t));
        uint64_t t10 = t4[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c10;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len93 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len93 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t4[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t4[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t4[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t4[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len93; i++)
        {
          uint64_t t1 = t4[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry4 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t4[i] = elem;
        }
        t4[len9] = carry4;
      }
      uint32_t len82 = (uint32_t)4U;
      uint64_t cin2 = t4[len82];
      uint64_t *x_3 = t4;
      uint32_t len93 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len93);
      uint64_t tempBuffer26[len93];
      memset(tempBuffer26, 0U, len93 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow3 = (uint64_t)0U;
      uint64_t
      p13[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len106 = (uint32_t)4U;
      uint64_t c10 = (uint64_t)0U;
      uint32_t k10 = len106 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k10 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_3[(uint32_t)4U * i];
        uint64_t t20 = p13[(uint32_t)4U * i];
        c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t20, tempBuffer26 + (uint32_t)4U * i);
        uint64_t t10 = x_3[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p13[(uint32_t)4U * i + (uint32_t)1U];
        c10 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
            t10,
            t21,
            tempBuffer26 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_3[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p13[(uint32_t)4U * i + (uint32_t)2U];
        c10 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
            t11,
            t22,
            tempBuffer26 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_3[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p13[(uint32_t)4U * i + (uint32_t)3U];
        c10 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
            t12,
            t2,
            tempBuffer26 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k10; i < len106; i++)
      {
        uint64_t t1 = x_3[i];
        uint64_t t2 = p13[i];
        c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t2, tempBuffer26 + i);
      }
      uint64_t r17 = c10;
      uint64_t carry03 = r17;
      uint64_t
      carry4 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry03,
          cin2,
          (uint64_t)0U,
          &tempBufferForSubborrow3);
      uint64_t mask3 = ~FStar_UInt64_eq_mask(carry4, (uint64_t)0U);
      uint32_t len107 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len107; i++)
      {
        uint64_t x_i = tempBuffer26[i];
        uint64_t y_i = x_3[i];
        uint64_t r_i = (y_i & mask3) | (x_i & ~mask3);
        tr_z2[i] = r_i;
      }
      uint32_t len68 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len68);
      uint64_t t5[(uint32_t)2U * len68];
      memset(t5, 0U, (uint32_t)2U * len68 * sizeof (uint64_t));
      uint32_t len78 = (uint32_t)4U;
      uint32_t resLen4 = len78 + len78;
      memset(t5, 0U, resLen4 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len78; i0++)
      {
        uint64_t uu____10 = x2[i0];
        uint64_t *res_ = t5 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len78 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z1[(uint32_t)4U * i], uu____10, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              sq_z1[(uint32_t)4U * i + (uint32_t)1U],
              uu____10,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              sq_z1[(uint32_t)4U * i + (uint32_t)2U],
              uu____10,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              sq_z1[(uint32_t)4U * i + (uint32_t)3U],
              uu____10,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len78; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z1[i], uu____10, res_ + i);
        }
        uint64_t r18 = c;
        t5[len78 + i0] = r18;
      }
      uint32_t len79 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len79; i0++)
      {
        uint32_t len83 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len83);
        uint64_t t2[(uint32_t)2U * len83];
        memset(t2, 0U, (uint32_t)2U * len83 * sizeof (uint64_t));
        uint64_t t10 = t5[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c11 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c11;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len94 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len94 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t5[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t5[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t5[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t5[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len94; i++)
        {
          uint64_t t1 = t5[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry5 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t5[i] = elem;
        }
        t5[len9] = carry5;
      }
      uint32_t len83 = (uint32_t)4U;
      uint64_t cin3 = t5[len83];
      uint64_t *x_4 = t5;
      uint32_t len94 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len94);
      uint64_t tempBuffer27[len94];
      memset(tempBuffer27, 0U, len94 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow4 = (uint64_t)0U;
      uint64_t
      p14[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len108 = (uint32_t)4U;
      uint64_t c11 = (uint64_t)0U;
      uint32_t k11 = len108 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k11 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_4[(uint32_t)4U * i];
        uint64_t t20 = p14[(uint32_t)4U * i];
        c11 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c11, t1, t20, tempBuffer27 + (uint32_t)4U * i);
        uint64_t t10 = x_4[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p14[(uint32_t)4U * i + (uint32_t)1U];
        c11 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c11,
            t10,
            t21,
            tempBuffer27 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_4[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p14[(uint32_t)4U * i + (uint32_t)2U];
        c11 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c11,
            t11,
            t22,
            tempBuffer27 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_4[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p14[(uint32_t)4U * i + (uint32_t)3U];
        c11 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c11,
            t12,
            t2,
            tempBuffer27 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k11; i < len108; i++)
      {
        uint64_t t1 = x_4[i];
        uint64_t t2 = p14[i];
        c11 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c11, t1, t2, tempBuffer27 + i);
      }
      uint64_t r18 = c11;
      uint64_t carry04 = r18;
      uint64_t
      carry5 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry04,
          cin3,
          (uint64_t)0U,
          &tempBufferForSubborrow4);
      uint64_t mask4 = ~FStar_UInt64_eq_mask(carry5, (uint64_t)0U);
      uint32_t len109 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len109; i++)
      {
        uint64_t x_i = tempBuffer27[i];
        uint64_t y_i = x_4[i];
        uint64_t r_i = (y_i & mask4) | (x_i & ~mask4);
        sq_z1[i] = r_i;
      }
      uint32_t len69 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len69);
      uint64_t t6[(uint32_t)2U * len69];
      memset(t6, 0U, (uint32_t)2U * len69 * sizeof (uint64_t));
      uint32_t len710 = (uint32_t)4U;
      uint32_t resLen5 = len710 + len710;
      memset(t6, 0U, resLen5 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len710; i0++)
      {
        uint64_t uu____11 = x1[i0];
        uint64_t *res_ = t6 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len710 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z2[(uint32_t)4U * i], uu____11, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              sq_z2[(uint32_t)4U * i + (uint32_t)1U],
              uu____11,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              sq_z2[(uint32_t)4U * i + (uint32_t)2U],
              uu____11,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              sq_z2[(uint32_t)4U * i + (uint32_t)3U],
              uu____11,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len710; i++)
        {
          c = mul_carry_add_u64_st(c, sq_z2[i], uu____11, res_ + i);
        }
        uint64_t r19 = c;
        t6[len710 + i0] = r19;
      }
      uint32_t len711 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len711; i0++)
      {
        uint32_t len84 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len84);
        uint64_t t2[(uint32_t)2U * len84];
        memset(t2, 0U, (uint32_t)2U * len84 * sizeof (uint64_t));
        uint64_t t10 = t6[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c12 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c12;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len95 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len95 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t6[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t6[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t6[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t6[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len95; i++)
        {
          uint64_t t1 = t6[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry6 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t6[i] = elem;
        }
        t6[len9] = carry6;
      }
      uint32_t len84 = (uint32_t)4U;
      uint64_t cin4 = t6[len84];
      uint64_t *x_5 = t6;
      uint32_t len95 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len95);
      uint64_t tempBuffer28[len95];
      memset(tempBuffer28, 0U, len95 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow5 = (uint64_t)0U;
      uint64_t
      p15[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len1010 = (uint32_t)4U;
      uint64_t c12 = (uint64_t)0U;
      uint32_t k12 = len1010 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k12 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_5[(uint32_t)4U * i];
        uint64_t t20 = p15[(uint32_t)4U * i];
        c12 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c12, t1, t20, tempBuffer28 + (uint32_t)4U * i);
        uint64_t t10 = x_5[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p15[(uint32_t)4U * i + (uint32_t)1U];
        c12 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c12,
            t10,
            t21,
            tempBuffer28 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_5[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p15[(uint32_t)4U * i + (uint32_t)2U];
        c12 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c12,
            t11,
            t22,
            tempBuffer28 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_5[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p15[(uint32_t)4U * i + (uint32_t)3U];
        c12 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c12,
            t12,
            t2,
            tempBuffer28 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k12; i < len1010; i++)
      {
        uint64_t t1 = x_5[i];
        uint64_t t2 = p15[i];
        c12 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c12, t1, t2, tempBuffer28 + i);
      }
      uint64_t r19 = c12;
      uint64_t carry05 = r19;
      uint64_t
      carry6 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry05,
          cin4,
          (uint64_t)0U,
          &tempBufferForSubborrow5);
      uint64_t mask5 = ~FStar_UInt64_eq_mask(carry6, (uint64_t)0U);
      uint32_t len1011 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len1011; i++)
      {
        uint64_t x_i = tempBuffer28[i];
        uint64_t y_i = x_5[i];
        uint64_t r_i = (y_i & mask5) | (x_i & ~mask5);
        sq_z2[i] = r_i;
      }
      uint32_t len610 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len610);
      uint64_t t7[(uint32_t)2U * len610];
      memset(t7, 0U, (uint32_t)2U * len610 * sizeof (uint64_t));
      uint32_t len712 = (uint32_t)4U;
      uint32_t resLen6 = len712 + len712;
      memset(t7, 0U, resLen6 * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len712; i0++)
      {
        uint64_t uu____12 = y2[i0];
        uint64_t *res_ = t7 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len712 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, tr_z1[(uint32_t)4U * i], uu____12, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              tr_z1[(uint32_t)4U * i + (uint32_t)1U],
              uu____12,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              tr_z1[(uint32_t)4U * i + (uint32_t)2U],
              uu____12,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              tr_z1[(uint32_t)4U * i + (uint32_t)3U],
              uu____12,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len712; i++)
        {
          c = mul_carry_add_u64_st(c, tr_z1[i], uu____12, res_ + i);
        }
        uint64_t r110 = c;
        t7[len712 + i0] = r110;
      }
      uint32_t len713 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len713; i0++)
      {
        uint32_t len85 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len85);
        uint64_t t2[(uint32_t)2U * len85];
        memset(t2, 0U, (uint32_t)2U * len85 * sizeof (uint64_t));
        uint64_t t10 = t7[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c13 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c13;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len96 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len96 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t7[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t7[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t7[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t7[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len96; i++)
        {
          uint64_t t1 = t7[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry7 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t7[i] = elem;
        }
        t7[len9] = carry7;
      }
      uint32_t len85 = (uint32_t)4U;
      uint64_t cin5 = t7[len85];
      uint64_t *x_6 = t7;
      uint32_t len96 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len96);
      uint64_t tempBuffer29[len96];
      memset(tempBuffer29, 0U, len96 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow6 = (uint64_t)0U;
      uint64_t
      p16[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len1012 = (uint32_t)4U;
      uint64_t c13 = (uint64_t)0U;
      uint32_t k13 = len1012 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k13 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_6[(uint32_t)4U * i];
        uint64_t t20 = p16[(uint32_t)4U * i];
        c13 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c13, t1, t20, tempBuffer29 + (uint32_t)4U * i);
        uint64_t t10 = x_6[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p16[(uint32_t)4U * i + (uint32_t)1U];
        c13 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c13,
            t10,
            t21,
            tempBuffer29 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_6[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p16[(uint32_t)4U * i + (uint32_t)2U];
        c13 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c13,
            t11,
            t22,
            tempBuffer29 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_6[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p16[(uint32_t)4U * i + (uint32_t)3U];
        c13 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c13,
            t12,
            t2,
            tempBuffer29 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k13; i < len1012; i++)
      {
        uint64_t t1 = x_6[i];
        uint64_t t2 = p16[i];
        c13 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c13, t1, t2, tempBuffer29 + i);
      }
      uint64_t r110 = c13;
      uint64_t carry06 = r110;
      uint64_t
      carry7 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry06,
          cin5,
          (uint64_t)0U,
          &tempBufferForSubborrow6);
      uint64_t mask6 = ~FStar_UInt64_eq_mask(carry7, (uint64_t)0U);
      uint32_t len1013 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len1013; i++)
      {
        uint64_t x_i = tempBuffer29[i];
        uint64_t y_i = x_6[i];
        uint64_t r_i = (y_i & mask6) | (x_i & ~mask6);
        tr_z1[i] = r_i;
      }
      uint32_t len611 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len611);
      uint64_t t8[(uint32_t)2U * len611];
      memset(t8, 0U, (uint32_t)2U * len611 * sizeof (uint64_t));
      uint32_t len7 = (uint32_t)4U;
      uint32_t resLen = len7 + len7;
      memset(t8, 0U, resLen * sizeof (uint64_t));
      for (uint32_t i0 = (uint32_t)0U; i0 < len7; i0++)
      {
        uint64_t uu____13 = y1[i0];
        uint64_t *res_ = t8 + i0;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len7 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          c = mul_carry_add_u64_st(c, tr_z2[(uint32_t)4U * i], uu____13, res_ + (uint32_t)4U * i);
          c =
            mul_carry_add_u64_st(c,
              tr_z2[(uint32_t)4U * i + (uint32_t)1U],
              uu____13,
              res_ + (uint32_t)4U * i + (uint32_t)1U);
          c =
            mul_carry_add_u64_st(c,
              tr_z2[(uint32_t)4U * i + (uint32_t)2U],
              uu____13,
              res_ + (uint32_t)4U * i + (uint32_t)2U);
          c =
            mul_carry_add_u64_st(c,
              tr_z2[(uint32_t)4U * i + (uint32_t)3U],
              uu____13,
              res_ + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len7; i++)
        {
          c = mul_carry_add_u64_st(c, tr_z2[i], uu____13, res_ + i);
        }
        uint64_t r111 = c;
        t8[len7 + i0] = r111;
      }
      uint32_t len714 = (uint32_t)4U;
      for (uint32_t i0 = (uint32_t)0U; i0 < len714; i0++)
      {
        uint32_t len86 = (uint32_t)4U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len86);
        uint64_t t2[(uint32_t)2U * len86];
        memset(t2, 0U, (uint32_t)2U * len86 * sizeof (uint64_t));
        uint64_t t10 = t8[0U];
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
        uint64_t h0120 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h0120;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t10;
        uint64_t l01 = (uint64_t)res;
        uint64_t h0121 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h0121;
        uint64_t l = o1[0U];
        uint64_t c14 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c14;
        uint128_t res1 = (uint128_t)f3 * t10;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h012 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h012;
        uint32_t len97 = (uint32_t)4U * (uint32_t)2U;
        uint64_t c = (uint64_t)0U;
        uint32_t k = len97 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = t8[(uint32_t)4U * i];
          uint64_t t210 = t2[(uint32_t)4U * i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t210, t2 + (uint32_t)4U * i);
          uint64_t t11 = t8[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t11,
              t211,
              t2 + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t12 = t8[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t12,
              t212,
              t2 + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t13 = t8[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
          c =
            Lib_IntTypes_Intrinsics_add_carry_u64(c,
              t13,
              t21,
              t2 + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len97; i++)
        {
          uint64_t t1 = t8[i];
          uint64_t t21 = t2[i];
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t21, t2 + i);
        }
        uint64_t carry8 = c;
        uint32_t len9 = (uint32_t)7U;
        for (uint32_t i = (uint32_t)0U; i < len9; i++)
        {
          uint64_t elem = t2[(uint32_t)1U + i];
          t8[i] = elem;
        }
        t8[len9] = carry8;
      }
      uint32_t len86 = (uint32_t)4U;
      uint64_t cin6 = t8[len86];
      uint64_t *x_ = t8;
      uint32_t len9 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len9);
      uint64_t tempBuffer210[len9];
      memset(tempBuffer210, 0U, len9 * sizeof (uint64_t));
      uint64_t tempBufferForSubborrow = (uint64_t)0U;
      uint64_t
      p1[4U] =
        {
          (uint64_t)0xffffffffffffffffU,
          (uint64_t)0xffffffffU,
          (uint64_t)0U,
          (uint64_t)0xffffffff00000001U
        };
      uint32_t len1014 = (uint32_t)4U;
      uint64_t c14 = (uint64_t)0U;
      uint32_t k14 = len1014 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k14 / (uint32_t)4U; i++)
      {
        uint64_t t1 = x_[(uint32_t)4U * i];
        uint64_t t20 = p1[(uint32_t)4U * i];
        c14 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c14, t1, t20, tempBuffer210 + (uint32_t)4U * i);
        uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
        c14 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c14,
            t10,
            t21,
            tempBuffer210 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
        c14 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c14,
            t11,
            t22,
            tempBuffer210 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
        c14 =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c14,
            t12,
            t2,
            tempBuffer210 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k14; i < len1014; i++)
      {
        uint64_t t1 = x_[i];
        uint64_t t2 = p1[i];
        c14 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c14, t1, t2, tempBuffer210 + i);
      }
      uint64_t r111 = c14;
      uint64_t carry07 = r111;
      uint64_t
      carry8 =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(carry07,
          cin6,
          (uint64_t)0U,
          &tempBufferForSubborrow);
      uint64_t mask7 = ~FStar_UInt64_eq_mask(carry8, (uint64_t)0U);
      uint32_t len10 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len10; i++)
      {
        uint64_t x_i = tempBuffer210[i];
        uint64_t y_i = x_[i];
        uint64_t r_i = (y_i & mask7) | (x_i & ~mask7);
        tr_z2[i] = r_i;
      }
      uint64_t tmp5 = (uint64_t)0U;
      tmp5 = (uint64_t)18446744073709551615U;
      uint32_t len612 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len612; i++)
      {
        uint64_t a_i = sq_z1[i];
        uint64_t b_i = sq_z2[i];
        uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
        uint64_t tmp0 = tmp5;
        tmp5 = r_i & tmp0;
      }
      uint64_t r112 = ~tmp5;
      uint64_t tmp6 = (uint64_t)0U;
      tmp6 = (uint64_t)18446744073709551615U;
      uint32_t len613 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len613; i++)
      {
        uint64_t a_i = sq_z1[i];
        uint64_t b_i = sq_z2[i];
        uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
        uint64_t tmp0 = tmp6;
        tmp6 = r_i & tmp0;
      }
      uint64_t uu____14 = tmp6;
      bool equalX = r112 == (uint64_t)0U;
      uint64_t tmp7 = (uint64_t)0U;
      tmp7 = (uint64_t)18446744073709551615U;
      uint32_t len614 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len614; i++)
      {
        uint64_t a_i = tr_z1[i];
        uint64_t b_i = tr_z2[i];
        uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
        uint64_t tmp0 = tmp7;
        tmp7 = r_i & tmp0;
      }
      uint64_t r113 = ~tmp7;
      uint64_t tmp8 = (uint64_t)0U;
      tmp8 = (uint64_t)18446744073709551615U;
      uint32_t len6 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len6; i++)
      {
        uint64_t a_i = tr_z1[i];
        uint64_t b_i = tr_z2[i];
        uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
        uint64_t tmp0 = tmp8;
        tmp8 = r_i & tmp0;
      }
      uint64_t uu____15 = tmp8;
      bool equalY = r113 == (uint64_t)0U;
      bool equalXAndY = equalX && equalY;
      if (equalXAndY)
      {
        uint32_t len615 = (uint32_t)4U;
        uint64_t *pY = p4 + len615;
        uint64_t *pZ = p4 + (uint32_t)2U * len615;
        uint64_t *x3 = result;
        uint64_t *y3 = result + len615;
        uint64_t *z3 = result + (uint32_t)2U * len615;
        uint64_t *delta = tempBuffer17;
        uint64_t *gamma = tempBuffer17 + len615;
        uint64_t *beta = tempBuffer17 + (uint32_t)2U * len615;
        uint64_t *alpha = tempBuffer17 + (uint32_t)3U * len615;
        uint64_t *fourBeta = tempBuffer17 + (uint32_t)4U * len615;
        uint64_t *eightBeta = tempBuffer17 + (uint32_t)5U * len615;
        uint64_t *eightGamma = tempBuffer17 + (uint32_t)6U * len615;
        uint64_t *tmp = tempBuffer17 + (uint32_t)7U * len615;
        uint32_t coordinateLen = (uint32_t)4U;
        uint64_t *pX1 = p4;
        uint64_t *pY1 = p4 + coordinateLen;
        uint64_t *pZ1 = p4 + (uint32_t)2U * coordinateLen;
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
      else
      {
        point_add_p256(p4, q, result, tempBuffer17);
      }
      norm(Spec_ECC_Curves_P256, result, result, tempBuffer17);
      uint32_t len49 = (uint32_t)4U;
      uint64_t *zCoordinate0 = result + (uint32_t)2U * len49;
      uint64_t tmp9 = (uint64_t)18446744073709551615U;
      uint32_t len59 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len59; i++)
      {
        uint64_t a_i = zCoordinate0[i];
        uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
        uint64_t tmp0 = tmp9;
        tmp9 = r_i & tmp0;
      }
      uint64_t f0 = tmp9;
      bool resultIsPAI = f0 == (uint64_t)0xffffffffffffffffU;
      uint64_t *xCoordinateSum = result;
      memcpy(x, xCoordinateSum, (uint32_t)4U * sizeof (uint64_t));
      uint32_t len410 = (uint32_t)4U;
      KRML_CHECK_SIZE(sizeof (uint64_t), len410);
      uint64_t tempBuffer211[len410];
      memset(tempBuffer211, 0U, len410 * sizeof (uint64_t));
      uint64_t
      p[4U] =
        {
          (uint64_t)17562291160714782033U,
          (uint64_t)13611842547513532036U,
          (uint64_t)18446744073709551615U,
          (uint64_t)18446744069414584320U
        };
      uint32_t len510 = (uint32_t)4U;
      uint64_t c = (uint64_t)0U;
      uint32_t k = len510 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = x[(uint32_t)4U * i];
        uint64_t t20 = p[(uint32_t)4U * i];
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tempBuffer211 + (uint32_t)4U * i);
        uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
        c =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
            t10,
            t21,
            tempBuffer211 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
        c =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
            t11,
            t22,
            tempBuffer211 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
        c =
          Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
            t12,
            t2,
            tempBuffer211 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len510; i++)
      {
        uint64_t t1 = x[i];
        uint64_t t2 = p[i];
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tempBuffer211 + i);
      }
      uint64_t r114 = c;
      uint64_t r115 = r114;
      uint64_t mask8 = ~FStar_UInt64_eq_mask(r115, (uint64_t)0U);
      uint32_t len5 = (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < len5; i++)
      {
        uint64_t x_i = tempBuffer211[i];
        uint64_t y_i = x[i];
        uint64_t r_i = (y_i & mask8) | (x_i & ~mask8);
        x[i] = r_i;
      }
      bool r116 = !resultIsPAI;
      bool state = r116;
      if (state == false)
      {
        r1 = false;
      }
      else
      {
        uint64_t tmp10 = (uint64_t)0U;
        tmp10 = (uint64_t)18446744073709551615U;
        uint32_t len28 = (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < len28; i++)
        {
          uint64_t a_i = x[i];
          uint64_t b_i = rAsFelem[i];
          uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
          uint64_t tmp0 = tmp10;
          tmp10 = r_i & tmp0;
        }
        uint64_t r117 = ~tmp10;
        uint64_t tmp = (uint64_t)0U;
        tmp = (uint64_t)18446744073709551615U;
        uint32_t len2 = (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < len2; i++)
        {
          uint64_t a_i = x[i];
          uint64_t b_i = rAsFelem[i];
          uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
          uint64_t tmp0 = tmp;
          tmp = r_i & tmp0;
        }
        uint64_t uu____16 = tmp;
        r1 = r117 == (uint64_t)0U;
      }
    }
  }
  bool result = r1;
  return result;
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
  uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
  for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256) - (uint32_t)1U - i0;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)4U
      * (uint32_t)8U
      - (uint32_t)1U
      - bit0 / (uint32_t)8U]
      >> bit0 % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len21 = (uint32_t)12U;
    for (uint32_t i = (uint32_t)0U; i < len21; i++)
    {
      uint64_t dummy = mask & (q[i] ^ resultBuffer[i]);
      q[i] = q[i] ^ dummy;
      resultBuffer[i] = resultBuffer[i] ^ dummy;
    }
    point_add_p256(q, resultBuffer, resultBuffer, buff);
    point_double_p256(q, q, buff);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len2 = (uint32_t)12U;
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint64_t dummy = mask0 & (q[i] ^ resultBuffer[i]);
      q[i] = q[i] ^ dummy;
      resultBuffer[i] = resultBuffer[i] ^ dummy;
    }
  }
  norm(Spec_ECC_Curves_P256, q, resultBuffer, buff);
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

uint64_t Hacl_P256_ecp384dh_i(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len);
  uint64_t tempBuffer[(uint32_t)20U * len];
  memset(tempBuffer, 0U, (uint32_t)20U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len10 = (uint32_t)6U;
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len10;
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
  uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
  for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384) - (uint32_t)1U - i0;
    uint64_t
    bit =
      (uint64_t)(scalar[(uint32_t)6U
      * (uint32_t)8U
      - (uint32_t)1U
      - bit0 / (uint32_t)8U]
      >> bit0 % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t mask = (uint64_t)0U - bit;
    uint32_t len21 = (uint32_t)18U;
    for (uint32_t i = (uint32_t)0U; i < len21; i++)
    {
      uint64_t dummy = mask & (q[i] ^ resultBuffer[i]);
      q[i] = q[i] ^ dummy;
      resultBuffer[i] = resultBuffer[i] ^ dummy;
    }
    point_add_p384(q, resultBuffer, resultBuffer, buff);
    point_double_p384(q, q, buff);
    uint64_t mask0 = (uint64_t)0U - bit;
    uint32_t len2 = (uint32_t)18U;
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint64_t dummy = mask0 & (q[i] ^ resultBuffer[i]);
      q[i] = q[i] ^ dummy;
      resultBuffer[i] = resultBuffer[i] ^ dummy;
    }
  }
  norm(Spec_ECC_Curves_P384, q, resultBuffer, buff);
  uint32_t len11 = (uint32_t)6U;
  uint32_t start = len11 * (uint32_t)2U;
  uint64_t *zCoordinate = resultBuffer + start;
  uint64_t tmp = (uint64_t)18446744073709551615U;
  uint32_t len21 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  uint64_t r0 = r;
  uint32_t len1 = (uint32_t)6U;
  uint32_t scalarLen = (uint32_t)48U;
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + len1;
  uint8_t *resultX = result;
  uint8_t *resultY = result + scalarLen;
  uint32_t len2 = (uint32_t)6U;
  uint32_t lenByTwo = len2 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i;
    uint64_t left = resultBufferX[i];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i] = right;
    resultBufferX[lenRight] = left;
  }
  uint32_t len22 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len22; i++)
  {
    store64_be(resultX + i * (uint32_t)8U, resultBufferX[i]);
  }
  uint32_t len23 = (uint32_t)6U;
  uint32_t lenByTwo0 = len23 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i;
    uint64_t left = resultBufferY[i];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i] = right;
    resultBufferY[lenRight] = left;
  }
  uint32_t len24 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len24; i++)
  {
    store64_be(resultY + i * (uint32_t)8U, resultBufferY[i]);
  }
  bool flag = r0 == (uint64_t)0U;
  return (uint64_t)flag;
}

uint64_t Hacl_P256_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len10 = (uint32_t)4U;
  uint32_t coordLen = (uint32_t)32U;
  uint8_t *pointScalarX = pubKey;
  uint8_t *pointScalarY = pubKey + coordLen;
  uint64_t *pointX = pkF;
  uint64_t *pointY = pkF + len10;
  uint64_t *pointZ = pkF + (uint32_t)2U * len10;
  uint32_t len20 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    uint64_t *os = pointX;
    uint8_t *bj = pointScalarX + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint32_t len30 = (uint32_t)4U;
  uint32_t lenByTwo = len30 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = pointX[i];
    uint64_t right = pointX[lenRight];
    pointX[i] = right;
    pointX[lenRight] = left;
  }
  uint32_t len21 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    uint64_t *os = pointY;
    uint8_t *bj = pointScalarY + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint32_t len31 = (uint32_t)4U;
  uint32_t lenByTwo0 = len31 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = pointY[i];
    uint64_t right = pointY[lenRight];
    pointY[i] = right;
    pointY[lenRight] = left;
  }
  pointZ[0U] = (uint64_t)1U;
  uint32_t len22 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)1U; i < len22; i++)
  {
    pointZ[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len11);
  uint64_t tempBuffer[(uint32_t)20U * len11];
  memset(tempBuffer, 0U, (uint32_t)20U * len11 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint(Spec_ECC_Curves_P256, pkF, tempBuffer);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len2 = (uint32_t)4U;
    uint64_t *q = tempBuffer;
    uint64_t *buff = tempBuffer + (uint32_t)3U * len2;
    uint32_t len32 = (uint32_t)4U;
    uint64_t *x = q;
    uint64_t *y = q + len32;
    uint64_t *z = q + (uint32_t)2U * len32;
    uint32_t len40 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len40; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len41 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len41; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len42 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len42; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len33 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len33;
    uint64_t *p_z = pkF + (uint32_t)2U * len33;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len33;
    uint64_t *r_z = rF + (uint32_t)2U * len33;
    uint32_t len4 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len4);
    uint64_t multBuffer[(uint32_t)2U * len4];
    memset(multBuffer, 0U, (uint32_t)2U * len4 * sizeof (uint64_t));
    uint32_t len50 = (uint32_t)4U;
    uint64_t *oToZero0 = multBuffer;
    uint64_t *oToCopy0 = multBuffer + len50;
    memcpy(oToCopy0, p_x, len50 * sizeof (uint64_t));
    uint32_t len6 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len6; i++)
    {
      oToZero0[i] = (uint64_t)0U;
    }
    reduction(Spec_ECC_Curves_P256, multBuffer, r_x);
    uint32_t len43 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len43);
    uint64_t multBuffer0[(uint32_t)2U * len43];
    memset(multBuffer0, 0U, (uint32_t)2U * len43 * sizeof (uint64_t));
    uint32_t len51 = (uint32_t)4U;
    uint64_t *oToZero1 = multBuffer0;
    uint64_t *oToCopy1 = multBuffer0 + len51;
    memcpy(oToCopy1, p_y, len51 * sizeof (uint64_t));
    uint32_t len60 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len60; i++)
    {
      oToZero1[i] = (uint64_t)0U;
    }
    reduction(Spec_ECC_Curves_P256, multBuffer0, r_y);
    uint32_t len44 = (uint32_t)4U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len44);
    uint64_t multBuffer1[(uint32_t)2U * len44];
    memset(multBuffer1, 0U, (uint32_t)2U * len44 * sizeof (uint64_t));
    uint32_t len5 = (uint32_t)4U;
    uint64_t *oToZero = multBuffer1;
    uint64_t *oToCopy = multBuffer1 + len5;
    memcpy(oToCopy, p_z, len5 * sizeof (uint64_t));
    uint32_t len61 = (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < len61; i++)
    {
      oToZero[i] = (uint64_t)0U;
    }
    reduction(Spec_ECC_Curves_P256, multBuffer1, r_z);
    uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
    for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
    {
      uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256) - (uint32_t)1U - i0;
      uint64_t
      bit =
        (uint64_t)(scalar[(uint32_t)4U
        * (uint32_t)8U
        - (uint32_t)1U
        - bit0 / (uint32_t)8U]
        >> bit0 % (uint32_t)8U
        & (uint8_t)1U);
      uint64_t mask = (uint64_t)0U - bit;
      uint32_t len34 = (uint32_t)12U;
      for (uint32_t i = (uint32_t)0U; i < len34; i++)
      {
        uint64_t dummy = mask & (q[i] ^ rF[i]);
        q[i] = q[i] ^ dummy;
        rF[i] = rF[i] ^ dummy;
      }
      point_add_p256(q, rF, rF, buff);
      point_double_p256(q, q, buff);
      uint64_t mask0 = (uint64_t)0U - bit;
      uint32_t len3 = (uint32_t)12U;
      for (uint32_t i = (uint32_t)0U; i < len3; i++)
      {
        uint64_t dummy = mask0 & (q[i] ^ rF[i]);
        q[i] = q[i] ^ dummy;
        rF[i] = rF[i] ^ dummy;
      }
    }
    norm(Spec_ECC_Curves_P256, q, rF, buff);
    uint32_t len23 = (uint32_t)4U;
    uint32_t start = len23 * (uint32_t)2U;
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
  uint32_t len1 = (uint32_t)4U;
  uint32_t scalarLen = (uint32_t)32U;
  uint64_t *resultBufferX = rF;
  uint64_t *resultBufferY = rF + len1;
  uint8_t *resultX = result;
  uint8_t *resultY = result + scalarLen;
  uint32_t len2 = (uint32_t)4U;
  uint32_t lenByTwo1 = len2 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo1; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = resultBufferX[i];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i] = right;
    resultBufferX[lenRight] = left;
  }
  uint32_t len23 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len23; i++)
  {
    store64_be(resultX + i * (uint32_t)8U, resultBufferX[i]);
  }
  uint32_t len24 = (uint32_t)4U;
  uint32_t lenByTwo2 = len24 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo2; i++)
  {
    uint32_t lenRight = (uint32_t)4U - (uint32_t)1U - i;
    uint64_t left = resultBufferY[i];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i] = right;
    resultBufferY[lenRight] = left;
  }
  uint32_t len25 = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < len25; i++)
  {
    store64_be(resultY + i * (uint32_t)8U, resultBufferY[i]);
  }
  bool flag0 = flag;
  return (uint64_t)flag0;
}

uint64_t Hacl_P256_ecp384dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t rF[(uint32_t)3U * len];
  memset(rF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t pkF[(uint32_t)3U * len];
  memset(pkF, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint32_t len10 = (uint32_t)6U;
  uint32_t coordLen = (uint32_t)48U;
  uint8_t *pointScalarX = pubKey;
  uint8_t *pointScalarY = pubKey + coordLen;
  uint64_t *pointX = pkF;
  uint64_t *pointY = pkF + len10;
  uint64_t *pointZ = pkF + (uint32_t)2U * len10;
  uint32_t len20 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len20; i++)
  {
    uint64_t *os = pointX;
    uint8_t *bj = pointScalarX + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint32_t len30 = (uint32_t)6U;
  uint32_t lenByTwo = len30 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i;
    uint64_t left = pointX[i];
    uint64_t right = pointX[lenRight];
    pointX[i] = right;
    pointX[lenRight] = left;
  }
  uint32_t len21 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len21; i++)
  {
    uint64_t *os = pointY;
    uint8_t *bj = pointScalarY + i * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint32_t len31 = (uint32_t)6U;
  uint32_t lenByTwo0 = len31 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo0; i++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i;
    uint64_t left = pointY[i];
    uint64_t right = pointY[lenRight];
    pointY[i] = right;
    pointY[lenRight] = left;
  }
  pointZ[0U] = (uint64_t)1U;
  uint32_t len22 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)1U; i < len22; i++)
  {
    pointZ[i] = (uint64_t)0U;
  }
  uint32_t len11 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len11);
  uint64_t tempBuffer[(uint32_t)20U * len11];
  memset(tempBuffer, 0U, (uint32_t)20U * len11 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint(Spec_ECC_Curves_P384, pkF, tempBuffer);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len2 = (uint32_t)6U;
    uint64_t *q = tempBuffer;
    uint64_t *buff = tempBuffer + (uint32_t)3U * len2;
    uint32_t len32 = (uint32_t)6U;
    uint64_t *x = q;
    uint64_t *y = q + len32;
    uint64_t *z = q + (uint32_t)2U * len32;
    uint32_t len40 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len40; i++)
    {
      x[i] = (uint64_t)0U;
    }
    uint32_t len41 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len41; i++)
    {
      y[i] = (uint64_t)0U;
    }
    uint32_t len42 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len42; i++)
    {
      z[i] = (uint64_t)0U;
    }
    uint32_t len33 = (uint32_t)6U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len33;
    uint64_t *p_z = pkF + (uint32_t)2U * len33;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len33;
    uint64_t *r_z = rF + (uint32_t)2U * len33;
    uint32_t len4 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len4);
    uint64_t multBuffer[(uint32_t)2U * len4];
    memset(multBuffer, 0U, (uint32_t)2U * len4 * sizeof (uint64_t));
    uint32_t len50 = (uint32_t)6U;
    uint64_t *oToZero0 = multBuffer;
    uint64_t *oToCopy0 = multBuffer + len50;
    memcpy(oToCopy0, p_x, len50 * sizeof (uint64_t));
    uint32_t len6 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len6; i++)
    {
      oToZero0[i] = (uint64_t)0U;
    }
    reduction(Spec_ECC_Curves_P384, multBuffer, r_x);
    uint32_t len43 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len43);
    uint64_t multBuffer0[(uint32_t)2U * len43];
    memset(multBuffer0, 0U, (uint32_t)2U * len43 * sizeof (uint64_t));
    uint32_t len51 = (uint32_t)6U;
    uint64_t *oToZero1 = multBuffer0;
    uint64_t *oToCopy1 = multBuffer0 + len51;
    memcpy(oToCopy1, p_y, len51 * sizeof (uint64_t));
    uint32_t len60 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len60; i++)
    {
      oToZero1[i] = (uint64_t)0U;
    }
    reduction(Spec_ECC_Curves_P384, multBuffer0, r_y);
    uint32_t len44 = (uint32_t)6U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len44);
    uint64_t multBuffer1[(uint32_t)2U * len44];
    memset(multBuffer1, 0U, (uint32_t)2U * len44 * sizeof (uint64_t));
    uint32_t len5 = (uint32_t)6U;
    uint64_t *oToZero = multBuffer1;
    uint64_t *oToCopy = multBuffer1 + len5;
    memcpy(oToCopy, p_z, len5 * sizeof (uint64_t));
    uint32_t len61 = (uint32_t)6U;
    for (uint32_t i = (uint32_t)0U; i < len61; i++)
    {
      oToZero[i] = (uint64_t)0U;
    }
    reduction(Spec_ECC_Curves_P384, multBuffer1, r_z);
    uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
    for (uint32_t i0 = (uint32_t)0U; i0 < cycleLoop; i0++)
    {
      uint32_t bit0 = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384) - (uint32_t)1U - i0;
      uint64_t
      bit =
        (uint64_t)(scalar[(uint32_t)6U
        * (uint32_t)8U
        - (uint32_t)1U
        - bit0 / (uint32_t)8U]
        >> bit0 % (uint32_t)8U
        & (uint8_t)1U);
      uint64_t mask = (uint64_t)0U - bit;
      uint32_t len34 = (uint32_t)18U;
      for (uint32_t i = (uint32_t)0U; i < len34; i++)
      {
        uint64_t dummy = mask & (q[i] ^ rF[i]);
        q[i] = q[i] ^ dummy;
        rF[i] = rF[i] ^ dummy;
      }
      point_add_p384(q, rF, rF, buff);
      point_double_p384(q, q, buff);
      uint64_t mask0 = (uint64_t)0U - bit;
      uint32_t len3 = (uint32_t)18U;
      for (uint32_t i = (uint32_t)0U; i < len3; i++)
      {
        uint64_t dummy = mask0 & (q[i] ^ rF[i]);
        q[i] = q[i] ^ dummy;
        rF[i] = rF[i] ^ dummy;
      }
    }
    norm(Spec_ECC_Curves_P384, q, rF, buff);
    uint32_t len23 = (uint32_t)6U;
    uint32_t start = len23 * (uint32_t)2U;
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
  uint32_t len1 = (uint32_t)6U;
  uint32_t scalarLen = (uint32_t)48U;
  uint64_t *resultBufferX = rF;
  uint64_t *resultBufferY = rF + len1;
  uint8_t *resultX = result;
  uint8_t *resultY = result + scalarLen;
  uint32_t len2 = (uint32_t)6U;
  uint32_t lenByTwo1 = len2 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo1; i++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i;
    uint64_t left = resultBufferX[i];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i] = right;
    resultBufferX[lenRight] = left;
  }
  uint32_t len23 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len23; i++)
  {
    store64_be(resultX + i * (uint32_t)8U, resultBufferX[i]);
  }
  uint32_t len24 = (uint32_t)6U;
  uint32_t lenByTwo2 = len24 >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo2; i++)
  {
    uint32_t lenRight = (uint32_t)6U - (uint32_t)1U - i;
    uint64_t left = resultBufferY[i];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i] = right;
    resultBufferY[lenRight] = left;
  }
  uint32_t len25 = (uint32_t)6U;
  for (uint32_t i = (uint32_t)0U; i < len25; i++)
  {
    store64_be(resultY + i * (uint32_t)8U, resultBufferY[i]);
  }
  bool flag0 = flag;
  return (uint64_t)flag0;
}

