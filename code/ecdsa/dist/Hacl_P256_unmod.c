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

static inline void
cmovznz4(Spec_ECC_Curves_curve c, uint64_t cin, uint64_t *x, uint64_t *y, uint64_t *r)
{
  uint64_t mask = ~FStar_UInt64_eq_mask(cin, (uint64_t)0U);
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
    uint64_t x_i = x[i];
    uint64_t y_i = y[i];
    uint64_t r_i = (y_i & mask) | (x_i & ~mask);
    r[i] = r_i;
  }
}

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

static inline void
felem_add(Spec_ECC_Curves_curve c, uint64_t *arg1, uint64_t *arg2, uint64_t *out)
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
  uint64_t c10 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg2[(uint32_t)4U * i];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg2[(uint32_t)4U * i + (uint32_t)1U];
    c10 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c10,
        t10,
        t21,
        out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg2[(uint32_t)4U * i + (uint32_t)2U];
    c10 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c10,
        t11,
        t22,
        out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg2[(uint32_t)4U * i + (uint32_t)3U];
    c10 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c10,
        t12,
        t2,
        out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg2[i];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, out + i);
  }
  uint64_t t = c10;
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
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
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
          uint64_t t1 = out[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = out[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          uint64_t t1 = out[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = out[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
      t,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4(c, carry, tempBuffer, out, out);
}

static inline void felem_double(Spec_ECC_Curves_curve c, uint64_t *arg1, uint64_t *out)
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
  uint64_t c10 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg1[(uint32_t)4U * i];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    c10 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c10,
        t10,
        t21,
        out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    c10 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c10,
        t11,
        t22,
        out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    c10 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c10,
        t12,
        t2,
        out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg1[i];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, out + i);
  }
  uint64_t t = c10;
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
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
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
          uint64_t t1 = out[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = out[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          uint64_t t1 = out[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = out[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = out[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = out[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = out[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
      t,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4(c, carry, tempBuffer, out, out);
}

static inline void
felem_sub(Spec_ECC_Curves_curve c, uint64_t *arg1, uint64_t *arg2, uint64_t *out)
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
  uint64_t c10 = (uint64_t)0U;
  uint32_t k0 = len0 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = arg1[(uint32_t)4U * i];
    uint64_t t20 = arg2[(uint32_t)4U * i];
    c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t20, out + (uint32_t)4U * i);
    uint64_t t10 = arg1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = arg2[(uint32_t)4U * i + (uint32_t)1U];
    c10 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
        t10,
        t21,
        out + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = arg1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = arg2[(uint32_t)4U * i + (uint32_t)2U];
    c10 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
        t11,
        t22,
        out + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = arg1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = arg2[(uint32_t)4U * i + (uint32_t)3U];
    c10 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c10,
        t12,
        t2,
        out + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < len0; i++)
  {
    uint64_t t1 = arg1[i];
    uint64_t t2 = arg2[i];
    c10 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c10, t1, t2, out + i);
  }
  uint64_t t = c10;
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t11 = out[(uint32_t)4U * i];
          uint64_t t210 = b[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t210, out + (uint32_t)4U * i);
          uint64_t t110 = out[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t211 = b[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t110,
              t211,
              out + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t111 = out[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t212 = b[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t111,
              t212,
              out + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t112 = out[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t112,
              t21,
              out + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < (uint32_t)6U; i++)
        {
          uint64_t t11 = out[i];
          uint64_t t21 = b[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t21, out + i);
        }
        uint64_t r0 = c1;
        r = r0;
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
        uint64_t b[len];
        memset(b, 0U, len * sizeof (uint64_t));
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
          uint64_t t1 = p[(uint32_t)4U * i];
          uint64_t t20 = out[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, b + (uint32_t)4U * i);
          uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = out[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              b + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = out[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              b + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = out[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              b + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len1; i++)
        {
          uint64_t t1 = p[i];
          uint64_t t2 = out[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, b + i);
        }
        uint64_t carry = c1;
        uint64_t mask = ~((uint64_t)0U - t);
        cmovznz4(c, mask, b, out, out);
        uint64_t r0 = carry;
        r = r0;
      }
  }
}

static inline void
montgomery_multiplication_round_w_k0(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *t2)
{
  uint64_t t1 = t[0U];
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
        uint64_t h020 = (uint64_t)(res0 >> (uint32_t)64U);
        o0[0U] = l00;
        temp = h020;
        uint64_t h0 = temp;
        uint128_t res = (uint128_t)f1 * t1;
        uint64_t l01 = (uint64_t)res;
        uint64_t h021 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l01;
        temp = h021;
        uint64_t l = o1[0U];
        uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h0, o1);
        uint64_t h = temp;
        o2[0U] = h + c1;
        uint128_t res1 = (uint128_t)f3 * t1;
        uint64_t l0 = (uint64_t)res1;
        uint64_t h02 = (uint64_t)(res1 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h02;
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
        uint64_t bBuffer = t1;
        uint64_t *partResult = t2;
        uint32_t resLen = len + (uint32_t)1U;
        memset(partResult, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____0 = (&bBuffer)[0U];
          uint64_t *res_ = partResult;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)1U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)2U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)3U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[i], uu____0, res_ + i);
          }
          uint64_t r = c1;
          partResult[len + (uint32_t)0U] = r;
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
        uint64_t bBuffer = t1;
        uint64_t *partResult = t2;
        uint32_t resLen = len + (uint32_t)1U;
        memset(partResult, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____1 = (&bBuffer)[0U];
          uint64_t *res_ = partResult;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)1U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)2U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)3U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[i], uu____1, res_ + i);
          }
          uint64_t r = c1;
          partResult[len + (uint32_t)0U] = r;
        }
      }
  }
}

static inline void
montgomery_multiplication_round_k0(
  Spec_ECC_Curves_curve c,
  uint64_t k0,
  uint64_t *t,
  uint64_t *t2
)
{
  uint64_t t1 = t[0U];
  uint64_t y = (uint64_t)0U;
  uint64_t temp = (uint64_t)0U;
  uint128_t res0 = (uint128_t)t1 * k0;
  uint64_t l00 = (uint64_t)res0;
  uint64_t h01 = (uint64_t)(res0 >> (uint32_t)64U);
  y = l00;
  temp = h01;
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
        uint64_t h020 = (uint64_t)(res1 >> (uint32_t)64U);
        o0[0U] = l01;
        temp1 = h020;
        uint64_t h2 = temp1;
        uint128_t res = (uint128_t)f1 * y_;
        uint64_t l02 = (uint64_t)res;
        uint64_t h021 = (uint64_t)(res >> (uint32_t)64U);
        o1[0U] = l02;
        temp1 = h021;
        uint64_t l = o1[0U];
        uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h2, o1);
        uint64_t h3 = temp1;
        o2[0U] = h3 + c1;
        uint128_t res2 = (uint128_t)f3 * y_;
        uint64_t l0 = (uint64_t)res2;
        uint64_t h02 = (uint64_t)(res2 >> (uint32_t)64U);
        o3[0U] = l0;
        o4[0U] = h02;
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
        uint64_t bBuffer = y_;
        uint64_t *partResult = t2;
        uint32_t resLen = len + (uint32_t)1U;
        memset(partResult, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____0 = (&bBuffer)[0U];
          uint64_t *res_ = partResult;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)1U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)2U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)3U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[i], uu____0, res_ + i);
          }
          uint64_t r = c1;
          partResult[len + (uint32_t)0U] = r;
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
        uint64_t bBuffer = y_;
        uint64_t *partResult = t2;
        uint32_t resLen = len + (uint32_t)1U;
        memset(partResult, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____1 = (&bBuffer)[0U];
          uint64_t *res_ = partResult;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)1U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)2U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                p[(uint32_t)4U * i + (uint32_t)3U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, p[i], uu____1, res_ + i);
          }
          uint64_t r = c1;
          partResult[len + (uint32_t)0U] = r;
        }
      }
  }
}

static inline void
montgomery_multiplication_reduction_dh(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *result)
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
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
    uint64_t sw0;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw0 = (uint64_t)0xffffffffffffffffU;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw0 = (uint64_t)0xffffffffU;
          break;
        }
      default:
        {
          sw0 = KRML_EABORT(uint64_t, "");
        }
    }
    bool r = sw0 == (uint64_t)0xffffffffffffffffU;
    if (r)
    {
      montgomery_multiplication_round_w_k0(c, t, t2);
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
                  sw = (uint64_t)0xffffffffffffffffU;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw = (uint64_t)0xffffffffU;
                  break;
                }
              default:
                {
                  sw = KRML_EABORT(uint64_t, "");
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
      montgomery_multiplication_round_k0(c, k0, t, t2);
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
    uint32_t len2 = sw1 * (uint32_t)2U;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len2 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t10,
          t211,
          t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t11,
          t212,
          t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len2; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
    uint32_t len20 = sw * (uint32_t)2U - (uint32_t)1U;
    for (uint32_t i = (uint32_t)0U; i < len20; i++)
    {
      uint64_t elem = t2[(uint32_t)1U + i];
      t[i] = elem;
    }
    t[len20] = carry;
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
  uint64_t cin = t[len1];
  uint64_t *x_ = t;
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
  KRML_CHECK_SIZE(sizeof (uint64_t), len2);
  uint64_t tempBuffer[len2];
  memset(tempBuffer, 0U, len2 * sizeof (uint64_t));
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len3 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len3; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len3 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len3; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
  cmovznz4(c, carry, tempBuffer, x_, result);
}

static inline void
montgomery_multiplication_buffer_by_one_dh(
  Spec_ECC_Curves_curve c,
  uint64_t *a,
  uint64_t *result
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *t_low = t;
  memcpy(t_low, a, len * sizeof (uint64_t));
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t sw0;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw0 = (uint64_t)0xffffffffffffffffU;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw0 = (uint64_t)0xffffffffU;
          break;
        }
      default:
        {
          sw0 = KRML_EABORT(uint64_t, "");
        }
    }
    bool r = sw0 == (uint64_t)0xffffffffffffffffU;
    if (r)
    {
      montgomery_multiplication_round_w_k0(c, t, t2);
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
                  sw = (uint64_t)0xffffffffffffffffU;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw = (uint64_t)0xffffffffU;
                  break;
                }
              default:
                {
                  sw = KRML_EABORT(uint64_t, "");
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
      montgomery_multiplication_round_k0(c, k0, t, t2);
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
    uint32_t len3 = sw1 * (uint32_t)2U;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len3 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t10,
          t211,
          t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t11,
          t212,
          t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len3; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
  uint64_t cin = t[len2];
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
        uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
  cmovznz4(c, carry, tempBuffer, x_, result);
}

static inline void
montgomery_multiplication_buffer_dh(
  Spec_ECC_Curves_curve c,
  uint64_t *a,
  uint64_t *b,
  uint64_t *result
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
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
  uint32_t resLen = len1 + len1;
  memset(t, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = t + i0;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      c1 = mul_carry_add_u64_st(c1, a[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
      c1 =
        mul_carry_add_u64_st(c1,
          a[(uint32_t)4U * i + (uint32_t)1U],
          uu____0,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c1 =
        mul_carry_add_u64_st(c1,
          a[(uint32_t)4U * i + (uint32_t)2U],
          uu____0,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c1 =
        mul_carry_add_u64_st(c1,
          a[(uint32_t)4U * i + (uint32_t)3U],
          uu____0,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len1; i++)
    {
      c1 = mul_carry_add_u64_st(c1, a[i], uu____0, res_ + i);
    }
    uint64_t r = c1;
    t[len1 + i0] = r;
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t sw0;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw0 = (uint64_t)0xffffffffffffffffU;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw0 = (uint64_t)0xffffffffU;
          break;
        }
      default:
        {
          sw0 = KRML_EABORT(uint64_t, "");
        }
    }
    bool r = sw0 == (uint64_t)0xffffffffffffffffU;
    if (r)
    {
      montgomery_multiplication_round_w_k0(c, t, t2);
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
                  sw = (uint64_t)0xffffffffffffffffU;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw = (uint64_t)0xffffffffU;
                  break;
                }
              default:
                {
                  sw = KRML_EABORT(uint64_t, "");
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
      montgomery_multiplication_round_k0(c, k0, t, t2);
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
    uint32_t len3 = sw1 * (uint32_t)2U;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len3 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t10,
          t211,
          t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t11,
          t212,
          t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len3; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
  uint64_t cin = t[len2];
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
        uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
  cmovznz4(c, carry, tempBuffer, x_, result);
}

static inline void
montgomery_square_buffer_dh(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t t[(uint32_t)2U * len];
  memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
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
  uint32_t resLen = len1 + len1;
  memset(t, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t *uu____0 = a;
    uint64_t uu____1 = a[i0];
    uint64_t *res_ = t + i0;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = i0 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      c1 = mul_carry_add_u64_st(c1, uu____0[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
      c1 =
        mul_carry_add_u64_st(c1,
          uu____0[(uint32_t)4U * i + (uint32_t)1U],
          uu____1,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c1 =
        mul_carry_add_u64_st(c1,
          uu____0[(uint32_t)4U * i + (uint32_t)2U],
          uu____1,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c1 =
        mul_carry_add_u64_st(c1,
          uu____0[(uint32_t)4U * i + (uint32_t)3U],
          uu____1,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < i0; i++)
    {
      c1 = mul_carry_add_u64_st(c1, uu____0[i], uu____1, res_ + i);
    }
    uint64_t r = c1;
    t[i0 + i0] = r;
  }
  uint64_t c10 = (uint64_t)0U;
  uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = t[(uint32_t)4U * i];
    uint64_t t20 = t[(uint32_t)4U * i];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, t + (uint32_t)4U * i);
    uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t[(uint32_t)4U * i + (uint32_t)1U];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t10, t21, t + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t[(uint32_t)4U * i + (uint32_t)2U];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t11, t22, t + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t[(uint32_t)4U * i + (uint32_t)3U];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < resLen; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = t[i];
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, t + i);
  }
  uint64_t uu____2 = c10;
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  uint64_t tmp[resLen];
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint128_t a2 = (uint128_t)a[i] * a[i];
    tmp[(uint32_t)2U * i] = (uint64_t)a2;
    tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
  }
  uint64_t c11 = (uint64_t)0U;
  uint32_t k1 = resLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = t[(uint32_t)4U * i];
    uint64_t t20 = tmp[(uint32_t)4U * i];
    c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t1, t20, t + (uint32_t)4U * i);
    uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
    c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t10, t21, t + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
    c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t11, t22, t + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
    c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k1; i < resLen; i++)
  {
    uint64_t t1 = t[i];
    uint64_t t2 = tmp[i];
    c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t1, t2, t + i);
  }
  uint64_t uu____3 = c11;
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
    uint64_t t2[(uint32_t)2U * len2];
    memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
    uint64_t sw0;
    switch (c)
    {
      case Spec_ECC_Curves_P256:
        {
          sw0 = (uint64_t)0xffffffffffffffffU;
          break;
        }
      case Spec_ECC_Curves_P384:
        {
          sw0 = (uint64_t)0xffffffffU;
          break;
        }
      default:
        {
          sw0 = KRML_EABORT(uint64_t, "");
        }
    }
    bool r = sw0 == (uint64_t)0xffffffffffffffffU;
    if (r)
    {
      montgomery_multiplication_round_w_k0(c, t, t2);
    }
    else
    {
      uint64_t k00;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            k00 = (uint64_t)1U;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            k00 = (uint64_t)4294967297U;
            break;
          }
        case Spec_ECC_Curves_Default:
          {
            uint64_t sw;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  sw = (uint64_t)0xffffffffffffffffU;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw = (uint64_t)0xffffffffU;
                  break;
                }
              default:
                {
                  sw = KRML_EABORT(uint64_t, "");
                }
            }
            k00 = mod_inv_u64(sw);
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
      montgomery_multiplication_round_k0(c, k00, t, t2);
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
    uint32_t len3 = sw1 * (uint32_t)2U;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len3 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t210 = t2[(uint32_t)4U * i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t10,
          t211,
          t2 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
      c1 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c1,
          t11,
          t212,
          t2 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t21, t2 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len3; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t21 = t2[i];
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
  uint64_t cin = t[len2];
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
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
        uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x_[(uint32_t)4U * i];
          uint64_t t20 = p[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
          uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len4; i++)
        {
          uint64_t t1 = x_[i];
          uint64_t t2 = p[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
  cmovznz4(c, carry, tempBuffer, x_, result);
}

static inline void fsquarePowN_dh(Spec_ECC_Curves_curve c, uint32_t n, uint64_t *a)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < n; i0++)
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
    uint64_t t[(uint32_t)2U * len];
    memset(t, 0U, (uint32_t)2U * len * sizeof (uint64_t));
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
    uint32_t resLen = len1 + len1;
    memset(t, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len1; i1++)
    {
      uint64_t *uu____0 = a;
      uint64_t uu____1 = a[i1];
      uint64_t *res_ = t + i1;
      uint64_t c1 = (uint64_t)0U;
      uint32_t k = i1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c1 = mul_carry_add_u64_st(c1, uu____0[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
        c1 =
          mul_carry_add_u64_st(c1,
            uu____0[(uint32_t)4U * i + (uint32_t)1U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c1 =
          mul_carry_add_u64_st(c1,
            uu____0[(uint32_t)4U * i + (uint32_t)2U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c1 =
          mul_carry_add_u64_st(c1,
            uu____0[(uint32_t)4U * i + (uint32_t)3U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i1; i++)
      {
        c1 = mul_carry_add_u64_st(c1, uu____0[i], uu____1, res_ + i);
      }
      uint64_t r = c1;
      t[i1 + i1] = r;
    }
    uint64_t c10 = (uint64_t)0U;
    uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t20 = t[(uint32_t)4U * i];
      c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, t + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = t[(uint32_t)4U * i + (uint32_t)1U];
      c10 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c10,
          t10,
          t21,
          t + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = t[(uint32_t)4U * i + (uint32_t)2U];
      c10 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c10,
          t11,
          t22,
          t + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = t[(uint32_t)4U * i + (uint32_t)3U];
      c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < resLen; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t2 = t[i];
      c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, t + i);
    }
    uint64_t uu____2 = c10;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
    uint64_t tmp[resLen];
    memset(tmp, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint128_t a2 = (uint128_t)a[i] * a[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c11 = (uint64_t)0U;
    uint32_t k1 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t[(uint32_t)4U * i];
      uint64_t t20 = tmp[(uint32_t)4U * i];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t1, t20, t + (uint32_t)4U * i);
      uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
      c11 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c11,
          t10,
          t21,
          t + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
      c11 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c11,
          t11,
          t22,
          t + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t12, t2, t + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < resLen; i++)
    {
      uint64_t t1 = t[i];
      uint64_t t2 = tmp[i];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t1, t2, t + i);
    }
    uint64_t uu____3 = c11;
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
    for (uint32_t i1 = (uint32_t)0U; i1 < len10; i1++)
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
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len2);
      uint64_t t2[(uint32_t)2U * len2];
      memset(t2, 0U, (uint32_t)2U * len2 * sizeof (uint64_t));
      uint64_t sw0;
      switch (c)
      {
        case Spec_ECC_Curves_P256:
          {
            sw0 = (uint64_t)0xffffffffffffffffU;
            break;
          }
        case Spec_ECC_Curves_P384:
          {
            sw0 = (uint64_t)0xffffffffU;
            break;
          }
        default:
          {
            sw0 = KRML_EABORT(uint64_t, "");
          }
      }
      bool r = sw0 == (uint64_t)0xffffffffffffffffU;
      if (r)
      {
        montgomery_multiplication_round_w_k0(c, t, t2);
      }
      else
      {
        uint64_t k00;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              k00 = (uint64_t)1U;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              k00 = (uint64_t)4294967297U;
              break;
            }
          case Spec_ECC_Curves_Default:
            {
              uint64_t sw;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    sw = (uint64_t)0xffffffffffffffffU;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    sw = (uint64_t)0xffffffffU;
                    break;
                  }
                default:
                  {
                    sw = KRML_EABORT(uint64_t, "");
                  }
              }
              k00 = mod_inv_u64(sw);
              break;
            }
          default:
            {
              KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        montgomery_multiplication_round_k0(c, k00, t, t2);
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
      uint32_t len3 = sw1 * (uint32_t)2U;
      uint64_t c1 = (uint64_t)0U;
      uint32_t k = len3 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t10,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t11,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t12,
            t21,
            t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len3; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
    uint64_t cin = t[len2];
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
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            uint64_t t1 = x_[(uint32_t)4U * i];
            uint64_t t20 = p[(uint32_t)4U * i];
            c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
            uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
            c1 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                t10,
                t21,
                tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
            uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
            uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
            c1 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                t11,
                t22,
                tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
            uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
            c1 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                t12,
                t2,
                tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len4; i++)
          {
            uint64_t t1 = x_[i];
            uint64_t t2 = p[i];
            c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            uint64_t t1 = x_[(uint32_t)4U * i];
            uint64_t t20 = p[(uint32_t)4U * i];
            c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tempBuffer + (uint32_t)4U * i);
            uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t t21 = p[(uint32_t)4U * i + (uint32_t)1U];
            c1 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                t10,
                t21,
                tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
            uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
            uint64_t t22 = p[(uint32_t)4U * i + (uint32_t)2U];
            c1 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                t11,
                t22,
                tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
            uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t t2 = p[(uint32_t)4U * i + (uint32_t)3U];
            c1 =
              Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                t12,
                t2,
                tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len4; i++)
          {
            uint64_t t1 = x_[i];
            uint64_t t2 = p[i];
            c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
    cmovznz4(c, carry, tempBuffer, x_, a);
  }
}

static inline void cswap(Spec_ECC_Curves_curve c, uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
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
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static inline void
montgomery_ladder_power(
  Spec_ECC_Curves_curve c,
  Hacl_Spec_MontgomeryMultiplication_mode m,
  uint64_t *a,
  const uint8_t *scalar,
  uint64_t *result
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
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t p[len];
  memset(p, 0U, len * sizeof (uint64_t));
  switch (m)
  {
    case Hacl_Spec_MontgomeryMultiplication_DH:
      {
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              p[0U] = (uint64_t)1U;
              p[1U] = (uint64_t)18446744069414584320U;
              p[2U] = (uint64_t)18446744073709551615U;
              p[3U] = (uint64_t)4294967294U;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              p[0U] = (uint64_t)18446744069414584321U;
              p[1U] = (uint64_t)4294967295U;
              p[2U] = (uint64_t)1U;
              p[3U] = (uint64_t)0U;
              p[4U] = (uint64_t)0U;
              p[5U] = (uint64_t)0U;
              break;
            }
          default:
            {
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
                p[i] = (uint64_t)0U;
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
              KRML_CHECK_SIZE(sizeof (uint64_t), len10);
              uint64_t tempBuffer[len10];
              memset(tempBuffer, 0U, len10 * sizeof (uint64_t));
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
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len2 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      uint64_t t1 = p[(uint32_t)4U * i];
                      uint64_t t20 = p1[(uint32_t)4U * i];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t1,
                          t20,
                          tempBuffer + (uint32_t)4U * i);
                      uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
                      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t10,
                          t21,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                      uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
                      uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t11,
                          t22,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                      uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
                      uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t12,
                          t2,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len2; i++)
                    {
                      uint64_t t1 = p[i];
                      uint64_t t2 = p1[i];
                      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
                    }
                    uint64_t r = c1;
                    carry0 = r;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    uint64_t
                    p1[6U] =
                      {
                        (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U,
                        (uint64_t)0xfffffffffffffffeU, (uint64_t)0xffffffffffffffffU,
                        (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
                      };
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
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len2 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      uint64_t t1 = p[(uint32_t)4U * i];
                      uint64_t t20 = p1[(uint32_t)4U * i];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t1,
                          t20,
                          tempBuffer + (uint32_t)4U * i);
                      uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
                      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t10,
                          t21,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                      uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
                      uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t11,
                          t22,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                      uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
                      uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t12,
                          t2,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len2; i++)
                    {
                      uint64_t t1 = p[i];
                      uint64_t t2 = p1[i];
                      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
                  (uint64_t)1U,
                  (uint64_t)0U,
                  &tempBufferForSubborrow);
              cmovznz4(c, carry, tempBuffer, p, p);
            }
        }
        break;
      }
    case Hacl_Spec_MontgomeryMultiplication_DSA:
      {
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              p[0U] = (uint64_t)884452912994769583U;
              p[1U] = (uint64_t)4834901526196019579U;
              p[2U] = (uint64_t)0U;
              p[3U] = (uint64_t)4294967295U;
              break;
            }
          default:
            {
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
                p[i] = (uint64_t)0U;
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
              KRML_CHECK_SIZE(sizeof (uint64_t), len10);
              uint64_t tempBuffer[len10];
              memset(tempBuffer, 0U, len10 * sizeof (uint64_t));
              uint64_t tempBufferForSubborrow = (uint64_t)0U;
              uint64_t carry0;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    uint64_t
                    p1[4U] =
                      {
                        (uint64_t)17562291160714782033U,
                        (uint64_t)13611842547513532036U,
                        (uint64_t)18446744073709551615U,
                        (uint64_t)18446744069414584320U
                      };
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
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len2 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      uint64_t t1 = p[(uint32_t)4U * i];
                      uint64_t t20 = p1[(uint32_t)4U * i];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t1,
                          t20,
                          tempBuffer + (uint32_t)4U * i);
                      uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
                      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t10,
                          t21,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                      uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
                      uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t11,
                          t22,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                      uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
                      uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t12,
                          t2,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len2; i++)
                    {
                      uint64_t t1 = p[i];
                      uint64_t t2 = p1[i];
                      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
                    }
                    uint64_t r = c1;
                    carry0 = r;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    uint64_t
                    p1[6U] =
                      {
                        (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
                        (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
                        (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
                      };
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
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len2 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      uint64_t t1 = p[(uint32_t)4U * i];
                      uint64_t t20 = p1[(uint32_t)4U * i];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t1,
                          t20,
                          tempBuffer + (uint32_t)4U * i);
                      uint64_t t10 = p[(uint32_t)4U * i + (uint32_t)1U];
                      uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t10,
                          t21,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                      uint64_t t11 = p[(uint32_t)4U * i + (uint32_t)2U];
                      uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t11,
                          t22,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                      uint64_t t12 = p[(uint32_t)4U * i + (uint32_t)3U];
                      uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                      c1 =
                        Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                          t12,
                          t2,
                          tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len2; i++)
                    {
                      uint64_t t1 = p[i];
                      uint64_t t2 = p1[i];
                      c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
                  (uint64_t)1U,
                  (uint64_t)0U,
                  &tempBufferForSubborrow);
              cmovznz4(c, carry, tempBuffer, p, p);
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
  memcpy(a, result, sw0 * sizeof (uint64_t));
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLen(c);
  for (uint32_t i0 = (uint32_t)0U; i0 < scalarLen; i0++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(c) - (uint32_t)1U - i0;
    uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
    cswap(c, bit, p, a);
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
    uint64_t t[(uint32_t)2U * len1];
    memset(t, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
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
    uint32_t resLen0 = len20 + len20;
    memset(t, 0U, resLen0 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len20; i1++)
    {
      uint64_t uu____0 = a[i1];
      uint64_t *res_ = t + i1;
      uint64_t c1 = (uint64_t)0U;
      uint32_t k = len20 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c1 = mul_carry_add_u64_st(c1, p[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
        c1 =
          mul_carry_add_u64_st(c1,
            p[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c1 =
          mul_carry_add_u64_st(c1,
            p[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c1 =
          mul_carry_add_u64_st(c1,
            p[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len20; i++)
      {
        c1 = mul_carry_add_u64_st(c1, p[i], uu____0, res_ + i);
      }
      uint64_t r = c1;
      t[len20 + i1] = r;
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
    for (uint32_t i1 = (uint32_t)0U; i1 < len21; i1++)
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
      switch (m)
      {
        case Hacl_Spec_MontgomeryMultiplication_DSA:
          {
            uint64_t sw;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  sw = (uint64_t)17562291160714782033U;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw = (uint64_t)17072048233947408755U;
                  break;
                }
              default:
                {
                  sw = KRML_EABORT(uint64_t, "");
                }
            }
            uint64_t k0 = mod_inv_u64(sw);
            uint64_t t1 = t[0U];
            uint64_t y = (uint64_t)0U;
            uint64_t temp = (uint64_t)0U;
            uint128_t res = (uint128_t)t1 * k0;
            uint64_t l0 = (uint64_t)res;
            uint64_t h07 = (uint64_t)(res >> (uint32_t)64U);
            y = l0;
            temp = h07;
            uint64_t y_ = y;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  uint64_t
                  p1[4U] =
                    {
                      (uint64_t)17562291160714782033U,
                      (uint64_t)13611842547513532036U,
                      (uint64_t)18446744073709551615U,
                      (uint64_t)18446744069414584320U
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
                    uint64_t uu____1 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i],
                          uu____1,
                          res_ + (uint32_t)4U * i);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)1U],
                          uu____1,
                          res_ + (uint32_t)4U * i + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)2U],
                          uu____1,
                          res_ + (uint32_t)4U * i + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)3U],
                          uu____1,
                          res_ + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len4; i++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p1[i], uu____1, res_ + i);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  uint64_t
                  p1[6U] =
                    {
                      (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
                      (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
                      (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
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
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i],
                          uu____2,
                          res_ + (uint32_t)4U * i);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)1U],
                          uu____2,
                          res_ + (uint32_t)4U * i + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)2U],
                          uu____2,
                          res_ + (uint32_t)4U * i + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)3U],
                          uu____2,
                          res_ + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len4; i++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p1[i], uu____2, res_ + i);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                  break;
                }
              default:
                {
                  uint64_t
                  p1[4U] =
                    {
                      (uint64_t)17562291160714782033U,
                      (uint64_t)13611842547513532036U,
                      (uint64_t)18446744073709551615U,
                      (uint64_t)18446744069414584320U
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
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i],
                          uu____3,
                          res_ + (uint32_t)4U * i);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)1U],
                          uu____3,
                          res_ + (uint32_t)4U * i + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)2U],
                          uu____3,
                          res_ + (uint32_t)4U * i + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)3U],
                          uu____3,
                          res_ + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len4; i++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p1[i], uu____3, res_ + i);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                }
            }
            break;
          }
        case Hacl_Spec_MontgomeryMultiplication_DH:
          {
            uint64_t sw1;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  sw1 = (uint64_t)0xffffffffffffffffU;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw1 = (uint64_t)0xffffffffU;
                  break;
                }
              default:
                {
                  sw1 = KRML_EABORT(uint64_t, "");
                }
            }
            bool r = sw1 == (uint64_t)0xffffffffffffffffU;
            if (r)
            {
              montgomery_multiplication_round_w_k0(c, t, t2);
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
                          sw = (uint64_t)0xffffffffffffffffU;
                          break;
                        }
                      case Spec_ECC_Curves_P384:
                        {
                          sw = (uint64_t)0xffffffffU;
                          break;
                        }
                      default:
                        {
                          sw = KRML_EABORT(uint64_t, "");
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
              montgomery_multiplication_round_k0(c, k0, t, t2);
            }
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
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
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t10 = t[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t10,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t11,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t12,
            t21,
            t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len4; i++)
      {
        uint64_t t1 = t[i];
        uint64_t t21 = t2[i];
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t[i] = elem;
      }
      t[len40] = carry;
    }
    switch (m)
    {
      case Hacl_Spec_MontgomeryMultiplication_DH:
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
          uint64_t cin = t[len3];
          uint64_t *x_ = t;
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
                p1[4U] =
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
                }
                uint64_t r = c1;
                carry0 = r;
                break;
              }
            case Spec_ECC_Curves_P384:
              {
                uint64_t
                p1[6U] =
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          cmovznz4(c, carry, tempBuffer, x_, a);
          break;
        }
      case Hacl_Spec_MontgomeryMultiplication_DSA:
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
          uint64_t cin = t[len3];
          uint64_t *x_ = t;
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
                p1[4U] =
                  {
                    (uint64_t)17562291160714782033U,
                    (uint64_t)13611842547513532036U,
                    (uint64_t)18446744073709551615U,
                    (uint64_t)18446744069414584320U
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
                }
                uint64_t r = c1;
                carry0 = r;
                break;
              }
            case Spec_ECC_Curves_P384:
              {
                uint64_t
                p1[6U] =
                  {
                    (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
                    (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
                    (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          cmovznz4(c, carry, tempBuffer, x_, a);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
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
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len10);
    uint64_t t0[(uint32_t)2U * len10];
    memset(t0, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
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
    uint32_t resLen1 = len2 + len2;
    memset(t0, 0U, resLen1 * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < len2; i1++)
    {
      uint64_t *uu____4 = p;
      uint64_t uu____5 = p[i1];
      uint64_t *res_ = t0 + i1;
      uint64_t c1 = (uint64_t)0U;
      uint32_t k = i1 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c1 = mul_carry_add_u64_st(c1, uu____4[(uint32_t)4U * i], uu____5, res_ + (uint32_t)4U * i);
        c1 =
          mul_carry_add_u64_st(c1,
            uu____4[(uint32_t)4U * i + (uint32_t)1U],
            uu____5,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c1 =
          mul_carry_add_u64_st(c1,
            uu____4[(uint32_t)4U * i + (uint32_t)2U],
            uu____5,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c1 =
          mul_carry_add_u64_st(c1,
            uu____4[(uint32_t)4U * i + (uint32_t)3U],
            uu____5,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i1; i++)
      {
        c1 = mul_carry_add_u64_st(c1, uu____4[i], uu____5, res_ + i);
      }
      uint64_t r = c1;
      t0[i1 + i1] = r;
    }
    uint64_t c10 = (uint64_t)0U;
    uint32_t k0 = resLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = t0[(uint32_t)4U * i];
      c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = t0[(uint32_t)4U * i + (uint32_t)1U];
      c10 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c10,
          t10,
          t21,
          t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = t0[(uint32_t)4U * i + (uint32_t)2U];
      c10 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c10,
          t11,
          t22,
          t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = t0[(uint32_t)4U * i + (uint32_t)3U];
      c10 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c10,
          t12,
          t2,
          t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < resLen1; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = t0[i];
      c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, t0 + i);
    }
    uint64_t uu____6 = c10;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen1);
    uint64_t tmp[resLen1];
    memset(tmp, 0U, resLen1 * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < len2; i++)
    {
      uint128_t a2 = (uint128_t)p[i] * p[i];
      tmp[(uint32_t)2U * i] = (uint64_t)a2;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
    }
    uint64_t c11 = (uint64_t)0U;
    uint32_t k1 = resLen1 / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
    {
      uint64_t t1 = t0[(uint32_t)4U * i];
      uint64_t t20 = tmp[(uint32_t)4U * i];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t1, t20, t0 + (uint32_t)4U * i);
      uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
      c11 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c11,
          t10,
          t21,
          t0 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
      c11 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c11,
          t11,
          t22,
          t0 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
      c11 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c11,
          t12,
          t2,
          t0 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k1; i < resLen1; i++)
    {
      uint64_t t1 = t0[i];
      uint64_t t2 = tmp[i];
      c11 = Lib_IntTypes_Intrinsics_add_carry_u64(c11, t1, t2, t0 + i);
    }
    uint64_t uu____7 = c11;
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
    for (uint32_t i1 = (uint32_t)0U; i1 < len22; i1++)
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
      switch (m)
      {
        case Hacl_Spec_MontgomeryMultiplication_DSA:
          {
            uint64_t sw;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  sw = (uint64_t)17562291160714782033U;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw = (uint64_t)17072048233947408755U;
                  break;
                }
              default:
                {
                  sw = KRML_EABORT(uint64_t, "");
                }
            }
            uint64_t k00 = mod_inv_u64(sw);
            uint64_t t1 = t0[0U];
            uint64_t y = (uint64_t)0U;
            uint64_t temp = (uint64_t)0U;
            uint128_t res = (uint128_t)t1 * k00;
            uint64_t l0 = (uint64_t)res;
            uint64_t h07 = (uint64_t)(res >> (uint32_t)64U);
            y = l0;
            temp = h07;
            uint64_t y_ = y;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  uint64_t
                  p1[4U] =
                    {
                      (uint64_t)17562291160714782033U,
                      (uint64_t)13611842547513532036U,
                      (uint64_t)18446744073709551615U,
                      (uint64_t)18446744069414584320U
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
                    uint64_t uu____8 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i],
                          uu____8,
                          res_ + (uint32_t)4U * i);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)1U],
                          uu____8,
                          res_ + (uint32_t)4U * i + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)2U],
                          uu____8,
                          res_ + (uint32_t)4U * i + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)3U],
                          uu____8,
                          res_ + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len4; i++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p1[i], uu____8, res_ + i);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  uint64_t
                  p1[6U] =
                    {
                      (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
                      (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
                      (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
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
                    uint64_t uu____9 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i],
                          uu____9,
                          res_ + (uint32_t)4U * i);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)1U],
                          uu____9,
                          res_ + (uint32_t)4U * i + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)2U],
                          uu____9,
                          res_ + (uint32_t)4U * i + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)3U],
                          uu____9,
                          res_ + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len4; i++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p1[i], uu____9, res_ + i);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                  break;
                }
              default:
                {
                  uint64_t
                  p1[4U] =
                    {
                      (uint64_t)17562291160714782033U,
                      (uint64_t)13611842547513532036U,
                      (uint64_t)18446744073709551615U,
                      (uint64_t)18446744069414584320U
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
                    uint64_t uu____10 = (&bBuffer)[0U];
                    uint64_t *res_ = partResult;
                    uint64_t c1 = (uint64_t)0U;
                    uint32_t k = len4 / (uint32_t)4U * (uint32_t)4U;
                    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                    {
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i],
                          uu____10,
                          res_ + (uint32_t)4U * i);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)1U],
                          uu____10,
                          res_ + (uint32_t)4U * i + (uint32_t)1U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)2U],
                          uu____10,
                          res_ + (uint32_t)4U * i + (uint32_t)2U);
                      c1 =
                        mul_carry_add_u64_st(c1,
                          p1[(uint32_t)4U * i + (uint32_t)3U],
                          uu____10,
                          res_ + (uint32_t)4U * i + (uint32_t)3U);
                    }
                    for (uint32_t i = k; i < len4; i++)
                    {
                      c1 = mul_carry_add_u64_st(c1, p1[i], uu____10, res_ + i);
                    }
                    uint64_t r = c1;
                    partResult[len4 + (uint32_t)0U] = r;
                  }
                }
            }
            break;
          }
        case Hacl_Spec_MontgomeryMultiplication_DH:
          {
            uint64_t sw1;
            switch (c)
            {
              case Spec_ECC_Curves_P256:
                {
                  sw1 = (uint64_t)0xffffffffffffffffU;
                  break;
                }
              case Spec_ECC_Curves_P384:
                {
                  sw1 = (uint64_t)0xffffffffU;
                  break;
                }
              default:
                {
                  sw1 = KRML_EABORT(uint64_t, "");
                }
            }
            bool r = sw1 == (uint64_t)0xffffffffffffffffU;
            if (r)
            {
              montgomery_multiplication_round_w_k0(c, t0, t2);
            }
            else
            {
              uint64_t k00;
              switch (c)
              {
                case Spec_ECC_Curves_P256:
                  {
                    k00 = (uint64_t)1U;
                    break;
                  }
                case Spec_ECC_Curves_P384:
                  {
                    k00 = (uint64_t)4294967297U;
                    break;
                  }
                case Spec_ECC_Curves_Default:
                  {
                    uint64_t sw;
                    switch (c)
                    {
                      case Spec_ECC_Curves_P256:
                        {
                          sw = (uint64_t)0xffffffffffffffffU;
                          break;
                        }
                      case Spec_ECC_Curves_P384:
                        {
                          sw = (uint64_t)0xffffffffU;
                          break;
                        }
                      default:
                        {
                          sw = KRML_EABORT(uint64_t, "");
                        }
                    }
                    k00 = mod_inv_u64(sw);
                    break;
                  }
                default:
                  {
                    KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
                    KRML_HOST_EXIT(253U);
                  }
              }
              montgomery_multiplication_round_k0(c, k00, t0, t2);
            }
            break;
          }
        default:
          {
            KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
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
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        uint64_t t1 = t0[(uint32_t)4U * i];
        uint64_t t210 = t2[(uint32_t)4U * i];
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t210, t2 + (uint32_t)4U * i);
        uint64_t t10 = t0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t211 = t2[(uint32_t)4U * i + (uint32_t)1U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t10,
            t211,
            t2 + (uint32_t)4U * i + (uint32_t)1U);
        uint64_t t11 = t0[(uint32_t)4U * i + (uint32_t)2U];
        uint64_t t212 = t2[(uint32_t)4U * i + (uint32_t)2U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t11,
            t212,
            t2 + (uint32_t)4U * i + (uint32_t)2U);
        uint64_t t12 = t0[(uint32_t)4U * i + (uint32_t)3U];
        uint64_t t21 = t2[(uint32_t)4U * i + (uint32_t)3U];
        c1 =
          Lib_IntTypes_Intrinsics_add_carry_u64(c1,
            t12,
            t21,
            t2 + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < len4; i++)
      {
        uint64_t t1 = t0[i];
        uint64_t t21 = t2[i];
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t21, t2 + i);
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
      for (uint32_t i = (uint32_t)0U; i < len40; i++)
      {
        uint64_t elem = t2[(uint32_t)1U + i];
        t0[i] = elem;
      }
      t0[len40] = carry;
    }
    switch (m)
    {
      case Hacl_Spec_MontgomeryMultiplication_DH:
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
          uint64_t cin = t0[len3];
          uint64_t *x_ = t0;
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
                p1[4U] =
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
                }
                uint64_t r = c1;
                carry0 = r;
                break;
              }
            case Spec_ECC_Curves_P384:
              {
                uint64_t
                p1[6U] =
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          cmovznz4(c, carry, tempBuffer, x_, p);
          break;
        }
      case Hacl_Spec_MontgomeryMultiplication_DSA:
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
          uint64_t cin = t0[len3];
          uint64_t *x_ = t0;
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
                p1[4U] =
                  {
                    (uint64_t)17562291160714782033U,
                    (uint64_t)13611842547513532036U,
                    (uint64_t)18446744073709551615U,
                    (uint64_t)18446744069414584320U
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
                }
                uint64_t r = c1;
                carry0 = r;
                break;
              }
            case Spec_ECC_Curves_P384:
              {
                uint64_t
                p1[6U] =
                  {
                    (uint64_t)17072048233947408755U, (uint64_t)6348401684107011962U,
                    (uint64_t)14367412456785391071U, (uint64_t)18446744073709551615U,
                    (uint64_t)18446744073709551615U, (uint64_t)18446744073709551615U
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
                for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
                {
                  uint64_t t1 = x_[(uint32_t)4U * i];
                  uint64_t t20 = p1[(uint32_t)4U * i];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t1,
                      t20,
                      tempBuffer + (uint32_t)4U * i);
                  uint64_t t10 = x_[(uint32_t)4U * i + (uint32_t)1U];
                  uint64_t t21 = p1[(uint32_t)4U * i + (uint32_t)1U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t10,
                      t21,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)1U);
                  uint64_t t11 = x_[(uint32_t)4U * i + (uint32_t)2U];
                  uint64_t t22 = p1[(uint32_t)4U * i + (uint32_t)2U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t11,
                      t22,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)2U);
                  uint64_t t12 = x_[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t t2 = p1[(uint32_t)4U * i + (uint32_t)3U];
                  c1 =
                    Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
                      t12,
                      t2,
                      tempBuffer + (uint32_t)4U * i + (uint32_t)3U);
                }
                for (uint32_t i = k; i < len5; i++)
                {
                  uint64_t t1 = x_[i];
                  uint64_t t2 = p1[i];
                  c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tempBuffer + i);
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
          cmovznz4(c, carry, tempBuffer, x_, p);
          break;
        }
      default:
        {
          KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
          KRML_HOST_EXIT(253U);
        }
    }
    cswap(c, bit, p, a);
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
  memcpy(result, p, sw * sizeof (uint64_t));
}

static inline void exponent_p384(uint64_t *t, uint64_t *result, uint64_t *tempBuffer)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)6U;
  uint64_t *t2 = tempBuffer + (uint32_t)12U;
  uint64_t *t3 = tempBuffer + (uint32_t)18U;
  uint64_t *t4 = tempBuffer + (uint32_t)24U;
  uint64_t *t5 = tempBuffer + (uint32_t)30U;
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t, t0, t0);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t0, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t, t0, t0);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t0, t1);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)2U, t1);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t0, t1, t1);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t1, t2);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)5U, t2);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t2, t1, t2);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t2, t3);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)11U, t3);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t2, t3, t2);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)6U, t2);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t2, t1, t1);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t1, t2);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t2, t, t2);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t2, t3);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t, t3, t3);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t3, t4);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)30U, t4);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t2, t4);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t4, t5);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)62U, t5);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t5, t4);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P384, t4, t5);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)125U, t5);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t5, t4);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)3U, t4);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t0, t4);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)33U, t4);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t3, t4);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)94U, t4);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t1, t4);
  fsquarePowN_dh(Spec_ECC_Curves_P384, (uint32_t)2U, t4);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P384, t4, t, result);
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
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t, t2);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t2, t0);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t0, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t2, t6);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t6, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)3U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t6, t7);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t7, t0);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t0, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t2, t1);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t1, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)9U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t1, t3);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t3, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)9U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t1, t4);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t4, t0);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t0, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t2, t5);
  montgomery_square_buffer_dh(Spec_ECC_Curves_P256, t5, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)31U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)128U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t5, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)32U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t5, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)30U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t4, t0);
  fsquarePowN_dh(Spec_ECC_Curves_P256, (uint32_t)2U, t0);
  montgomery_multiplication_buffer_dh(Spec_ECC_Curves_P256, t0, t, result);
}

static inline void
exponent(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result, uint64_t *tempBuffer)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        exponent_p256(a, result, tempBuffer);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        exponent_p384(a, result, tempBuffer);
        break;
      }
    default:
      {
        const uint8_t *sw;
        switch (c)
        {
          case Spec_ECC_Curves_P256:
            {
              sw = prime256_inverse_buffer;
              break;
            }
          case Spec_ECC_Curves_P384:
            {
              sw = prime384_inverse_buffer;
              break;
            }
          default:
            {
              sw = prime256_inverse_buffer;
            }
        }
        montgomery_ladder_power(c, Hacl_Spec_MontgomeryMultiplication_DH, a, sw, result);
      }
  }
}

static inline void
point_double(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *result, uint64_t *tempBuffer)
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
  montgomery_square_buffer_dh(c, pZ1, delta);
  montgomery_square_buffer_dh(c, pY1, gamma);
  montgomery_multiplication_buffer_dh(c, pX1, gamma, beta);
  felem_sub(c, pX1, delta, a0);
  felem_add(c, pX1, delta, a1);
  montgomery_multiplication_buffer_dh(c, a0, a1, alpha0);
  felem_add(c, alpha0, alpha0, alpha);
  felem_add(c, alpha0, alpha, alpha);
  montgomery_square_buffer_dh(c, alpha, x3);
  felem_add(c, beta, beta, fourBeta);
  felem_add(c, fourBeta, fourBeta, fourBeta);
  felem_add(c, fourBeta, fourBeta, eightBeta);
  felem_sub(c, x3, eightBeta, x3);
  felem_add(c, pY, pZ, z3);
  montgomery_square_buffer_dh(c, z3, z3);
  felem_sub(c, z3, gamma, z3);
  felem_sub(c, z3, delta, z3);
  felem_sub(c, fourBeta, x3, y3);
  montgomery_multiplication_buffer_dh(c, alpha, y3, y3);
  montgomery_square_buffer_dh(c, gamma, gamma);
  felem_add(c, gamma, gamma, eightGamma);
  felem_add(c, eightGamma, eightGamma, eightGamma);
  felem_add(c, eightGamma, eightGamma, eightGamma);
  felem_sub(c, y3, eightGamma, y3);
}

static inline void
point_add(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *q,
  uint64_t *result,
  uint64_t *tempBuffer
)
{
  uint64_t *t12 = tempBuffer;
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
  uint64_t *t5 = tempBuffer + (uint32_t)12U * sw0;
  uint64_t *t4 = t12;
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
  uint64_t *u1 = t12 + (uint32_t)4U * sw1;
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
  uint64_t *u2 = t12 + (uint32_t)5U * sw2;
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
  uint64_t *s1 = t12 + (uint32_t)6U * sw3;
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
  uint64_t *s2 = t12 + (uint32_t)7U * sw4;
  uint64_t *pX = p;
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
  uint64_t *pY = p + sw5;
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
  uint64_t *pZ = p + (uint32_t)2U * sw6;
  uint64_t *qX = q;
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
  uint64_t *qY = q + sw7;
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
  uint64_t *qZ = q + (uint32_t)2U * sw8;
  uint64_t *z2Square = t4;
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
  uint64_t *z1Square = t4 + sw9;
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
  uint64_t *z2Cube = t4 + (uint32_t)2U * sw10;
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
  uint64_t *z1Cube = t4 + (uint32_t)3U * sw11;
  montgomery_square_buffer_dh(c, qZ, z2Square);
  montgomery_square_buffer_dh(c, pZ, z1Square);
  montgomery_multiplication_buffer_dh(c, z2Square, qZ, z2Cube);
  montgomery_multiplication_buffer_dh(c, z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer_dh(c, z2Square, pX, u1);
  montgomery_multiplication_buffer_dh(c, z1Square, qX, u2);
  montgomery_multiplication_buffer_dh(c, z2Cube, pY, s1);
  montgomery_multiplication_buffer_dh(c, z1Cube, qY, s2);
  uint64_t *t40 = t12;
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
  uint64_t *u10 = t12 + (uint32_t)4U * sw12;
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
  uint64_t *u20 = t12 + (uint32_t)5U * sw13;
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
  uint64_t *s10 = t12 + (uint32_t)6U * sw14;
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
  uint64_t *s20 = t12 + (uint32_t)7U * sw15;
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
  uint64_t *h0 = t12 + (uint32_t)8U * sw16;
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
  uint64_t *r = t12 + (uint32_t)9U * sw17;
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
  uint64_t *uh = t12 + (uint32_t)10U * sw18;
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
  uint64_t *hCube = t12 + (uint32_t)11U * sw19;
  uint64_t *temp = t40;
  felem_sub(c, u20, u10, h0);
  felem_sub(c, s20, s10, r);
  montgomery_square_buffer_dh(c, h0, temp);
  montgomery_multiplication_buffer_dh(c, temp, u10, uh);
  montgomery_multiplication_buffer_dh(c, temp, h0, hCube);
  uint64_t *x3y3z3u1u2s1s2 = t12;
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
  uint64_t *rhuhhCube = t12 + (uint32_t)8U * sw20;
  uint64_t *h = rhuhhCube;
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
  uint64_t *r0 = rhuhhCube + sw21;
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
  uint64_t *uh0 = rhuhhCube + (uint32_t)2U * sw22;
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
  uint64_t *hCube0 = rhuhhCube + (uint32_t)3U * sw23;
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
  uint64_t *u11 = x3y3z3u1u2s1s2 + (uint32_t)4U * sw24;
  uint32_t sw25;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw25 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw25 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw25 = (uint32_t)4U;
      }
  }
  uint64_t *u21 = x3y3z3u1u2s1s2 + (uint32_t)5U * sw25;
  uint32_t sw26;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw26 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw26 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw26 = (uint32_t)4U;
      }
  }
  uint64_t *s11 = x3y3z3u1u2s1s2 + (uint32_t)6U * sw26;
  uint32_t sw27;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw27 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw27 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw27 = (uint32_t)4U;
      }
  }
  uint64_t *s21 = x3y3z3u1u2s1s2 + (uint32_t)7U * sw27;
  uint64_t *x3 = t5;
  uint32_t sw28;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw28 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw28 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw28 = (uint32_t)4U;
      }
  }
  uint64_t *tempBuffer3 = t5 + sw28;
  uint64_t *rSquare = tempBuffer3;
  uint32_t sw29;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw29 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw29 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw29 = (uint32_t)4U;
      }
  }
  uint64_t *rH = tempBuffer3 + sw29;
  uint32_t sw30;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw30 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw30 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw30 = (uint32_t)4U;
      }
  }
  uint64_t *twoUh = tempBuffer3 + (uint32_t)2U * sw30;
  montgomery_square_buffer_dh(c, r0, rSquare);
  felem_sub(c, rSquare, hCube0, rH);
  felem_add(c, uh0, uh0, twoUh);
  felem_sub(c, rH, twoUh, x3);
  uint64_t *x30 = t5;
  uint32_t sw31;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw31 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw31 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw31 = (uint32_t)4U;
      }
  }
  uint64_t *y3 = t5 + sw31;
  uint32_t sw32;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw32 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw32 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw32 = (uint32_t)4U;
      }
  }
  uint64_t *tempBuffer30 = t5 + (uint32_t)2U * sw32;
  uint64_t *s1hCube = tempBuffer30;
  uint32_t sw33;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw33 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw33 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw33 = (uint32_t)4U;
      }
  }
  uint64_t *u1hx3 = tempBuffer30 + sw33;
  uint32_t sw34;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw34 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw34 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw34 = (uint32_t)4U;
      }
  }
  uint64_t *ru1hx3 = tempBuffer30 + (uint32_t)2U * sw34;
  montgomery_multiplication_buffer_dh(c, s11, hCube0, s1hCube);
  felem_sub(c, uh0, x30, u1hx3);
  montgomery_multiplication_buffer_dh(c, u1hx3, r0, ru1hx3);
  felem_sub(c, ru1hx3, s1hCube, y3);
  uint32_t sw35;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw35 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw35 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw35 = (uint32_t)4U;
      }
  }
  uint64_t *z1 = p + (uint32_t)2U * sw35;
  uint32_t sw36;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw36 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw36 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw36 = (uint32_t)4U;
      }
  }
  uint64_t *z2 = q + (uint32_t)2U * sw36;
  uint32_t sw37;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw37 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw37 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw37 = (uint32_t)4U;
      }
  }
  uint64_t *z3 = t5 + (uint32_t)2U * sw37;
  uint32_t sw38;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw38 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw38 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw38 = (uint32_t)4U;
      }
  }
  uint64_t *t1 = t5 + (uint32_t)3U * sw38;
  uint64_t *z1z2 = t1;
  montgomery_multiplication_buffer_dh(c, z1, z2, z1z2);
  montgomery_multiplication_buffer_dh(c, z1z2, h, z3);
  uint64_t *x3_out = t5;
  uint32_t sw39;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw39 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw39 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw39 = (uint32_t)4U;
      }
  }
  uint64_t *y3_out = t5 + sw39;
  uint32_t sw40;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw40 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw40 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw40 = (uint32_t)4U;
      }
  }
  uint64_t *z3_out = t5 + (uint32_t)2U * sw40;
  uint32_t sw41;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw41 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw41 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw41 = (uint32_t)4U;
      }
  }
  uint64_t *z = p + (uint32_t)2U * sw41;
  uint64_t tmp1 = (uint64_t)18446744073709551615U;
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
    uint64_t tmp0 = tmp1;
    tmp1 = r_i & tmp0;
  }
  uint64_t mask = tmp1;
  uint64_t *p_x0 = q;
  uint32_t sw42;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw42 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw42 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw42 = (uint32_t)4U;
      }
  }
  uint64_t *p_y = q + sw42;
  uint32_t sw43;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw43 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw43 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw43 = (uint32_t)4U;
      }
  }
  uint64_t *p_z = q + (uint32_t)2U * sw43;
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
    uint64_t x_i = p_x0[i];
    uint64_t out_i = x3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    x3_out[i] = r_i;
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
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t x_i = p_y[i];
    uint64_t out_i = y3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    y3_out[i] = r_i;
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
  for (uint32_t i = (uint32_t)0U; i < len3; i++)
  {
    uint64_t x_i = p_z[i];
    uint64_t out_i = z3_out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    z3_out[i] = r_i;
  }
  uint32_t sw44;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw44 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw44 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw44 = (uint32_t)4U;
      }
  }
  uint64_t *z0 = q + (uint32_t)2U * sw44;
  uint64_t tmp = (uint64_t)18446744073709551615U;
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
    uint64_t a_i = z0[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t mask0 = tmp;
  uint64_t *p_x = p;
  uint32_t sw45;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw45 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw45 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw45 = (uint32_t)4U;
      }
  }
  uint64_t *p_y0 = p + sw45;
  uint32_t sw46;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw46 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw46 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw46 = (uint32_t)4U;
      }
  }
  uint64_t *p_z0 = p + (uint32_t)2U * sw46;
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
    uint64_t x_i = p_x[i];
    uint64_t out_i = x3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    x3_out[i] = r_i;
  }
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
  for (uint32_t i = (uint32_t)0U; i < len5; i++)
  {
    uint64_t x_i = p_y0[i];
    uint64_t out_i = y3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    y3_out[i] = r_i;
  }
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
  for (uint32_t i = (uint32_t)0U; i < len6; i++)
  {
    uint64_t x_i = p_z0[i];
    uint64_t out_i = z3_out[i];
    uint64_t r_i = out_i ^ (mask0 & (out_i ^ x_i));
    z3_out[i] = r_i;
  }
  uint32_t sw47;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw47 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw47 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw47 = (uint32_t)4U;
      }
  }
  memcpy(result, x3_out, sw47 * sizeof (uint64_t));
  uint32_t sw48;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw48 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw48 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw48 = (uint32_t)4U;
      }
  }
  uint32_t sw49;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw49 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw49 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw49 = (uint32_t)4U;
      }
  }
  memcpy(result + sw48, y3_out, sw49 * sizeof (uint64_t));
  uint32_t sw50;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw50 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw50 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw50 = (uint32_t)4U;
      }
  }
  uint32_t sw51;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw51 = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw51 = (uint32_t)6U;
        break;
      }
    default:
      {
        sw51 = (uint32_t)4U;
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
  memcpy(result + sw50 + sw51, z3_out, sw * sizeof (uint64_t));
}

static inline uint64_t
scalar_bit(Spec_ECC_Curves_curve c, Lib_Buffer_buftype buf_type, void *s, uint32_t n)
{
  uint8_t sw0;
  switch (buf_type)
  {
    case Lib_Buffer_MUT:
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
              sw = (uint32_t)1U;
            }
        }
        sw0 = ((uint8_t *)s)[sw * (uint32_t)8U - (uint32_t)1U - n / (uint32_t)8U];
        break;
      }
    case Lib_Buffer_IMMUT:
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
              sw = (uint32_t)1U;
            }
        }
        sw0 = ((uint8_t *)s)[sw * (uint32_t)8U - (uint32_t)1U - n / (uint32_t)8U];
        break;
      }
    case Lib_Buffer_CONST:
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
              sw = (uint32_t)1U;
            }
        }
        sw0 = ((const uint8_t *)s)[sw * (uint32_t)8U - (uint32_t)1U - n / (uint32_t)8U];
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  return (uint64_t)(sw0 >> n % (uint32_t)8U & (uint8_t)1U);
}

static inline void cswap0(Spec_ECC_Curves_curve c, uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
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
  uint32_t len = sw * (uint32_t)3U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static inline void
montgomery_ladder(
  Spec_ECC_Curves_curve c,
  Lib_Buffer_buftype a,
  uint64_t *p,
  uint64_t *q,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t cycleLoop = Spec_ECC_Curves_getScalarLen(c);
  for (uint32_t i = (uint32_t)0U; i < cycleLoop; i++)
  {
    uint32_t bit0 = Spec_ECC_Curves_getScalarLen(c) - (uint32_t)1U - i;
    uint64_t bit = scalar_bit(c, a, scalar, bit0);
    cswap0(c, bit, p, q);
    point_add(c, p, q, q, tempBuffer);
    point_double(c, p, p, tempBuffer);
    cswap0(c, bit, p, q);
  }
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
  cmovznz4(Spec_ECC_Curves_P256, r0, tempBuffer1, t01, t01);
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
  uint32_t k1 = len11 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k1; i8 < len11; i8++)
  {
    uint64_t t12 = t110[i8];
    uint64_t t22 = p1[i8];
    c17 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c17, t12, t22, tempBuffer10 + i8);
  }
  uint64_t r1 = c17;
  uint64_t r2 = r1;
  cmovznz4(Spec_ECC_Curves_P256, r2, tempBuffer10, t110, t110);
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
  uint32_t k2 = len12 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k2; i8 < len12; i8++)
  {
    uint64_t t12 = t310[i8];
    uint64_t t22 = p2[i8];
    c18 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c18, t12, t22, tempBuffer11 + i8);
  }
  uint64_t r3 = c18;
  uint64_t r4 = r3;
  cmovznz4(Spec_ECC_Curves_P256, r4, tempBuffer11, t310, t310);
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
  uint32_t k3 = len13 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k3; i8 < len13; i8++)
  {
    uint64_t t12 = t410[i8];
    uint64_t t22 = p3[i8];
    c19 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c19, t12, t22, tempBuffer12 + i8);
  }
  uint64_t r5 = c19;
  uint64_t r6 = r5;
  cmovznz4(Spec_ECC_Curves_P256, r6, tempBuffer12, t410, t410);
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
  uint32_t k4 = len14 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k4; i8 < len14; i8++)
  {
    uint64_t t12 = t510[i8];
    uint64_t t22 = p4[i8];
    c20 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c20, t12, t22, tempBuffer13 + i8);
  }
  uint64_t r7 = c20;
  uint64_t r8 = r7;
  cmovznz4(Spec_ECC_Curves_P256, r8, tempBuffer13, t510, t510);
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
  uint32_t k5 = len15 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k5; i8 < len15; i8++)
  {
    uint64_t t12 = t610[i8];
    uint64_t t22 = p5[i8];
    c21 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c21, t12, t22, tempBuffer14 + i8);
  }
  uint64_t r9 = c21;
  uint64_t r10 = r9;
  cmovznz4(Spec_ECC_Curves_P256, r10, tempBuffer14, t610, t610);
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
  uint32_t k6 = len16 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k6; i8 < len16; i8++)
  {
    uint64_t t12 = t710[i8];
    uint64_t t22 = p6[i8];
    c22 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c22, t12, t22, tempBuffer15 + i8);
  }
  uint64_t r11 = c22;
  uint64_t r12 = r11;
  cmovznz4(Spec_ECC_Curves_P256, r12, tempBuffer15, t710, t710);
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
  uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i8 = k; i8 < len1; i8++)
  {
    uint64_t t12 = t810[i8];
    uint64_t t22 = p[i8];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t22, tempBuffer16 + i8);
  }
  uint64_t r13 = c;
  uint64_t r14 = r13;
  cmovznz4(Spec_ECC_Curves_P256, r14, tempBuffer16, t810, t810);
  uint64_t *t010 = tempBuffer;
  uint64_t *t11 = tempBuffer + (uint32_t)4U;
  uint64_t *t21 = tempBuffer + (uint32_t)8U;
  uint64_t *t31 = tempBuffer + (uint32_t)12U;
  uint64_t *t41 = tempBuffer + (uint32_t)16U;
  uint64_t *t51 = tempBuffer + (uint32_t)20U;
  uint64_t *t61 = tempBuffer + (uint32_t)24U;
  uint64_t *t71 = tempBuffer + (uint32_t)28U;
  uint64_t *t81 = tempBuffer + (uint32_t)32U;
  felem_double(Spec_ECC_Curves_P256, t21, t21);
  felem_double(Spec_ECC_Curves_P256, t11, t11);
  felem_add(Spec_ECC_Curves_P256, t010, t11, o);
  felem_add(Spec_ECC_Curves_P256, t21, o, o);
  felem_add(Spec_ECC_Curves_P256, t31, o, o);
  felem_add(Spec_ECC_Curves_P256, t41, o, o);
  felem_sub(Spec_ECC_Curves_P256, o, t51, o);
  felem_sub(Spec_ECC_Curves_P256, o, t61, o);
  felem_sub(Spec_ECC_Curves_P256, o, t71, o);
  felem_sub(Spec_ECC_Curves_P256, o, t81, o);
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
  cmovznz4(Spec_ECC_Curves_P384, r0, tempBuffer1, t01, t01);
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
  uint32_t k1 = len11 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k1; i12 < len11; i12++)
  {
    uint64_t t12 = t210[i12];
    uint64_t t22 = p1[i12];
    c25 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c25, t12, t22, tempBuffer10 + i12);
  }
  uint64_t r1 = c25;
  uint64_t r2 = r1;
  cmovznz4(Spec_ECC_Curves_P384, r2, tempBuffer10, t210, t210);
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
  uint32_t k2 = len12 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k2; i12 < len12; i12++)
  {
    uint64_t t12 = t310[i12];
    uint64_t t22 = p2[i12];
    c26 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c26, t12, t22, tempBuffer11 + i12);
  }
  uint64_t r3 = c26;
  uint64_t r4 = r3;
  cmovznz4(Spec_ECC_Curves_P384, r4, tempBuffer11, t310, t310);
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
  uint32_t k3 = len13 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k3; i12 < len13; i12++)
  {
    uint64_t t12 = t410[i12];
    uint64_t t22 = p3[i12];
    c27 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c27, t12, t22, tempBuffer12 + i12);
  }
  uint64_t r5 = c27;
  uint64_t r6 = r5;
  cmovznz4(Spec_ECC_Curves_P384, r6, tempBuffer12, t410, t410);
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
  uint32_t k4 = len14 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k4; i12 < len14; i12++)
  {
    uint64_t t12 = t510[i12];
    uint64_t t22 = p4[i12];
    c28 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c28, t12, t22, tempBuffer13 + i12);
  }
  uint64_t r7 = c28;
  uint64_t r8 = r7;
  cmovznz4(Spec_ECC_Curves_P384, r8, tempBuffer13, t510, t510);
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
  uint32_t k5 = len15 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k5; i12 < len15; i12++)
  {
    uint64_t t12 = t610[i12];
    uint64_t t22 = p5[i12];
    c29 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c29, t12, t22, tempBuffer14 + i12);
  }
  uint64_t r9 = c29;
  uint64_t r10 = r9;
  cmovznz4(Spec_ECC_Curves_P384, r10, tempBuffer14, t610, t610);
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
  uint32_t k6 = len16 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k6; i12 < len16; i12++)
  {
    uint64_t t12 = t710[i12];
    uint64_t t22 = p6[i12];
    c30 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c30, t12, t22, tempBuffer15 + i12);
  }
  uint64_t r11 = c30;
  uint64_t r12 = r11;
  cmovznz4(Spec_ECC_Curves_P384, r12, tempBuffer15, t710, t710);
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
  uint32_t k7 = len17 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k7; i12 < len17; i12++)
  {
    uint64_t t12 = t810[i12];
    uint64_t t22 = p7[i12];
    c31 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c31, t12, t22, tempBuffer16 + i12);
  }
  uint64_t r13 = c31;
  uint64_t r14 = r13;
  cmovznz4(Spec_ECC_Curves_P384, r14, tempBuffer16, t810, t810);
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
  uint32_t k = len1 / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i12 = k; i12 < len1; i12++)
  {
    uint64_t t12 = t910[i12];
    uint64_t t22 = p[i12];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t22, tempBuffer17 + i12);
  }
  uint64_t r15 = c;
  uint64_t r16 = r15;
  cmovznz4(Spec_ECC_Curves_P384, r16, tempBuffer17, t910, t910);
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
  felem_double(Spec_ECC_Curves_P384, t11, t11);
  felem_add(Spec_ECC_Curves_P384, t010, t11, t11);
  felem_add(Spec_ECC_Curves_P384, t11, t21, t21);
  felem_add(Spec_ECC_Curves_P384, t21, t31, t31);
  felem_add(Spec_ECC_Curves_P384, t31, t41, t41);
  felem_add(Spec_ECC_Curves_P384, t41, t51, t51);
  felem_add(Spec_ECC_Curves_P384, t51, t61, t61);
  felem_sub(Spec_ECC_Curves_P384, t61, t71, t71);
  felem_sub(Spec_ECC_Curves_P384, t71, t81, t81);
  felem_sub(Spec_ECC_Curves_P384, t81, t91, o);
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
        montgomery_multiplication_reduction_dh(c, i, o);
        montgomery_multiplication_buffer_dh(c, t, o, o);
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
  montgomery_square_buffer_dh(c, zf, z2f);
  montgomery_multiplication_buffer_dh(c, z2f, zf, z3f);
  exponent(c, z2f, z2f, t8);
  exponent(c, z3f, z3f, t8);
  montgomery_multiplication_buffer_dh(c, xf, z2f, z2f);
  montgomery_multiplication_buffer_dh(c, yf, z3f, z3f);
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
  montgomery_multiplication_buffer_by_one_dh(c, z2f, resultX);
  montgomery_multiplication_buffer_by_one_dh(c, z3f, resultY);
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

static inline void fromFormPoint(Spec_ECC_Curves_curve c, uint64_t *i, uint8_t *o)
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
  uint32_t scalarLen = sw0 * (uint32_t)8U;
  uint64_t *resultBufferX = i;
  uint64_t *resultBufferY = i + len;
  uint8_t *resultX = o;
  uint8_t *resultY = o + scalarLen;
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
  uint32_t lenByTwo = len1 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
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
    uint32_t lenRight = sw - (uint32_t)1U - i0;
    uint64_t left = resultBufferX[i0];
    uint64_t right = resultBufferX[lenRight];
    resultBufferX[i0] = right;
    resultBufferX[lenRight] = left;
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    store64_be(resultX + i0 * (uint32_t)8U, resultBufferX[i0]);
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
  uint32_t lenByTwo0 = len11 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo0; i0++)
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
    uint32_t lenRight = sw - (uint32_t)1U - i0;
    uint64_t left = resultBufferY[i0];
    uint64_t right = resultBufferY[lenRight];
    resultBufferY[i0] = right;
    resultBufferY[lenRight] = left;
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len12; i0++)
  {
    store64_be(resultY + i0 * (uint32_t)8U, resultBufferY[i0]);
  }
}

static inline void toFormPoint(Spec_ECC_Curves_curve c, uint8_t *i, uint64_t *o)
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
  uint32_t coordLen = sw0 * (uint32_t)8U;
  uint8_t *pointScalarX = i;
  uint8_t *pointScalarY = i + coordLen;
  uint64_t *pointX = o;
  uint64_t *pointY = o + len;
  uint64_t *pointZ = o + (uint32_t)2U * len;
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len1; i0++)
  {
    uint64_t *os = pointX;
    uint8_t *bj = pointScalarX + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
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
  uint32_t lenByTwo = len2 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo; i0++)
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
    uint32_t lenRight = sw - (uint32_t)1U - i0;
    uint64_t left = pointX[i0];
    uint64_t right = pointX[lenRight];
    pointX[i0] = right;
    pointX[lenRight] = left;
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
  for (uint32_t i0 = (uint32_t)0U; i0 < len10; i0++)
  {
    uint64_t *os = pointY;
    uint8_t *bj = pointScalarY + i0 * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i0] = x;
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
  uint32_t lenByTwo0 = len20 >> (uint32_t)1U;
  for (uint32_t i0 = (uint32_t)0U; i0 < lenByTwo0; i0++)
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
    uint32_t lenRight = sw - (uint32_t)1U - i0;
    uint64_t left = pointY[i0];
    uint64_t right = pointY[lenRight];
    pointY[i0] = right;
    pointY[lenRight] = left;
  }
  pointZ[0U] = (uint64_t)1U;
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
  for (uint32_t i0 = (uint32_t)1U; i0 < len11; i0++)
  {
    pointZ[i0] = (uint64_t)0U;
  }
}

static inline bool isPointAtInfinityPublic(Spec_ECC_Curves_curve c, uint64_t *p)
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
  uint64_t *zCoordinate = p + (uint32_t)2U * len;
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
    uint64_t a_i = zCoordinate[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t f = tmp;
  return f == (uint64_t)0xffffffffffffffffU;
}

static inline bool isPointOnCurvePublic(Spec_ECC_Curves_curve c, uint64_t *p)
{
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
  uint64_t *x = p;
  uint64_t *y = p + sz;
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len0);
  uint64_t multBuffer[(uint32_t)2U * len0];
  memset(multBuffer, 0U, (uint32_t)2U * len0 * sizeof (uint64_t));
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
  memcpy(oToCopy0, y, len10 * sizeof (uint64_t));
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
    oToZero0[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer, y2Buffer);
  montgomery_square_buffer_dh(c, y2Buffer, y2Buffer);
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
  uint64_t multBuffer0[(uint32_t)2U * len3];
  memset(multBuffer0, 0U, (uint32_t)2U * len3 * sizeof (uint64_t));
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
  uint64_t *oToZero = multBuffer0;
  uint64_t *oToCopy = multBuffer0 + len1;
  memcpy(oToCopy, x, len1 * sizeof (uint64_t));
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
    oToZero[i] = (uint64_t)0U;
  }
  reduction(c, multBuffer0, xToDomainBuffer);
  montgomery_square_buffer_dh(c, xToDomainBuffer, xBuffer);
  montgomery_multiplication_buffer_dh(c, xBuffer, xToDomainBuffer, xBuffer);
  felem_add(c, xToDomainBuffer, xToDomainBuffer, minusThreeXBuffer);
  felem_add(c, xToDomainBuffer, minusThreeXBuffer, minusThreeXBuffer);
  felem_sub(c, xBuffer, minusThreeXBuffer, xBuffer);
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
  felem_add(c, xBuffer, b_constant, xBuffer);
  uint64_t tmp = (uint64_t)0U;
  tmp = (uint64_t)18446744073709551615U;
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
    uint64_t a_i = y2Buffer[i];
    uint64_t b_i = xBuffer[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  uint64_t r = tmp;
  return !(r == (uint64_t)0U);
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
  bool belongsToCurve = isPointOnCurvePublic(c, pubKey);
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
    uint64_t *q = tempBuffer;
    uint64_t *buff = tempBuffer + (uint32_t)3U * len2;
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
    uint64_t *x = q;
    uint64_t *y = q + len3;
    uint64_t *z = q + (uint32_t)2U * len3;
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
    uint64_t *p_x = pBuffer;
    uint64_t *p_y = pBuffer + len30;
    uint64_t *p_z = pBuffer + (uint32_t)2U * len30;
    uint64_t *r_x = multResult;
    uint64_t *r_y = multResult + len30;
    uint64_t *r_z = multResult + (uint32_t)2U * len30;
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
    uint64_t multBuffer[(uint32_t)2U * len4];
    memset(multBuffer, 0U, (uint32_t)2U * len4 * sizeof (uint64_t));
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
    uint64_t *oToZero0 = multBuffer;
    uint64_t *oToCopy0 = multBuffer + len50;
    memcpy(oToCopy0, p_x, len50 * sizeof (uint64_t));
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
    for (uint32_t i = (uint32_t)0U; i < len6; i++)
    {
      oToZero0[i] = (uint64_t)0U;
    }
    reduction(c, multBuffer, r_x);
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
    uint64_t multBuffer0[(uint32_t)2U * len43];
    memset(multBuffer0, 0U, (uint32_t)2U * len43 * sizeof (uint64_t));
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
    uint64_t *oToZero1 = multBuffer0;
    uint64_t *oToCopy1 = multBuffer0 + len51;
    memcpy(oToCopy1, p_y, len51 * sizeof (uint64_t));
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
      oToZero1[i] = (uint64_t)0U;
    }
    reduction(c, multBuffer0, r_y);
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
    uint64_t multBuffer1[(uint32_t)2U * len44];
    memset(multBuffer1, 0U, (uint32_t)2U * len44 * sizeof (uint64_t));
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
    uint64_t *oToZero = multBuffer1;
    uint64_t *oToCopy = multBuffer1 + len5;
    memcpy(oToCopy, p_z, len5 * sizeof (uint64_t));
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
      oToZero[i] = (uint64_t)0U;
    }
    reduction(c, multBuffer1, r_z);
    montgomery_ladder(c, Lib_Buffer_CONST, q, multResult, (void *)prime256_order_, buff);
    norm(c, q, multResult, buff);
    bool result = isPointAtInfinityPublic(c, multResult);
    bool orderCorrect0 = result;
    orderCorrect = orderCorrect0;
  }
  else
  {
    orderCorrect = true;
  }
  return coordinatesValid && belongsToCurve && orderCorrect;
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
  montgomery_ladder(Spec_ECC_Curves_P256, Lib_Buffer_MUT, q, resultBuffer, (void *)scalar, buff);
  norm(Spec_ECC_Curves_P256, q, resultBuffer, buff);
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
  fromFormPoint(Spec_ECC_Curves_P256, resultBuffer, result);
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
  montgomery_ladder(Spec_ECC_Curves_P384, Lib_Buffer_MUT, q, resultBuffer, (void *)scalar, buff);
  norm(Spec_ECC_Curves_P384, q, resultBuffer, buff);
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
  fromFormPoint(Spec_ECC_Curves_P384, resultBuffer, result);
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
  toFormPoint(Spec_ECC_Curves_P256, pubKey, pkF);
  uint32_t len1 = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint(Spec_ECC_Curves_P256, pkF, tempBuffer);
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
    uint32_t len31 = (uint32_t)4U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len31;
    uint64_t *p_z = pkF + (uint32_t)2U * len31;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len31;
    uint64_t *r_z = rF + (uint32_t)2U * len31;
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
    montgomery_ladder(Spec_ECC_Curves_P256, Lib_Buffer_MUT, q, rF, (void *)scalar, buff);
    norm(Spec_ECC_Curves_P256, q, rF, buff);
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
  fromFormPoint(Spec_ECC_Curves_P256, rF, result);
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
  toFormPoint(Spec_ECC_Curves_P384, pubKey, pkF);
  uint32_t len1 = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)20U * len1);
  uint64_t tempBuffer[(uint32_t)20U * len1];
  memset(tempBuffer, 0U, (uint32_t)20U * len1 * sizeof (uint64_t));
  bool publicKeyCorrect = verifyQValidCurvePoint(Spec_ECC_Curves_P384, pkF, tempBuffer);
  bool flag;
  if (publicKeyCorrect)
  {
    uint32_t len2 = (uint32_t)6U;
    uint64_t *q = tempBuffer;
    uint64_t *buff = tempBuffer + (uint32_t)3U * len2;
    uint32_t len30 = (uint32_t)6U;
    uint64_t *x = q;
    uint64_t *y = q + len30;
    uint64_t *z = q + (uint32_t)2U * len30;
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
    uint32_t len31 = (uint32_t)6U;
    uint64_t *p_x = pkF;
    uint64_t *p_y = pkF + len31;
    uint64_t *p_z = pkF + (uint32_t)2U * len31;
    uint64_t *r_x = rF;
    uint64_t *r_y = rF + len31;
    uint64_t *r_z = rF + (uint32_t)2U * len31;
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
    montgomery_ladder(Spec_ECC_Curves_P384, Lib_Buffer_MUT, q, rF, (void *)scalar, buff);
    norm(Spec_ECC_Curves_P384, q, rF, buff);
    uint32_t len20 = (uint32_t)6U;
    uint32_t start = len20 * (uint32_t)2U;
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
  fromFormPoint(Spec_ECC_Curves_P384, rF, result);
  bool flag0 = flag;
  return (uint64_t)flag0;
}

