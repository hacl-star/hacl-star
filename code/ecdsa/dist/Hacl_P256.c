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
uint64_t
prime256_buffer[4U] =
  {
    (uint64_t)0xffffffffffffffffU,
    (uint64_t)0xffffffffU,
    (uint64_t)0U,
    (uint64_t)0xffffffff00000001U
  };

static const
uint64_t
prime384_buffer[6U] =
  {
    (uint64_t)0xffffffffU, (uint64_t)0xffffffff00000000U, (uint64_t)0xfffffffffffffffeU,
    (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU, (uint64_t)0xffffffffffffffffU
  };

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

static uint64_t getK0(Spec_ECC_Curves_curve c)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return (uint64_t)1U;
      }
    case Spec_ECC_Curves_P384:
      {
        return (uint64_t)4294967297U;
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
        uint64_t r = mod_inv_u64(sw);
        return r;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
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

static void
copy_conditional(Spec_ECC_Curves_curve c, uint64_t *out, uint64_t *x, uint64_t mask)
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
    uint64_t x_i = x[i];
    uint64_t out_i = out[i];
    uint64_t r_i = out_i ^ (mask & (out_i ^ x_i));
    out[i] = r_i;
  }
}

static void
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

static uint64_t add6(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t c = (uint64_t)0U;
  uint32_t k = (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = x[(uint32_t)4U * i];
    uint64_t t20 = y[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, result + (uint32_t)4U * i);
    uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
    c =
      Lib_IntTypes_Intrinsics_add_carry_u64(c,
        t10,
        t21,
        result + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
    c =
      Lib_IntTypes_Intrinsics_add_carry_u64(c,
        t11,
        t22,
        result + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, result + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < (uint32_t)6U; i++)
  {
    uint64_t t1 = x[i];
    uint64_t t2 = y[i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, result + i);
  }
  return c;
}

static uint64_t add_dep_prime_p384(uint64_t *x, uint64_t t, uint64_t *result)
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
  uint64_t r = add6(x, b, result);
  return r;
}

static uint64_t add4(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc0 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc0, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static uint64_t add4_with_carry(uint64_t c, uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_add_carry_u64(c, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_add_carry_u64(cc, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_add_carry_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_add_carry_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static uint64_t add8(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *a0 = x;
  uint64_t *a1 = x + (uint32_t)4U;
  uint64_t *b0 = y;
  uint64_t *b1 = y + (uint32_t)4U;
  uint64_t *c0 = result;
  uint64_t *c1 = result + (uint32_t)4U;
  uint64_t carry0 = add4(a0, b0, c0);
  uint64_t carry1 = add4_with_carry(carry0, a1, b1, c1);
  return carry1;
}

static uint64_t sub4_il(uint64_t *x, const uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static uint64_t sub4(uint64_t *x, uint64_t *y, uint64_t *result)
{
  uint64_t *r0 = result;
  uint64_t *r1 = result + (uint32_t)1U;
  uint64_t *r2 = result + (uint32_t)2U;
  uint64_t *r3 = result + (uint32_t)3U;
  uint64_t cc = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, x[0U], y[0U], r0);
  uint64_t cc1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc, x[1U], y[1U], r1);
  uint64_t cc2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc1, x[2U], y[2U], r2);
  uint64_t cc3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(cc2, x[3U], y[3U], r3);
  return cc3;
}

static void mul64(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static void square_p256(uint64_t *f, uint64_t *out)
{
  uint64_t wb[17U] = { 0U };
  uint64_t *tb = wb;
  uint64_t *memory = wb + (uint32_t)5U;
  uint64_t *b0 = out;
  uint64_t f01 = f[0U];
  uint64_t f310 = f[3U];
  uint64_t *o30 = b0 + (uint32_t)3U;
  uint64_t *temp1 = tb;
  uint64_t f02 = f[0U];
  uint64_t f12 = f[1U];
  uint64_t f22 = f[2U];
  uint64_t *o01 = b0;
  uint64_t *o10 = b0 + (uint32_t)1U;
  uint64_t *o20 = b0 + (uint32_t)2U;
  mul64(f02, f02, o01, temp1);
  uint64_t h_00 = temp1[0U];
  mul64(f02, f12, o10, temp1);
  uint64_t l0 = o10[0U];
  memory[0U] = l0;
  memory[1U] = temp1[0U];
  uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h_00, o10);
  uint64_t h_10 = temp1[0U];
  mul64(f02, f22, o20, temp1);
  uint64_t l10 = o20[0U];
  memory[2U] = l10;
  memory[3U] = temp1[0U];
  uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l10, h_10, o20);
  uint64_t h_20 = temp1[0U];
  mul64(f01, f310, o30, temp1);
  uint64_t l3 = o30[0U];
  memory[4U] = l3;
  memory[5U] = temp1[0U];
  uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l3, h_20, o30);
  uint64_t temp0 = temp1[0U];
  uint64_t c0 = c3 + temp0;
  out[4U] = c0;
  uint64_t *b1 = out + (uint32_t)1U;
  uint64_t *temp2 = tb;
  uint64_t *tempBufferResult0 = tb + (uint32_t)1U;
  uint64_t f11 = f[1U];
  uint64_t f210 = f[2U];
  uint64_t f311 = f[3U];
  uint64_t *o00 = tempBufferResult0;
  uint64_t *o11 = tempBufferResult0 + (uint32_t)1U;
  uint64_t *o21 = tempBufferResult0 + (uint32_t)2U;
  uint64_t *o31 = tempBufferResult0 + (uint32_t)3U;
  o00[0U] = memory[0U];
  uint64_t h_01 = memory[1U];
  mul64(f11, f11, o11, temp2);
  uint64_t l4 = o11[0U];
  uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l4, h_01, o11);
  uint64_t h_11 = temp2[0U];
  mul64(f11, f210, o21, temp2);
  uint64_t l11 = o21[0U];
  memory[6U] = l11;
  memory[7U] = temp2[0U];
  uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l11, h_11, o21);
  uint64_t h_21 = temp2[0U];
  mul64(f11, f311, o31, temp2);
  uint64_t l20 = o31[0U];
  memory[8U] = l20;
  memory[9U] = temp2[0U];
  uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l20, h_21, o31);
  uint64_t h_30 = temp2[0U];
  uint64_t c40 = add4(tempBufferResult0, b1, b1);
  uint64_t c11 = c30 + h_30 + c40;
  out[5U] = c11;
  uint64_t *b2 = out + (uint32_t)2U;
  uint64_t *temp3 = tb;
  uint64_t *tempBufferResult1 = tb + (uint32_t)1U;
  uint64_t f21 = f[2U];
  uint64_t f312 = f[3U];
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
  uint64_t c41 = add4(tempBufferResult1, b2, b2);
  uint64_t c22 = c31 + h_31 + c41;
  out[6U] = c22;
  uint64_t *b3 = out + (uint32_t)3U;
  uint64_t *temp = tb;
  uint64_t *tempBufferResult = tb + (uint32_t)1U;
  uint64_t f31 = f[3U];
  uint64_t *o0 = tempBufferResult;
  uint64_t *o1 = tempBufferResult + (uint32_t)1U;
  uint64_t *o2 = tempBufferResult + (uint32_t)2U;
  uint64_t *o3 = tempBufferResult + (uint32_t)3U;
  o0[0U] = memory[4U];
  uint64_t h = memory[5U];
  o1[0U] = memory[8U];
  uint64_t l = o1[0U];
  uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l, h, o1);
  uint64_t h4 = memory[9U];
  o2[0U] = memory[10U];
  uint64_t l1 = o2[0U];
  uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l1, h4, o2);
  uint64_t h5 = memory[11U];
  mul64(f31, f31, o3, temp);
  uint64_t l2 = o3[0U];
  uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l2, h5, o3);
  uint64_t h_3 = temp[0U];
  uint64_t c4 = add4(tempBufferResult, b3, b3);
  uint64_t c33 = c32 + h_3 + c4;
  out[7U] = c33;
}

static void uploadZeroImpl(Spec_ECC_Curves_curve c, uint64_t *f)
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
    f[i] = (uint64_t)0U;
  }
}

static void uploadOneImpl(Spec_ECC_Curves_curve c, uint64_t *f)
{
  f[0U] = (uint64_t)1U;
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
    f[i] = (uint64_t)0U;
  }
}

static void uploadZeroPoint(Spec_ECC_Curves_curve c, uint64_t *p)
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
  uint64_t *x = p;
  uint64_t *y = p + len;
  uint64_t *z = p + (uint32_t)2U * len;
  uploadZeroImpl(c, x);
  uploadZeroImpl(c, y);
  uploadZeroImpl(c, z);
}

static uint64_t add_bn(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *y, uint64_t *result)
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
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return add4(x, y, result);
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x[(uint32_t)4U * i];
          uint64_t t20 = y[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len; i++)
        {
          uint64_t t1 = x[i];
          uint64_t t2 = y[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, result + i);
        }
        return c1;
      }
    case Spec_ECC_Curves_Default:
      {
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x[(uint32_t)4U * i];
          uint64_t t20 = y[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len; i++)
        {
          uint64_t t1 = x[i];
          uint64_t t2 = y[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, result + i);
        }
        return c1;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t
add_long_bn(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *y, uint64_t *result)
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
  uint32_t len = sw * (uint32_t)2U;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return add8(x, y, result);
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x[(uint32_t)4U * i];
          uint64_t t20 = y[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len; i++)
        {
          uint64_t t1 = x[i];
          uint64_t t2 = y[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, result + i);
        }
        return c1;
      }
    case Spec_ECC_Curves_Default:
      {
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x[(uint32_t)4U * i];
          uint64_t t20 = y[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len; i++)
        {
          uint64_t t1 = x[i];
          uint64_t t2 = y[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, result + i);
        }
        return c1;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t *const_to_ibuffer__uint64_t(const uint64_t *b)
{
  return (uint64_t *)b;
}

static uint64_t *const_to_ilbuffer__uint64_t(const uint64_t *b)
{
  return const_to_ibuffer__uint64_t(b);
}

static uint64_t
_add_dep_prime(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t t, uint64_t *result)
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
  uint64_t b[len];
  memset(b, 0U, len * sizeof (uint64_t));
  uint32_t unused;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        unused = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        unused = (uint32_t)6U;
        break;
      }
    default:
      {
        unused = (uint32_t)4U;
      }
  }
  const uint64_t *sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t carry = add_bn(c, const_to_ilbuffer__uint64_t(sw), x, b);
  uint64_t mask = (uint64_t)0U - t;
  copy_conditional(c, result, b, mask);
  return carry;
}

static uint64_t
add_dep_prime(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t t, uint64_t *result)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return _add_dep_prime(c, x, t, result);
      }
    case Spec_ECC_Curves_P384:
      {
        return add_dep_prime_p384(x, t, result);
      }
    case Spec_ECC_Curves_Default:
      {
        return _add_dep_prime(c, x, t, result);
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t sub_bn(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *y, uint64_t *result)
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
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return sub4(x, y, result);
      }
    case Spec_ECC_Curves_P384:
      {
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x[(uint32_t)4U * i];
          uint64_t t20 = y[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len; i++)
        {
          uint64_t t1 = x[i];
          uint64_t t2 = y[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, result + i);
        }
        return c1;
      }
    case Spec_ECC_Curves_Default:
      {
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = x[(uint32_t)4U * i];
          uint64_t t20 = y[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = x[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = y[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = x[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = y[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = x[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = y[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < len; i++)
        {
          uint64_t t1 = x[i];
          uint64_t t2 = y[i];
          c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, result + i);
        }
        return c1;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint64_t
sub_bn_gl(Spec_ECC_Curves_curve c, uint64_t *x, const uint64_t *y, uint64_t *result)
{
  uint32_t unused;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        unused = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        unused = (uint32_t)6U;
        break;
      }
    default:
      {
        unused = (uint32_t)4U;
      }
  }
  uint64_t *y_ = const_to_ilbuffer__uint64_t(y);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        return sub4_il(x, y, result);
      }
    case Spec_ECC_Curves_P384:
      {
        return sub_bn(c, x, y_, result);
      }
    case Spec_ECC_Curves_Default:
      {
        return sub_bn(c, x, y_, result);
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
_shortened_mul(Spec_ECC_Curves_curve c, const uint64_t *a, uint64_t b, uint64_t *result)
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
  uint64_t bBuffer = b;
  uint32_t unused;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        unused = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        unused = (uint32_t)6U;
        break;
      }
    default:
      {
        unused = (uint32_t)4U;
      }
  }
  uint64_t *a_ = const_to_ilbuffer__uint64_t(a);
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint32_t resLen = len + (uint32_t)1U;
        memset(result, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____0 = (&bBuffer)[0U];
          uint64_t *res_ = result;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, a_[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)1U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)2U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)3U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, a_[i], uu____0, res_ + i);
          }
          uint64_t r = c1;
          result[len + (uint32_t)0U] = r;
        }
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint32_t resLen = len + (uint32_t)1U;
        memset(result, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____1 = (&bBuffer)[0U];
          uint64_t *res_ = result;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, a_[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)1U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)2U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)3U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, a_[i], uu____1, res_ + i);
          }
          uint64_t r = c1;
          result[len + (uint32_t)0U] = r;
        }
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        uint32_t resLen = len + (uint32_t)1U;
        memset(result, 0U, resLen * sizeof (uint64_t));
        {
          uint64_t uu____2 = (&bBuffer)[0U];
          uint64_t *res_ = result;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, a_[(uint32_t)4U * i], uu____2, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)1U],
                uu____2,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)2U],
                uu____2,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                a_[(uint32_t)4U * i + (uint32_t)3U],
                uu____2,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, a_[i], uu____2, res_ + i);
          }
          uint64_t r = c1;
          result[len + (uint32_t)0U] = r;
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

static void
short_mul_bn(Spec_ECC_Curves_curve c, const uint64_t *x, uint64_t y, uint64_t *result)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint64_t *result04 = result;
        uint64_t temp = (uint64_t)0U;
        uint64_t f1 = x[1U];
        uint64_t f2 = x[2U];
        uint64_t f3 = x[3U];
        uint64_t *o0 = result04;
        uint64_t *o1 = result04 + (uint32_t)1U;
        uint64_t *o2 = result04 + (uint32_t)2U;
        uint64_t *o3 = result04 + (uint32_t)3U;
        uint64_t f01 = x[0U];
        mul64(f01, y, o0, &temp);
        uint64_t h0 = temp;
        mul64(f1, y, o1, &temp);
        uint64_t l0 = o1[0U];
        uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o1);
        uint64_t h1 = temp;
        mul64(f2, y, o2, &temp);
        uint64_t l1 = o2[0U];
        uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o2);
        uint64_t h = temp;
        mul64(f3, y, o3, &temp);
        uint64_t l = o3[0U];
        uint64_t c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l, h, o3);
        uint64_t temp0 = temp;
        uint64_t c10 = c3 + temp0;
        result[4U] = c10;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        _shortened_mul(c, x, y, result);
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        _shortened_mul(c, x, y, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void square_bn(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *result)
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
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        square_p256(x, result);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint32_t resLen = len + len;
        memset(result, 0U, resLen * sizeof (uint64_t));
        for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
        {
          uint64_t *uu____0 = x;
          uint64_t uu____1 = x[i0];
          uint64_t *res_ = result + i0;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = i0 / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 =
              mul_carry_add_u64_st(c1,
                uu____0[(uint32_t)4U * i],
                uu____1,
                res_ + (uint32_t)4U * i);
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
          result[i0 + i0] = r;
        }
        uint64_t c10 = (uint64_t)0U;
        uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
        {
          uint64_t t1 = result[(uint32_t)4U * i];
          uint64_t t20 = result[(uint32_t)4U * i];
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = result[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = result[(uint32_t)4U * i + (uint32_t)1U];
          c10 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c10,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = result[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = result[(uint32_t)4U * i + (uint32_t)2U];
          c10 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c10,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = result[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = result[(uint32_t)4U * i + (uint32_t)3U];
          c10 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c10,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k0; i < resLen; i++)
        {
          uint64_t t1 = result[i];
          uint64_t t2 = result[i];
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, result + i);
        }
        uint64_t uu____2 = c10;
        KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
        uint64_t tmp[resLen];
        memset(tmp, 0U, resLen * sizeof (uint64_t));
        for (uint32_t i = (uint32_t)0U; i < len; i++)
        {
          uint128_t a2 = (uint128_t)x[i] * x[i];
          tmp[(uint32_t)2U * i] = (uint64_t)a2;
          tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
        }
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = resLen / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = result[(uint32_t)4U * i];
          uint64_t t20 = tmp[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = result[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = result[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = result[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < resLen; i++)
        {
          uint64_t t1 = result[i];
          uint64_t t2 = tmp[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, result + i);
        }
        uint64_t uu____3 = c1;
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        uint32_t resLen = len + len;
        memset(result, 0U, resLen * sizeof (uint64_t));
        for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
        {
          uint64_t *uu____4 = x;
          uint64_t uu____5 = x[i0];
          uint64_t *res_ = result + i0;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = i0 / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 =
              mul_carry_add_u64_st(c1,
                uu____4[(uint32_t)4U * i],
                uu____5,
                res_ + (uint32_t)4U * i);
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
          for (uint32_t i = k; i < i0; i++)
          {
            c1 = mul_carry_add_u64_st(c1, uu____4[i], uu____5, res_ + i);
          }
          uint64_t r = c1;
          result[i0 + i0] = r;
        }
        uint64_t c10 = (uint64_t)0U;
        uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
        {
          uint64_t t1 = result[(uint32_t)4U * i];
          uint64_t t20 = result[(uint32_t)4U * i];
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = result[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = result[(uint32_t)4U * i + (uint32_t)1U];
          c10 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c10,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = result[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = result[(uint32_t)4U * i + (uint32_t)2U];
          c10 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c10,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = result[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = result[(uint32_t)4U * i + (uint32_t)3U];
          c10 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c10,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k0; i < resLen; i++)
        {
          uint64_t t1 = result[i];
          uint64_t t2 = result[i];
          c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, result + i);
        }
        uint64_t uu____6 = c10;
        KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
        uint64_t tmp[resLen];
        memset(tmp, 0U, resLen * sizeof (uint64_t));
        for (uint32_t i = (uint32_t)0U; i < len; i++)
        {
          uint128_t a2 = (uint128_t)x[i] * x[i];
          tmp[(uint32_t)2U * i] = (uint64_t)a2;
          tmp[(uint32_t)2U * i + (uint32_t)1U] = (uint64_t)(a2 >> (uint32_t)64U);
        }
        uint64_t c1 = (uint64_t)0U;
        uint32_t k = resLen / (uint32_t)4U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
        {
          uint64_t t1 = result[(uint32_t)4U * i];
          uint64_t t20 = tmp[(uint32_t)4U * i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, result + (uint32_t)4U * i);
          uint64_t t10 = result[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t t21 = tmp[(uint32_t)4U * i + (uint32_t)1U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t10,
              t21,
              result + (uint32_t)4U * i + (uint32_t)1U);
          uint64_t t11 = result[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = tmp[(uint32_t)4U * i + (uint32_t)2U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t11,
              t22,
              result + (uint32_t)4U * i + (uint32_t)2U);
          uint64_t t12 = result[(uint32_t)4U * i + (uint32_t)3U];
          uint64_t t2 = tmp[(uint32_t)4U * i + (uint32_t)3U];
          c1 =
            Lib_IntTypes_Intrinsics_add_carry_u64(c1,
              t12,
              t2,
              result + (uint32_t)4U * i + (uint32_t)3U);
        }
        for (uint32_t i = k; i < resLen; i++)
        {
          uint64_t t1 = result[i];
          uint64_t t2 = tmp[i];
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, result + i);
        }
        uint64_t uu____7 = c1;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
reduction_prime_2prime_with_carry_cin(
  Spec_ECC_Curves_curve c,
  uint64_t cin,
  uint64_t *x,
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
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t tempBufferForSubborrow = (uint64_t)0U;
  const uint64_t *sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t carry0 = sub_bn_gl(c, x, sw, tempBuffer);
  uint64_t
  carry =
    Lib_IntTypes_Intrinsics_sub_borrow_u64(carry0,
      cin,
      (uint64_t)0U,
      &tempBufferForSubborrow);
  cmovznz4(c, carry, tempBuffer, x, result);
}

static void
reduction_prime_2prime_with_carry(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *result)
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
  uint64_t cin = x[len];
  uint64_t *x_ = x;
  reduction_prime_2prime_with_carry_cin(c, cin, x_, result);
}

static void reduction_prime_2prime(Spec_ECC_Curves_curve c, uint64_t *x, uint64_t *result)
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
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  const uint64_t *sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t r = sub_bn_gl(c, x, sw, tempBuffer);
  cmovznz4(c, r, tempBuffer, x, result);
}

static void felem_add(Spec_ECC_Curves_curve c, uint64_t *arg1, uint64_t *arg2, uint64_t *out)
{
  uint64_t t = add_bn(c, arg1, arg2, out);
  reduction_prime_2prime_with_carry_cin(c, t, out, out);
}

static void felem_double(Spec_ECC_Curves_curve c, uint64_t *arg1, uint64_t *out)
{
  uint64_t t = add_bn(c, arg1, arg1, out);
  reduction_prime_2prime_with_carry_cin(c, t, out, out);
}

static void felem_sub(Spec_ECC_Curves_curve c, uint64_t *arg1, uint64_t *arg2, uint64_t *out)
{
  uint64_t t = sub_bn(c, arg1, arg2, out);
  uint64_t cc = add_dep_prime(c, out, t, out);
}

static void mul(Spec_ECC_Curves_curve c, uint64_t *f, uint64_t *r, uint64_t *out)
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
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        uint64_t f0 = f[0U];
        uint64_t f1 = f[1U];
        uint64_t f2 = f[2U];
        uint64_t f3 = f[3U];
        uint64_t *b0 = out;
        uint64_t temp2 = (uint64_t)0U;
        uint64_t f110 = r[1U];
        uint64_t f210 = r[2U];
        uint64_t f310 = r[3U];
        uint64_t *o00 = b0;
        uint64_t *o10 = b0 + (uint32_t)1U;
        uint64_t *o20 = b0 + (uint32_t)2U;
        uint64_t *o30 = b0 + (uint32_t)3U;
        uint64_t f020 = r[0U];
        mul64(f020, f0, o00, &temp2);
        uint64_t h0 = temp2;
        mul64(f110, f0, o10, &temp2);
        uint64_t l0 = o10[0U];
        uint64_t c1 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l0, h0, o10);
        uint64_t h1 = temp2;
        mul64(f210, f0, o20, &temp2);
        uint64_t l1 = o20[0U];
        uint64_t c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, l1, h1, o20);
        uint64_t h2 = temp2;
        mul64(f310, f0, o30, &temp2);
        uint64_t l2 = o30[0U];
        uint64_t c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, l2, h2, o30);
        uint64_t temp00 = temp2;
        uint64_t c0 = c30 + temp00;
        out[4U] = c0;
        uint64_t *b1 = out + (uint32_t)1U;
        uint64_t temp3[4U] = { 0U };
        uint64_t temp10 = (uint64_t)0U;
        uint64_t f111 = r[1U];
        uint64_t f211 = r[2U];
        uint64_t f311 = r[3U];
        uint64_t *o01 = temp3;
        uint64_t *o11 = temp3 + (uint32_t)1U;
        uint64_t *o21 = temp3 + (uint32_t)2U;
        uint64_t *o31 = temp3 + (uint32_t)3U;
        uint64_t f021 = r[0U];
        mul64(f021, f1, o01, &temp10);
        uint64_t h3 = temp10;
        mul64(f111, f1, o11, &temp10);
        uint64_t l3 = o11[0U];
        uint64_t c10 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l3, h3, o11);
        uint64_t h4 = temp10;
        mul64(f211, f1, o21, &temp10);
        uint64_t l4 = o21[0U];
        uint64_t c20 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, l4, h4, o21);
        uint64_t h5 = temp10;
        mul64(f311, f1, o31, &temp10);
        uint64_t l5 = o31[0U];
        uint64_t c32 = Lib_IntTypes_Intrinsics_add_carry_u64(c20, l5, h5, o31);
        uint64_t temp01 = temp10;
        uint64_t c11 = c32 + temp01;
        uint64_t c33 = add4(temp3, b1, b1);
        uint64_t c12 = c11 + c33;
        out[5U] = c12;
        uint64_t *b2 = out + (uint32_t)2U;
        uint64_t temp4[4U] = { 0U };
        uint64_t temp11 = (uint64_t)0U;
        uint64_t f112 = r[1U];
        uint64_t f212 = r[2U];
        uint64_t f312 = r[3U];
        uint64_t *o02 = temp4;
        uint64_t *o12 = temp4 + (uint32_t)1U;
        uint64_t *o22 = temp4 + (uint32_t)2U;
        uint64_t *o32 = temp4 + (uint32_t)3U;
        uint64_t f022 = r[0U];
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
        uint64_t c34 = Lib_IntTypes_Intrinsics_add_carry_u64(c21, l8, h8, o32);
        uint64_t temp02 = temp11;
        uint64_t c22 = c34 + temp02;
        uint64_t c3 = add4(temp4, b2, b2);
        uint64_t c23 = c22 + c3;
        out[6U] = c23;
        uint64_t *b3 = out + (uint32_t)3U;
        uint64_t temp[4U] = { 0U };
        uint64_t temp1 = (uint64_t)0U;
        uint64_t f11 = r[1U];
        uint64_t f21 = r[2U];
        uint64_t f31 = r[3U];
        uint64_t *o0 = temp;
        uint64_t *o1 = temp + (uint32_t)1U;
        uint64_t *o2 = temp + (uint32_t)2U;
        uint64_t *o3 = temp + (uint32_t)3U;
        uint64_t f02 = r[0U];
        mul64(f02, f3, o0, &temp1);
        uint64_t h9 = temp1;
        mul64(f11, f3, o1, &temp1);
        uint64_t l9 = o1[0U];
        uint64_t c111 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, l9, h9, o1);
        uint64_t h10 = temp1;
        mul64(f21, f3, o2, &temp1);
        uint64_t l10 = o2[0U];
        uint64_t c210 = Lib_IntTypes_Intrinsics_add_carry_u64(c111, l10, h10, o2);
        uint64_t h = temp1;
        mul64(f31, f3, o3, &temp1);
        uint64_t l = o3[0U];
        uint64_t c35 = Lib_IntTypes_Intrinsics_add_carry_u64(c210, l, h, o3);
        uint64_t temp0 = temp1;
        uint64_t c36 = c35 + temp0;
        uint64_t c31 = add4(temp, b3, b3);
        uint64_t c37 = c36 + c31;
        out[7U] = c37;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        uint32_t resLen = len + len;
        memset(out, 0U, resLen * sizeof (uint64_t));
        for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
        {
          uint64_t uu____0 = r[i0];
          uint64_t *res_ = out + i0;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, f[(uint32_t)4U * i], uu____0, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                f[(uint32_t)4U * i + (uint32_t)1U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                f[(uint32_t)4U * i + (uint32_t)2U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                f[(uint32_t)4U * i + (uint32_t)3U],
                uu____0,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, f[i], uu____0, res_ + i);
          }
          uint64_t r1 = c1;
          out[len + i0] = r1;
        }
        break;
      }
    case Spec_ECC_Curves_Default:
      {
        uint32_t resLen = len + len;
        memset(out, 0U, resLen * sizeof (uint64_t));
        for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
        {
          uint64_t uu____1 = r[i0];
          uint64_t *res_ = out + i0;
          uint64_t c1 = (uint64_t)0U;
          uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
          {
            c1 = mul_carry_add_u64_st(c1, f[(uint32_t)4U * i], uu____1, res_ + (uint32_t)4U * i);
            c1 =
              mul_carry_add_u64_st(c1,
                f[(uint32_t)4U * i + (uint32_t)1U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)1U);
            c1 =
              mul_carry_add_u64_st(c1,
                f[(uint32_t)4U * i + (uint32_t)2U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)2U);
            c1 =
              mul_carry_add_u64_st(c1,
                f[(uint32_t)4U * i + (uint32_t)3U],
                uu____1,
                res_ + (uint32_t)4U * i + (uint32_t)3U);
          }
          for (uint32_t i = k; i < len; i++)
          {
            c1 = mul_carry_add_u64_st(c1, f[i], uu____1, res_ + i);
          }
          uint64_t r1 = c1;
          out[len + i0] = r1;
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

static uint64_t isZero_uint64_CT(Spec_ECC_Curves_curve c, uint64_t *f)
{
  uint64_t tmp = (uint64_t)18446744073709551615U;
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
    uint64_t a_i = f[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, (uint64_t)0U);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  return tmp;
}

static uint64_t compare_felem(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *b)
{
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
    uint64_t a_i = a[i];
    uint64_t b_i = b[i];
    uint64_t r_i = FStar_UInt64_eq_mask(a_i, b_i);
    uint64_t tmp0 = tmp;
    tmp = r_i & tmp0;
  }
  return tmp;
}

static void shiftLeftWord(Spec_ECC_Curves_curve c, uint64_t *i, uint64_t *o)
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
  for (uint32_t i0 = len; i0 < (uint32_t)2U * len; i0++)
  {
    uint64_t i_i = i[i0 - len];
    o[i0] = i_i;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    o[i0] = (uint64_t)0U;
  }
}

static void
shift1_with_carry(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *out, uint64_t carry)
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
  uint32_t len = sw * (uint32_t)2U - (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t elem = t[(uint32_t)1U + i];
    out[i] = elem;
  }
  out[len] = carry;
}

static void mul_atomic(uint64_t x, uint64_t y, uint64_t *result, uint64_t *temp)
{
  uint128_t res = (uint128_t)x * y;
  uint64_t l0 = (uint64_t)res;
  uint64_t h0 = (uint64_t)(res >> (uint32_t)64U);
  result[0U] = l0;
  temp[0U] = h0;
}

static void
montgomery_multiplication_round_w_k0(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *t2)
{
  uint64_t t1 = t[0U];
  const uint64_t *sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  short_mul_bn(c, sw, t1, t2);
}

static void
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
  mul_atomic(t1, k0, &y, &temp);
  uint64_t y_ = y;
  const uint64_t *sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  short_mul_bn(c, sw, y_, t2);
}

static void
montgomery_multiplication_round_(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *t2)
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
  bool r = sw == (uint64_t)0xffffffffffffffffU;
  if (r)
  {
    montgomery_multiplication_round_w_k0(c, t, t2);
    return;
  }
  uint64_t k0 = getK0(c);
  montgomery_multiplication_round_k0(c, k0, t, t2);
}

static void
montgomery_multiplication_round(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *round)
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
  uint64_t t2[(uint32_t)2U * len];
  memset(t2, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  montgomery_multiplication_round_(c, t, t2);
  uint64_t carry = add_long_bn(c, t, t2, t2);
  shift1_with_carry(c, t2, round, carry);
}

static void
montgomery_multiplication_reduction(Spec_ECC_Curves_curve c, uint64_t *t, uint64_t *result)
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
    montgomery_multiplication_round(c, t, t);
  }
  reduction_prime_2prime_with_carry(c, t, result);
}

static void
montgomery_multiplication_buffer_by_one(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
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
  montgomery_multiplication_reduction(c, t, result);
}

static void
montgomery_multiplication_buffer(
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
  mul(c, a, b, t);
  montgomery_multiplication_reduction(c, t, result);
}

static void montgomery_square_buffer(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
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
  square_bn(c, a, t);
  montgomery_multiplication_reduction(c, t, result);
}

static void fsquarePowN(Spec_ECC_Curves_curve c, uint32_t n, uint64_t *a)
{
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    montgomery_square_buffer(c, a, a);
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

static void
montgomery_ladder_power_step(
  Spec_ECC_Curves_curve c,
  uint64_t *a,
  uint64_t *b,
  const uint8_t *scalar,
  uint32_t i
)
{
  uint32_t bit0 = Spec_ECC_Curves_getScalarLenBytes(c) * (uint32_t)8U - (uint32_t)1U - i;
  uint64_t bit = (uint64_t)(scalar[bit0 / (uint32_t)8U] >> bit0 % (uint32_t)8U & (uint8_t)1U);
  cswap(c, bit, a, b);
  montgomery_multiplication_buffer(c, a, b, b);
  montgomery_square_buffer(c, a, a);
  cswap(c, bit, a, b);
}

static void
_montgomery_ladder_power(
  Spec_ECC_Curves_curve c,
  uint64_t *a,
  uint64_t *b,
  const uint8_t *scalar
)
{
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLenBytes(c) * (uint32_t)8U;
  for (uint32_t i = (uint32_t)0U; i < scalarLen; i++)
  {
    montgomery_ladder_power_step(c, a, b, scalar, i);
  }
}

static void
montgomery_ladder_power(
  Spec_ECC_Curves_curve c,
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
    case Spec_ECC_Curves_Default:
      {
        reduction_prime_2prime_with_carry_cin(c, (uint64_t)1U, p, p);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  _montgomery_ladder_power(c, p, a, scalar);
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
  montgomery_square_buffer(Spec_ECC_Curves_P384, t, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t, t0, t0);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t0, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t, t0, t0);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t0, t1);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)2U, t1);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t0, t1, t1);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t1, t2);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)5U, t2);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t2, t1, t2);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t2, t3);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)11U, t3);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t2, t3, t2);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)6U, t2);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t2, t1, t1);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t1, t2);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t2, t, t2);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t2, t3);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t, t3, t3);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t3, t4);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)30U, t4);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t2, t4);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t4, t5);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)62U, t5);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t5, t4);
  montgomery_square_buffer(Spec_ECC_Curves_P384, t4, t5);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)125U, t5);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t5, t4);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)3U, t4);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t0, t4);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)33U, t4);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t3, t4);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)94U, t4);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t1, t4);
  fsquarePowN(Spec_ECC_Curves_P384, (uint32_t)2U, t4);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P384, t4, t, result);
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
  montgomery_square_buffer(Spec_ECC_Curves_P256, t, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t, t2);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t2, t0);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t0, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t2, t6);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t6, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)3U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t6, t7);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t7, t0);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t0, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t2, t1);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t1, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)9U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t1, t3);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t3, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)9U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t1, t4);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t4, t0);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t0, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t2, t5);
  montgomery_square_buffer(Spec_ECC_Curves_P256, t5, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)31U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)128U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t5, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)32U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t5, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)30U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t4, t0);
  fsquarePowN(Spec_ECC_Curves_P256, (uint32_t)2U, t0);
  montgomery_multiplication_buffer(Spec_ECC_Curves_P256, t0, t, result);
}

static void
exponent(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result, uint64_t *tempBuffer)
{
  switch (c)
  {
    case Spec_ECC_Curves_P384:
      {
        exponent_p384(a, result, tempBuffer);
        break;
      }
    case Spec_ECC_Curves_P256:
      {
        exponent_p256(a, result, tempBuffer);
        break;
      }
    case Spec_ECC_Curves_Default:
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
              KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        montgomery_ladder_power(c, a, sw, result);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void toUint8(Spec_ECC_Curves_curve c, uint64_t *i, uint8_t *o)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        {
          store64_be(o + (uint32_t)0U * (uint32_t)8U, i[0U]);
        }
        {
          store64_be(o + (uint32_t)1U * (uint32_t)8U, i[1U]);
        }
        {
          store64_be(o + (uint32_t)2U * (uint32_t)8U, i[2U]);
        }
        {
          store64_be(o + (uint32_t)3U * (uint32_t)8U, i[3U]);
        }
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        {
          store64_be(o + (uint32_t)0U * (uint32_t)8U, i[0U]);
        }
        {
          store64_be(o + (uint32_t)1U * (uint32_t)8U, i[1U]);
        }
        {
          store64_be(o + (uint32_t)2U * (uint32_t)8U, i[2U]);
        }
        {
          store64_be(o + (uint32_t)3U * (uint32_t)8U, i[3U]);
        }
        {
          store64_be(o + (uint32_t)4U * (uint32_t)8U, i[4U]);
        }
        {
          store64_be(o + (uint32_t)5U * (uint32_t)8U, i[5U]);
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

static void changeEndian(Spec_ECC_Curves_curve c, uint64_t *b)
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
  uint32_t lenByTwo = len >> (uint32_t)1U;
  for (uint32_t i = (uint32_t)0U; i < lenByTwo; i++)
  {
    uint64_t left = b[i];
    uint32_t rightIndex = len - (uint32_t)1U - i;
    uint64_t right = b[rightIndex];
    b[i] = right;
    b[rightIndex] = left;
  }
}

static void toUint64CEP256(uint8_t *i, uint64_t *o)
{
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)0U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[0U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)1U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[1U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)2U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[2U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)3U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[3U] = x;
  }
  changeEndian(Spec_ECC_Curves_P256, o);
}

static void toUint64CEP384(uint8_t *i, uint64_t *o)
{
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)0U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[0U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)1U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[1U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)2U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[2U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)3U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[3U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)4U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[4U] = x;
  }
  {
    uint64_t *os = o;
    uint8_t *bj = i + (uint32_t)5U * (uint32_t)8U;
    uint64_t u = load64_be(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[5U] = x;
  }
  changeEndian(Spec_ECC_Curves_P384, o);
}

static void toUint64ChangeEndian(Spec_ECC_Curves_curve c, uint8_t *i, uint64_t *o)
{
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        toUint64CEP256(i, o);
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        toUint64CEP384(i, o);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void multByTwo(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *out)
{
  felem_add(c, a, a, out);
}

static void multByThree(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
{
  multByTwo(c, a, result);
  felem_add(c, a, result, result);
}

static void multByFour(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
{
  multByTwo(c, a, result);
  multByTwo(c, result, result);
}

static void multByEight(Spec_ECC_Curves_curve c, uint64_t *a, uint64_t *result)
{
  multByTwo(c, a, result);
  multByTwo(c, result, result);
  multByTwo(c, result, result);
}

static void
point_double_a_b_g(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *alpha,
  uint64_t *beta,
  uint64_t *gamma,
  uint64_t *delta,
  uint64_t *tempBuffer
)
{
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
  uint64_t *pX = p;
  uint64_t *pY = p + coordinateLen;
  uint64_t *pZ = p + (uint32_t)2U * coordinateLen;
  uint64_t *a0 = tempBuffer;
  uint64_t *a1 = tempBuffer + coordinateLen;
  uint64_t *alpha0 = tempBuffer + (uint32_t)2U * coordinateLen;
  montgomery_square_buffer(c, pZ, delta);
  montgomery_square_buffer(c, pY, gamma);
  montgomery_multiplication_buffer(c, pX, gamma, beta);
  felem_sub(c, pX, delta, a0);
  felem_add(c, pX, delta, a1);
  montgomery_multiplication_buffer(c, a0, a1, alpha0);
  multByThree(c, alpha0, alpha);
}

static void
point_double_x3(
  Spec_ECC_Curves_curve c,
  uint64_t *x3,
  uint64_t *alpha,
  uint64_t *fourBeta,
  uint64_t *beta,
  uint64_t *eightBeta
)
{
  montgomery_square_buffer(c, alpha, x3);
  multByFour(c, beta, fourBeta);
  multByTwo(c, fourBeta, eightBeta);
  felem_sub(c, x3, eightBeta, x3);
}

static void
point_double_z3(
  Spec_ECC_Curves_curve c,
  uint64_t *z3,
  uint64_t *pY,
  uint64_t *pZ,
  uint64_t *gamma,
  uint64_t *delta
)
{
  felem_add(c, pY, pZ, z3);
  montgomery_square_buffer(c, z3, z3);
  felem_sub(c, z3, gamma, z3);
  felem_sub(c, z3, delta, z3);
}

static void
point_double_y3(
  Spec_ECC_Curves_curve c,
  uint64_t *y3,
  uint64_t *x3,
  uint64_t *alpha,
  uint64_t *gamma,
  uint64_t *eightGamma,
  uint64_t *fourBeta
)
{
  felem_sub(c, fourBeta, x3, y3);
  montgomery_multiplication_buffer(c, alpha, y3, y3);
  montgomery_square_buffer(c, gamma, gamma);
  multByEight(c, gamma, eightGamma);
  felem_sub(c, y3, eightGamma, y3);
}

static void
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
  point_double_a_b_g(c, p, alpha, beta, gamma, delta, tmp);
  point_double_x3(c, x3, alpha, fourBeta, beta, eightBeta);
  point_double_z3(c, z3, pY, pZ, gamma, delta);
  point_double_y3(c, y3, x3, alpha, gamma, eightGamma, fourBeta);
}

static void
copy_point_conditional(
  Spec_ECC_Curves_curve c,
  uint64_t *x3_out,
  uint64_t *y3_out,
  uint64_t *z3_out,
  uint64_t *p,
  uint64_t *maskPoint
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
  uint64_t mask = isZero_uint64_CT(c, z);
  uint64_t *p_x = p;
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
  uint64_t *p_y = p + sw1;
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
  copy_conditional(c, x3_out, p_x, mask);
  copy_conditional(c, y3_out, p_y, mask);
  copy_conditional(c, z3_out, p_z, mask);
}

static void compute_common_params_point_add(Spec_ECC_Curves_curve c, uint64_t *t12)
{
  uint64_t *t4 = t12;
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
  uint64_t *u1 = t12 + (uint32_t)4U * sw0;
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
  uint64_t *u2 = t12 + (uint32_t)5U * sw1;
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
  uint64_t *s1 = t12 + (uint32_t)6U * sw2;
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
  uint64_t *s2 = t12 + (uint32_t)7U * sw3;
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
  uint64_t *h = t12 + (uint32_t)8U * sw4;
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
  uint64_t *r = t12 + (uint32_t)9U * sw5;
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
  uint64_t *uh = t12 + (uint32_t)10U * sw6;
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
  uint64_t *hCube = t12 + (uint32_t)11U * sw;
  uint64_t *temp = t4;
  felem_sub(c, u2, u1, h);
  felem_sub(c, s2, s1, r);
  montgomery_square_buffer(c, h, temp);
  montgomery_multiplication_buffer(c, temp, u1, uh);
  montgomery_multiplication_buffer(c, temp, h, hCube);
}

static void
computex3_point_add(
  Spec_ECC_Curves_curve c,
  uint64_t *hCube,
  uint64_t *uh,
  uint64_t *r,
  uint64_t *t4
)
{
  uint64_t *x3 = t4;
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
  uint64_t *tempBuffer3 = t4 + sw0;
  uint64_t *rSquare = tempBuffer3;
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
  uint64_t *rH = tempBuffer3 + sw1;
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
  uint64_t *twoUh = tempBuffer3 + (uint32_t)2U * sw;
  montgomery_square_buffer(c, r, rSquare);
  felem_sub(c, rSquare, hCube, rH);
  multByTwo(c, uh, twoUh);
  felem_sub(c, rH, twoUh, x3);
}

static void
computeY3_point_add(
  Spec_ECC_Curves_curve c,
  uint64_t *s1,
  uint64_t *hCube,
  uint64_t *uh,
  uint64_t *r,
  uint64_t *tempBuffer5
)
{
  uint64_t *x3 = tempBuffer5;
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
  uint64_t *y3 = tempBuffer5 + sw0;
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
  uint64_t *tempBuffer3 = tempBuffer5 + (uint32_t)2U * sw1;
  uint64_t *s1hCube = tempBuffer3;
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
  uint64_t *u1hx3 = tempBuffer3 + sw2;
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
  uint64_t *ru1hx3 = tempBuffer3 + (uint32_t)2U * sw;
  montgomery_multiplication_buffer(c, s1, hCube, s1hCube);
  felem_sub(c, uh, x3, u1hx3);
  montgomery_multiplication_buffer(c, u1hx3, r, ru1hx3);
  felem_sub(c, ru1hx3, s1hCube, y3);
}

static void
copy_result_point_add(
  Spec_ECC_Curves_curve c,
  uint64_t *t5,
  uint64_t *p,
  uint64_t *q,
  uint64_t *result
)
{
  uint64_t *x3_out = t5;
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
  uint64_t *y3_out = t5 + sw0;
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
  uint64_t *z3_out = t5 + (uint32_t)2U * sw1;
  copy_point_conditional(c, x3_out, y3_out, z3_out, q, p);
  copy_point_conditional(c, x3_out, y3_out, z3_out, p, q);
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
  memcpy(result, x3_out, sw2 * sizeof (uint64_t));
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
  memcpy(result + sw3, y3_out, sw4 * sizeof (uint64_t));
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
  memcpy(result + sw5 + sw6, z3_out, sw * sizeof (uint64_t));
}

static void
computeXY(
  Spec_ECC_Curves_curve c,
  uint64_t *hCube,
  uint64_t *uh,
  uint64_t *r,
  uint64_t *t5,
  uint64_t *s1
)
{
  computex3_point_add(c, hCube, uh, r, t5);
  computeY3_point_add(c, s1, hCube, uh, r, t5);
}

static void
computeXYZ(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *q,
  uint64_t *hCube,
  uint64_t *uh,
  uint64_t *r,
  uint64_t *t5,
  uint64_t *s1,
  uint64_t *h
)
{
  computeXY(c, hCube, uh, r, t5, s1);
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
  uint64_t *z1 = p + (uint32_t)2U * sw0;
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
  uint64_t *z2 = q + (uint32_t)2U * sw1;
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
  uint64_t *z3 = t5 + (uint32_t)2U * sw2;
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
  uint64_t *t1 = t5 + (uint32_t)3U * sw;
  uint64_t *z1z2 = t1;
  montgomery_multiplication_buffer(c, z1, z2, z1z2);
  montgomery_multiplication_buffer(c, z1z2, h, z3);
}

static void
__point_add_if_second_branch_impl(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  uint64_t *q,
  uint64_t *s1,
  uint64_t *r,
  uint64_t *h,
  uint64_t *uh,
  uint64_t *hCube,
  uint64_t *t5
)
{
  computeXYZ(c, p, q, hCube, uh, r, t5, s1, h);
  copy_result_point_add(c, t5, p, q, result);
}

static void
_point_add_if_second_branch_impl(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  uint64_t *q,
  uint64_t *x3y3z3u1u2s1s2,
  uint64_t *r,
  uint64_t *h,
  uint64_t *uh,
  uint64_t *hCube,
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
  uint64_t *u1 = x3y3z3u1u2s1s2 + (uint32_t)4U * sw0;
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
  uint64_t *u2 = x3y3z3u1u2s1s2 + (uint32_t)5U * sw1;
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
  uint64_t *s1 = x3y3z3u1u2s1s2 + (uint32_t)6U * sw2;
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
  uint64_t *s2 = x3y3z3u1u2s1s2 + (uint32_t)7U * sw;
  __point_add_if_second_branch_impl(c, result, p, q, s1, r, h, uh, hCube, t5);
}

static void
_point_add_if_second_branch_impl0(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  uint64_t *q,
  uint64_t *x3y3z3u1u2s1s2,
  uint64_t *rhuhhCube,
  uint64_t *tempBuffer5
)
{
  uint64_t *h = rhuhhCube;
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
  uint64_t *r = rhuhhCube + sw0;
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
  uint64_t *uh = rhuhhCube + (uint32_t)2U * sw1;
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
  uint64_t *hCube = rhuhhCube + (uint32_t)3U * sw;
  _point_add_if_second_branch_impl(c,
    result,
    p,
    q,
    x3y3z3u1u2s1s2,
    r,
    h,
    uh,
    hCube,
    tempBuffer5);
}

static void
_point_add_if_second_branch_impl1(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint64_t *p,
  uint64_t *q,
  uint64_t *x3hCube,
  uint64_t *t5
)
{
  uint64_t *x3y3z3u1u2s1s2 = x3hCube;
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
  uint64_t *rhuhhCube = x3hCube + (uint32_t)8U * sw;
  _point_add_if_second_branch_impl0(c, result, p, q, x3y3z3u1u2s1s2, rhuhhCube, t5);
}

static void _point_add_0(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *q, uint64_t *t12)
{
  uint64_t *t4 = t12;
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
  uint64_t *u1 = t12 + (uint32_t)4U * sw0;
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
  uint64_t *u2 = t12 + (uint32_t)5U * sw1;
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
  uint64_t *s1 = t12 + (uint32_t)6U * sw2;
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
  uint64_t *s2 = t12 + (uint32_t)7U * sw3;
  uint64_t *pX = p;
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
  uint64_t *pY = p + sw4;
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
  uint64_t *pZ = p + (uint32_t)2U * sw5;
  uint64_t *qX = q;
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
  uint64_t *qY = q + sw6;
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
  uint64_t *qZ = q + (uint32_t)2U * sw7;
  uint64_t *z2Square = t4;
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
  uint64_t *z1Square = t4 + sw8;
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
  uint64_t *z2Cube = t4 + (uint32_t)2U * sw9;
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
  uint64_t *z1Cube = t4 + (uint32_t)3U * sw;
  montgomery_square_buffer(c, qZ, z2Square);
  montgomery_square_buffer(c, pZ, z1Square);
  montgomery_multiplication_buffer(c, z2Square, qZ, z2Cube);
  montgomery_multiplication_buffer(c, z1Square, pZ, z1Cube);
  montgomery_multiplication_buffer(c, z2Square, pX, u1);
  montgomery_multiplication_buffer(c, z1Square, qX, u2);
  montgomery_multiplication_buffer(c, z2Cube, pY, s1);
  montgomery_multiplication_buffer(c, z1Cube, qY, s2);
  compute_common_params_point_add(c, t12);
}

static void
point_add(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *q,
  uint64_t *result,
  uint64_t *tempBuffer
)
{
  uint64_t *t12 = tempBuffer;
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
  uint64_t *t5 = tempBuffer + (uint32_t)12U * sw;
  _point_add_0(c, p, q, t12);
  _point_add_if_second_branch_impl1(c, result, p, q, t12, t5);
}

static uint32_t coordinate521 = (uint32_t)9U;

extern void Hacl_Impl_EC_P521_Reduction_felem_add(uint64_t *a, uint64_t *b, uint64_t *out);

static void getZeroWord(uint64_t *i, uint64_t *o)
{
  memcpy(o, i, coordinate521 * sizeof (uint64_t));
  uint64_t o8 = o[8U];
  uint64_t o8Updated = (uint64_t)0x00000000000002ffU & o8;
  o[8U] = o8Updated;
}

static void getFirstWord(uint64_t *i, uint64_t *o)
{
  uint64_t flag0 = (uint64_t)0xfffffffffffffd00U;
  uint64_t flag1 = (uint64_t)0x00000000000002ffU;
  uint64_t i0 = i[9U];
  uint64_t i1 = i[10U];
  uint64_t i0_ = i0 & flag0;
  uint64_t i1_ = i1 & flag1;
  uint64_t o0 = i0_ ^ i1_;
  o[0U] = o0;
}

static void reduction_p521(uint64_t *i, uint64_t *o)
{
  uint64_t a0[9U] = { 0U };
  uint64_t a1[9U] = { 0U };
  uint64_t a2[9U] = { 0U };
  getZeroWord(i, a0);
  getFirstWord(i, a1);
  getFirstWord(i, a2);
  Hacl_Impl_EC_P521_Reduction_felem_add(a0, a1, o);
  Hacl_Impl_EC_P521_Reduction_felem_add(o, a2, o);
}

static uint64_t store_high_low_u(uint32_t high, uint32_t low)
{
  uint64_t as_uint64_high = (uint64_t)high;
  uint64_t as_uint64_high1 = as_uint64_high << (uint32_t)32U;
  uint64_t as_uint64_low = (uint64_t)low;
  return as_uint64_low ^ as_uint64_high1;
}

static void
upl_zer_buffer(
  uint32_t c0,
  uint32_t c1,
  uint32_t c2,
  uint32_t c3,
  uint32_t c4,
  uint32_t c5,
  uint32_t c6,
  uint32_t c7,
  uint32_t c8,
  uint32_t c9,
  uint32_t c10,
  uint32_t c11,
  uint64_t *o
)
{
  uint64_t a0 = store_high_low_u(c1, c0);
  uint64_t a1 = store_high_low_u(c3, c2);
  uint64_t a2 = store_high_low_u(c5, c4);
  uint64_t a3 = store_high_low_u(c7, c6);
  uint64_t a4 = store_high_low_u(c9, c8);
  uint64_t a5 = store_high_low_u(c11, c10);
  o[0U] = a0;
  o[1U] = a1;
  o[2U] = a2;
  o[3U] = a3;
  o[4U] = a4;
  o[5U] = a5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void upl_fir_buffer(uint32_t c21, uint32_t c22, uint32_t c23, uint64_t *o)
{
  uint64_t b0 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b1 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c22, c21);
  uint64_t b3 = store_high_low_u((uint32_t)0U, c23);
  uint64_t b4 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b5 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
}

static void
upl_sec_buffer(
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint32_t c16,
  uint32_t c17,
  uint32_t c18,
  uint32_t c19,
  uint32_t c20,
  uint32_t c21,
  uint32_t c22,
  uint32_t c23,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c13, c12);
  uint64_t b1 = store_high_low_u(c15, c14);
  uint64_t b2 = store_high_low_u(c17, c16);
  uint64_t b3 = store_high_low_u(c19, c18);
  uint64_t b4 = store_high_low_u(c21, c20);
  uint64_t b5 = store_high_low_u(c23, c22);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void
upl_thi_buffer(
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint32_t c16,
  uint32_t c17,
  uint32_t c18,
  uint32_t c19,
  uint32_t c20,
  uint32_t c21,
  uint32_t c22,
  uint32_t c23,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c22, c21);
  uint64_t b1 = store_high_low_u(c12, c23);
  uint64_t b2 = store_high_low_u(c14, c13);
  uint64_t b3 = store_high_low_u(c16, c15);
  uint64_t b4 = store_high_low_u(c18, c17);
  uint64_t b5 = store_high_low_u(c20, c19);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void
upl_forth_buffer(
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint32_t c16,
  uint32_t c17,
  uint32_t c18,
  uint32_t c19,
  uint32_t c20,
  uint32_t c23,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c23, (uint32_t)0U);
  uint64_t b1 = store_high_low_u(c20, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c13, c12);
  uint64_t b3 = store_high_low_u(c15, c14);
  uint64_t b4 = store_high_low_u(c17, c16);
  uint64_t b5 = store_high_low_u(c19, c18);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void upl_fif_buffer(uint32_t c20, uint32_t c21, uint32_t c22, uint32_t c23, uint64_t *o)
{
  uint64_t b0 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b1 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c21, c20);
  uint64_t b3 = store_high_low_u(c23, c22);
  uint64_t b4 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b5 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void upl_six_buffer(uint32_t c20, uint32_t c21, uint32_t c22, uint32_t c23, uint64_t *o)
{
  uint64_t b0 = store_high_low_u((uint32_t)0U, c20);
  uint64_t b1 = store_high_low_u(c21, (uint32_t)0U);
  uint64_t b2 = store_high_low_u(c23, c22);
  uint64_t b3 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b4 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b5 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void
upl_sev_buffer(
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint32_t c16,
  uint32_t c17,
  uint32_t c18,
  uint32_t c19,
  uint32_t c20,
  uint32_t c21,
  uint32_t c22,
  uint32_t c23,
  uint64_t *o
)
{
  uint64_t b0 = store_high_low_u(c12, c23);
  uint64_t b1 = store_high_low_u(c14, c13);
  uint64_t b2 = store_high_low_u(c16, c15);
  uint64_t b3 = store_high_low_u(c18, c17);
  uint64_t b4 = store_high_low_u(c20, c19);
  uint64_t b5 = store_high_low_u(c22, c21);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void upl_eit_buffer(uint32_t c20, uint32_t c21, uint32_t c22, uint32_t c23, uint64_t *o)
{
  uint64_t b0 = store_high_low_u(c20, (uint32_t)0U);
  uint64_t b1 = store_high_low_u(c22, c21);
  uint64_t b2 = store_high_low_u((uint32_t)0U, c23);
  uint64_t b3 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b4 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b5 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void upl_nin_buffer(uint32_t c23, uint64_t *o)
{
  uint64_t b0 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b1 = store_high_low_u(c23, (uint32_t)0U);
  uint64_t b2 = store_high_low_u((uint32_t)0U, c23);
  uint64_t b3 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b4 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  uint64_t b5 = store_high_low_u((uint32_t)0U, (uint32_t)0U);
  o[0U] = b0;
  o[1U] = b1;
  o[2U] = b2;
  o[3U] = b3;
  o[4U] = b4;
  o[5U] = b5;
  reduction_prime_2prime(Spec_ECC_Curves_P384, o, o);
}

static void
solinas_reduction_upload(
  uint32_t c0,
  uint32_t c1,
  uint32_t c2,
  uint32_t c3,
  uint32_t c4,
  uint32_t c5,
  uint32_t c6,
  uint32_t c7,
  uint32_t c8,
  uint32_t c9,
  uint32_t c10,
  uint32_t c11,
  uint32_t c12,
  uint32_t c13,
  uint32_t c14,
  uint32_t c15,
  uint32_t c16,
  uint32_t c17,
  uint32_t c18,
  uint32_t c19,
  uint32_t c20,
  uint32_t c21,
  uint32_t c22,
  uint32_t c23,
  uint64_t *tempBuffer
)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)6U;
  uint64_t *t2 = tempBuffer + (uint32_t)12U;
  uint64_t *t3 = tempBuffer + (uint32_t)18U;
  uint64_t *t4 = tempBuffer + (uint32_t)24U;
  uint64_t *t5 = tempBuffer + (uint32_t)30U;
  uint64_t *t6 = tempBuffer + (uint32_t)36U;
  uint64_t *t7 = tempBuffer + (uint32_t)42U;
  uint64_t *t8 = tempBuffer + (uint32_t)48U;
  uint64_t *t9 = tempBuffer + (uint32_t)54U;
  upl_zer_buffer(c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, t0);
  upl_fir_buffer(c21, c22, c23, t1);
  upl_sec_buffer(c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, t2);
  upl_thi_buffer(c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, t3);
  upl_forth_buffer(c12, c13, c14, c15, c16, c17, c18, c19, c20, c23, t4);
  upl_fif_buffer(c20, c21, c22, c23, t5);
  upl_six_buffer(c20, c21, c22, c23, t6);
  upl_sev_buffer(c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, t7);
  upl_eit_buffer(c20, c21, c22, c23, t8);
  upl_nin_buffer(c23, t9);
}

static void solinas_reduction_operations(uint64_t *tempBuffer, uint64_t *o)
{
  uint64_t *t0 = tempBuffer;
  uint64_t *t1 = tempBuffer + (uint32_t)6U;
  uint64_t *t2 = tempBuffer + (uint32_t)12U;
  uint64_t *t3 = tempBuffer + (uint32_t)18U;
  uint64_t *t4 = tempBuffer + (uint32_t)24U;
  uint64_t *t5 = tempBuffer + (uint32_t)30U;
  uint64_t *t6 = tempBuffer + (uint32_t)36U;
  uint64_t *t7 = tempBuffer + (uint32_t)42U;
  uint64_t *t8 = tempBuffer + (uint32_t)48U;
  uint64_t *t9 = tempBuffer + (uint32_t)54U;
  felem_double(Spec_ECC_Curves_P384, t1, t1);
  felem_add(Spec_ECC_Curves_P384, t0, t1, t1);
  felem_add(Spec_ECC_Curves_P384, t1, t2, t2);
  felem_add(Spec_ECC_Curves_P384, t2, t3, t3);
  felem_add(Spec_ECC_Curves_P384, t3, t4, t4);
  felem_add(Spec_ECC_Curves_P384, t4, t5, t5);
  felem_add(Spec_ECC_Curves_P384, t5, t6, t6);
  felem_sub(Spec_ECC_Curves_P384, t6, t7, t7);
  felem_sub(Spec_ECC_Curves_P384, t7, t8, t8);
  felem_sub(Spec_ECC_Curves_P384, t8, t9, o);
}

static void solinas_reduction_impl_p384(uint64_t *i, uint64_t *o)
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
  solinas_reduction_upload(c0,
    c1,
    c2,
    c3,
    c4,
    c5,
    c6,
    c7,
    c8,
    c9,
    c10,
    c11,
    c12,
    c13,
    c14,
    c15,
    c16,
    c17,
    c18,
    c19,
    c20,
    c21,
    c22,
    c23,
    tempBuffer);
  solinas_reduction_operations(tempBuffer, o);
}

static uint64_t store_high_low_u0(uint32_t high, uint32_t low)
{
  uint64_t as_uint64_high = (uint64_t)high;
  uint64_t as_uint64_high1 = as_uint64_high << (uint32_t)32U;
  uint64_t as_uint64_low = (uint64_t)low;
  return as_uint64_low ^ as_uint64_high1;
}

static void solinas_reduction_impl_p256(uint64_t *i, uint64_t *o)
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
  uint64_t b0 = store_high_low_u0(c1, c0);
  uint64_t b10 = store_high_low_u0(c3, c2);
  uint64_t b20 = store_high_low_u0(c5, c4);
  uint64_t b30 = store_high_low_u0(c7, c6);
  t01[0U] = b0;
  t01[1U] = b10;
  t01[2U] = b20;
  t01[3U] = b30;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t01, t01);
  uint64_t b00 = (uint64_t)0U;
  uint64_t b11 = store_high_low_u0(c11, (uint32_t)0U);
  uint64_t b21 = store_high_low_u0(c13, c12);
  uint64_t b31 = store_high_low_u0(c15, c14);
  t110[0U] = b00;
  t110[1U] = b11;
  t110[2U] = b21;
  t110[3U] = b31;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t110, t110);
  uint64_t b01 = (uint64_t)0U;
  uint64_t b12 = store_high_low_u0(c12, (uint32_t)0U);
  uint64_t b22 = store_high_low_u0(c14, c13);
  uint64_t b32 = store_high_low_u0((uint32_t)0U, c15);
  t210[0U] = b01;
  t210[1U] = b12;
  t210[2U] = b22;
  t210[3U] = b32;
  uint64_t b02 = store_high_low_u0(c9, c8);
  uint64_t b13 = store_high_low_u0((uint32_t)0U, c10);
  uint64_t b23 = (uint64_t)0U;
  uint64_t b33 = store_high_low_u0(c15, c14);
  t310[0U] = b02;
  t310[1U] = b13;
  t310[2U] = b23;
  t310[3U] = b33;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t310, t310);
  uint64_t b03 = store_high_low_u0(c10, c9);
  uint64_t b14 = store_high_low_u0(c13, c11);
  uint64_t b24 = store_high_low_u0(c15, c14);
  uint64_t b34 = store_high_low_u0(c8, c13);
  t410[0U] = b03;
  t410[1U] = b14;
  t410[2U] = b24;
  t410[3U] = b34;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t410, t410);
  uint64_t b04 = store_high_low_u0(c12, c11);
  uint64_t b15 = store_high_low_u0((uint32_t)0U, c13);
  uint64_t b25 = (uint64_t)0U;
  uint64_t b35 = store_high_low_u0(c10, c8);
  t510[0U] = b04;
  t510[1U] = b15;
  t510[2U] = b25;
  t510[3U] = b35;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t510, t510);
  uint64_t b05 = store_high_low_u0(c13, c12);
  uint64_t b16 = store_high_low_u0(c15, c14);
  uint64_t b26 = (uint64_t)0U;
  uint64_t b36 = store_high_low_u0(c11, c9);
  t610[0U] = b05;
  t610[1U] = b16;
  t610[2U] = b26;
  t610[3U] = b36;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t610, t610);
  uint64_t b06 = store_high_low_u0(c14, c13);
  uint64_t b17 = store_high_low_u0(c8, c15);
  uint64_t b27 = store_high_low_u0(c10, c9);
  uint64_t b37 = store_high_low_u0(c12, (uint32_t)0U);
  t710[0U] = b06;
  t710[1U] = b17;
  t710[2U] = b27;
  t710[3U] = b37;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t710, t710);
  uint64_t b07 = store_high_low_u0(c15, c14);
  uint64_t b1 = store_high_low_u0(c9, (uint32_t)0U);
  uint64_t b2 = store_high_low_u0(c11, c10);
  uint64_t b3 = store_high_low_u0(c13, (uint32_t)0U);
  t810[0U] = b07;
  t810[1U] = b1;
  t810[2U] = b2;
  t810[3U] = b3;
  reduction_prime_2prime(Spec_ECC_Curves_P256, t810, t810);
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

static void reduction(Spec_ECC_Curves_curve c, uint64_t *i, uint64_t *o)
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
        reduction_p521(i, o);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void pointToDomain(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *result)
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
  uint64_t *p_x = p;
  uint64_t *p_y = p + len;
  uint64_t *p_z = p + (uint32_t)2U * len;
  uint64_t *r_x = result;
  uint64_t *r_y = result + len;
  uint64_t *r_z = result + (uint32_t)2U * len;
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
  uint64_t multBuffer[(uint32_t)2U * len1];
  memset(multBuffer, 0U, (uint32_t)2U * len1 * sizeof (uint64_t));
  shiftLeftWord(c, p_x, multBuffer);
  reduction(c, multBuffer, r_x);
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
  uint64_t multBuffer0[(uint32_t)2U * len10];
  memset(multBuffer0, 0U, (uint32_t)2U * len10 * sizeof (uint64_t));
  shiftLeftWord(c, p_y, multBuffer0);
  reduction(c, multBuffer0, r_y);
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len11);
  uint64_t multBuffer1[(uint32_t)2U * len11];
  memset(multBuffer1, 0U, (uint32_t)2U * len11 * sizeof (uint64_t));
  shiftLeftWord(c, p_z, multBuffer1);
  reduction(c, multBuffer1, r_z);
}

static uint64_t isPointAtInfinityPrivate(Spec_ECC_Curves_curve c, uint64_t *p)
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
  uint32_t start = len * (uint32_t)2U;
  uint64_t *zCoordinate = p + start;
  uint64_t r = isZero_uint64_CT(c, zCoordinate);
  return r;
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

static void
normalisation_update(
  Spec_ECC_Curves_curve c,
  uint64_t *z2x,
  uint64_t *z3y,
  uint64_t *p,
  uint64_t *resultPoint
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
  uint64_t zeroBuffer[len];
  memset(zeroBuffer, 0U, len * sizeof (uint64_t));
  uint64_t *resultX = resultPoint;
  uint64_t *resultY = resultPoint + len;
  uint64_t *resultZ = resultPoint + (uint32_t)2U * len;
  uint64_t bit = isPointAtInfinityPrivate(c, p);
  montgomery_multiplication_buffer_by_one(c, z2x, resultX);
  montgomery_multiplication_buffer_by_one(c, z3y, resultY);
  uploadOneImpl(c, resultZ);
  copy_conditional(c, resultZ, zeroBuffer, bit);
}

static void
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
  montgomery_square_buffer(c, zf, z2f);
  montgomery_multiplication_buffer(c, z2f, zf, z3f);
  exponent(c, z2f, z2f, t8);
  exponent(c, z3f, z3f, t8);
  montgomery_multiplication_buffer(c, xf, z2f, z2f);
  montgomery_multiplication_buffer(c, yf, z3f, z3f);
  normalisation_update(c, z2f, z3f, p, resultPoint);
}

static uint64_t
scalar_bit(Spec_ECC_Curves_curve c, Lib_Buffer_buftype buf_type, void *s, uint32_t n)
{
  uint8_t sw;
  switch (buf_type)
  {
    case Lib_Buffer_MUT:
      {
        sw = ((uint8_t *)s)[Spec_ECC_Curves_getScalarLen(c) - (uint32_t)1U - n / (uint32_t)8U];
        break;
      }
    case Lib_Buffer_IMMUT:
      {
        sw = ((uint8_t *)s)[Spec_ECC_Curves_getScalarLen(c) - (uint32_t)1U - n / (uint32_t)8U];
        break;
      }
    case Lib_Buffer_CONST:
      {
        sw = ((const uint8_t *)s)[Spec_ECC_Curves_getScalarLen(c) - (uint32_t)1U - n / (uint32_t)8U];
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  return (uint64_t)(sw >> n % (uint32_t)8U & (uint8_t)1U);
}

static void
montgomery_ladder_step1(
  Spec_ECC_Curves_curve c,
  uint64_t *r0,
  uint64_t *r1,
  uint64_t *tempBuffer
)
{
  point_add(c, r0, r1, r1, tempBuffer);
  point_double(c, r0, r0, tempBuffer);
}

static void
montgomery_ladder_step(
  Spec_ECC_Curves_curve c,
  Lib_Buffer_buftype buf_type,
  uint64_t *r0,
  uint64_t *r1,
  uint64_t *tempBuffer,
  void *scalar,
  uint32_t i
)
{
  uint32_t bit0 = Spec_ECC_Curves_getPowerU(c) - i - (uint32_t)1U;
  uint64_t bit = scalar_bit(c, buf_type, scalar, bit0);
  cswap0(c, bit, r0, r1);
  montgomery_ladder_step1(c, r0, r1, tempBuffer);
  cswap0(c, bit, r0, r1);
}

static void
montgomery_ladder(
  Spec_ECC_Curves_curve c,
  Lib_Buffer_buftype a,
  uint64_t *p,
  uint64_t *q,
  void *scalar,
  uint64_t *tempBuffer
)
{
  uint32_t cycleLoop = Spec_ECC_Curves_getPowerU(c);
  for (uint32_t i = (uint32_t)0U; i < cycleLoop; i++)
  {
    montgomery_ladder_step(c, a, p, q, tempBuffer, scalar, i);
  }
}

static void
scalarMultiplicationL(
  Spec_ECC_Curves_curve c,
  uint64_t *p,
  uint64_t *result,
  uint8_t *scalar,
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
  uploadZeroPoint(c, q);
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  pointToDomain(c, p, result);
  montgomery_ladder(c, Lib_Buffer_MUT, q, result, (void *)scalar, buff);
  norm(c, q, result, buff);
}

static void uploadBasePoint(Spec_ECC_Curves_curve c, uint64_t *p)
{
  switch (c)
  {
    case Spec_ECC_Curves_P384:
      {
        p[0U] = (uint64_t)0x3dd0756649c0b528U;
        p[1U] = (uint64_t)0x20e378e2a0d6ce38U;
        p[2U] = (uint64_t)0x879c3afc541b4d6eU;
        p[3U] = (uint64_t)0x6454868459a30effU;
        p[4U] = (uint64_t)0x812ff723614ede2bU;
        p[5U] = (uint64_t)0x4d3aadc2299e1513U;
        p[6U] = (uint64_t)0x23043dad4b03a4feU;
        p[7U] = (uint64_t)0xa1bfa8bf7bb4a9acU;
        p[8U] = (uint64_t)0x8bade7562e83b050U;
        p[9U] = (uint64_t)0xc6c3521968f4ffd9U;
        p[10U] = (uint64_t)0xdd8002263969a840U;
        p[11U] = (uint64_t)0x2b78abc25a15c5e9U;
        p[12U] = (uint64_t)0xffffffff00000001U;
        p[13U] = (uint64_t)0xffffffffU;
        p[14U] = (uint64_t)0x1U;
        p[15U] = (uint64_t)0U;
        p[16U] = (uint64_t)0U;
        p[17U] = (uint64_t)0U;
        break;
      }
    case Spec_ECC_Curves_P256:
      {
        p[0U] = (uint64_t)0x79e730d418a9143cU;
        p[1U] = (uint64_t)0x75ba95fc5fedb601U;
        p[2U] = (uint64_t)0x79fb732b77622510U;
        p[3U] = (uint64_t)0x18905f76a53755c6U;
        p[4U] = (uint64_t)0xddf25357ce95560aU;
        p[5U] = (uint64_t)0x8b4ab8e4ba19e45cU;
        p[6U] = (uint64_t)0xd2e88688dd21f325U;
        p[7U] = (uint64_t)0x8571ff1825885d85U;
        p[8U] = (uint64_t)0x1U;
        p[9U] = (uint64_t)0xffffffff00000000U;
        p[10U] = (uint64_t)0xffffffffffffffffU;
        p[11U] = (uint64_t)0xfffffffeU;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void
secretToPublic(
  Spec_ECC_Curves_curve c,
  uint64_t *result,
  uint8_t *scalar,
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
  uint64_t basePoint[(uint32_t)3U * len];
  memset(basePoint, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uploadBasePoint(c, basePoint);
  uint64_t *q = tempBuffer;
  uint64_t *buff = tempBuffer + (uint32_t)3U * len;
  uploadZeroPoint(c, q);
  montgomery_ladder(c, Lib_Buffer_MUT, q, basePoint, (void *)scalar, buff);
  norm(c, q, result, buff);
}

static void bufferToJac(Spec_ECC_Curves_curve c, uint64_t *p, uint64_t *result)
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
  uint32_t lengthXY = sw * (uint32_t)2U;
  uint64_t *partPoint = result;
  memcpy(partPoint, p, lengthXY * sizeof (uint64_t));
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        result[lengthXY] = (uint64_t)1U;
        result[lengthXY + (uint32_t)1U] = (uint64_t)0U;
        result[lengthXY + (uint32_t)2U] = (uint64_t)0U;
        result[lengthXY + (uint32_t)3U] = (uint64_t)0U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        result[lengthXY] = (uint64_t)1U;
        result[lengthXY + (uint32_t)1U] = (uint64_t)0U;
        result[lengthXY + (uint32_t)2U] = (uint64_t)0U;
        result[lengthXY + (uint32_t)3U] = (uint64_t)0U;
        result[lengthXY + (uint32_t)4U] = (uint64_t)0U;
        result[lengthXY + (uint32_t)5U] = (uint64_t)0U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/*
  This code is not side channel resistant
*/
static bool isPointOnCurvePublic(Spec_ECC_Curves_curve c, uint64_t *p)
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
  shiftLeftWord(c, y, multBuffer);
  reduction(c, multBuffer, y2Buffer);
  montgomery_square_buffer(c, y2Buffer, y2Buffer);
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
  uint64_t multBuffer0[(uint32_t)2U * len];
  memset(multBuffer0, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  shiftLeftWord(c, x, multBuffer0);
  reduction(c, multBuffer0, xToDomainBuffer);
  montgomery_square_buffer(c, xToDomainBuffer, xBuffer);
  montgomery_multiplication_buffer(c, xBuffer, xToDomainBuffer, xBuffer);
  multByThree(c, xToDomainBuffer, minusThreeXBuffer);
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
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  felem_add(c, xBuffer, b_constant, xBuffer);
  uint64_t r = compare_felem(c, y2Buffer, xBuffer);
  return !(r == (uint64_t)0U);
}

static bool isCoordinateValid(Spec_ECC_Curves_curve c, uint64_t *p)
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
  uint64_t tempBuffer[len];
  memset(tempBuffer, 0U, len * sizeof (uint64_t));
  uint64_t *x = p;
  uint64_t *y = p + len;
  const uint64_t *sw0;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw0 = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw0 = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t carryX = sub_bn_gl(c, x, sw0, tempBuffer);
  const uint64_t *sw;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        sw = prime256_buffer;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        sw = prime384_buffer;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint64_t carryY = sub_bn_gl(c, y, sw, tempBuffer);
  bool lessX = carryX == (uint64_t)1U;
  bool lessY = carryY == (uint64_t)1U;
  return lessX && lessY;
}

/*
  This code is not side channel resistant
*/
static bool verifyQValidCurvePoint(Spec_ECC_Curves_curve uu___, uint64_t *pubKeyAsPoint)
{
  bool coordinatesValid = isCoordinateValid(uu___, pubKeyAsPoint);
  if (!coordinatesValid)
  {
    return false;
  }
  bool belongsToCurve = isPointOnCurvePublic(uu___, pubKeyAsPoint);
  return coordinatesValid && belongsToCurve;
}

static uint64_t
_ecp256dh_r(Spec_ECC_Curves_curve c, uint64_t *result, uint64_t *pubKey, uint8_t *scalar)
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)25U * len);
  uint64_t tempBuffer[(uint32_t)25U * len];
  memset(tempBuffer, 0U, (uint32_t)25U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t publicKeyBuffer[(uint32_t)3U * len];
  memset(publicKeyBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  bufferToJac(c, pubKey, publicKeyBuffer);
  bool publicKeyCorrect = verifyQValidCurvePoint(c, publicKeyBuffer);
  if (publicKeyCorrect)
  {
    scalarMultiplicationL(c, publicKeyBuffer, result, scalar, tempBuffer);
    uint64_t flag = isPointAtInfinityPrivate(c, result);
    return flag;
  }
  return (uint64_t)18446744073709551615U;
}

uint64_t Hacl_P256_ecp256dh_i(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)4U;
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)25U * len);
  uint64_t tempBuffer[(uint32_t)25U * len];
  memset(tempBuffer, 0U, (uint32_t)25U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + len;
  uint8_t *resultX = result;
  uint8_t *resultY = result + scalarLen;
  secretToPublic(Spec_ECC_Curves_P256, resultBuffer, scalar, tempBuffer);
  uint64_t flag = isPointAtInfinityPrivate(Spec_ECC_Curves_P256, resultBuffer);
  changeEndian(Spec_ECC_Curves_P256, resultBufferX);
  changeEndian(Spec_ECC_Curves_P256, resultBufferY);
  toUint8(Spec_ECC_Curves_P256, resultBufferX, resultX);
  toUint8(Spec_ECC_Curves_P256, resultBufferY, resultY);
  return flag;
}

uint64_t Hacl_P256_ecp384dh_i(uint8_t *result, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  uint32_t scalarLen = Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)25U * len);
  uint64_t tempBuffer[(uint32_t)25U * len];
  memset(tempBuffer, 0U, (uint32_t)25U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBuffer[(uint32_t)3U * len];
  memset(resultBuffer, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint64_t *resultBufferX = resultBuffer;
  uint64_t *resultBufferY = resultBuffer + len;
  uint8_t *resultX = result;
  uint8_t *resultY = result + scalarLen;
  secretToPublic(Spec_ECC_Curves_P384, resultBuffer, scalar, tempBuffer);
  uint64_t flag = isPointAtInfinityPrivate(Spec_ECC_Curves_P384, resultBuffer);
  changeEndian(Spec_ECC_Curves_P384, resultBufferX);
  changeEndian(Spec_ECC_Curves_P384, resultBufferY);
  toUint8(Spec_ECC_Curves_P384, resultBufferX, resultX);
  toUint8(Spec_ECC_Curves_P384, resultBufferY, resultY);
  return flag;
}

uint64_t Hacl_P256_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBufferFelem[(uint32_t)3U * len];
  memset(resultBufferFelem, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint64_t *resultBufferFelemX = resultBufferFelem;
  uint64_t *resultBufferFelemY = resultBufferFelem + len;
  uint8_t *resultX = result;
  uint8_t *resultY = result + Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t publicKeyAsFelem[(uint32_t)2U * len];
  memset(publicKeyAsFelem, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P256);
  toUint64ChangeEndian(Spec_ECC_Curves_P256, pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(Spec_ECC_Curves_P256, pubKeyY, publicKeyFelemY);
  uint64_t flag = _ecp256dh_r(Spec_ECC_Curves_P256, resultBufferFelem, publicKeyAsFelem, scalar);
  changeEndian(Spec_ECC_Curves_P256, resultBufferFelemX);
  changeEndian(Spec_ECC_Curves_P256, resultBufferFelemY);
  toUint8(Spec_ECC_Curves_P256, resultBufferFelemX, resultX);
  toUint8(Spec_ECC_Curves_P256, resultBufferFelemY, resultY);
  return flag;
}

uint64_t Hacl_P256_ecp384dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar)
{
  uint32_t len = (uint32_t)6U;
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)3U * len);
  uint64_t resultBufferFelem[(uint32_t)3U * len];
  memset(resultBufferFelem, 0U, (uint32_t)3U * len * sizeof (uint64_t));
  uint64_t *resultBufferFelemX = resultBufferFelem;
  uint64_t *resultBufferFelemY = resultBufferFelem + len;
  uint8_t *resultX = result;
  uint8_t *resultY = result + Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)2U * len);
  uint64_t publicKeyAsFelem[(uint32_t)2U * len];
  memset(publicKeyAsFelem, 0U, (uint32_t)2U * len * sizeof (uint64_t));
  uint64_t *publicKeyFelemX = publicKeyAsFelem;
  uint64_t *publicKeyFelemY = publicKeyAsFelem + len;
  uint8_t *pubKeyX = pubKey;
  uint8_t *pubKeyY = pubKey + Spec_ECC_Curves_getScalarLen(Spec_ECC_Curves_P384);
  toUint64ChangeEndian(Spec_ECC_Curves_P384, pubKeyX, publicKeyFelemX);
  toUint64ChangeEndian(Spec_ECC_Curves_P384, pubKeyY, publicKeyFelemY);
  uint64_t flag = _ecp256dh_r(Spec_ECC_Curves_P384, resultBufferFelem, publicKeyAsFelem, scalar);
  changeEndian(Spec_ECC_Curves_P384, resultBufferFelemX);
  changeEndian(Spec_ECC_Curves_P384, resultBufferFelemY);
  toUint8(Spec_ECC_Curves_P384, resultBufferFelemX, resultX);
  toUint8(Spec_ECC_Curves_P384, resultBufferFelemY, resultY);
  return flag;
}

