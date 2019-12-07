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


#include "Hacl_Ed25519.h"

static void Hacl_Bignum25519_fsum(uint64_t *a, uint64_t *b)
{
  Hacl_Impl_Curve25519_Field51_fadd(a, a, b);
}

static void Hacl_Bignum25519_fdifference(uint64_t *a, uint64_t *b)
{
  Hacl_Impl_Curve25519_Field51_fsub(a, b, a);
}

static void Hacl_Bignum25519_reduce_513(uint64_t *a)
{
  Hacl_Impl_Curve25519_Field51_fmul1(a, a, (uint64_t)1U);
}

static void Hacl_Bignum25519_fmul(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  uint128_t tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = (uint128_t)(uint64_t)0U;
  Hacl_Impl_Curve25519_Field51_fmul(output, input, input2, tmp);
}

static void Hacl_Bignum25519_times_2(uint64_t *out, uint64_t *a)
{
  uint64_t a0 = a[0U];
  uint64_t a1 = a[1U];
  uint64_t a2 = a[2U];
  uint64_t a3 = a[3U];
  uint64_t a4 = a[4U];
  uint64_t o0 = (uint64_t)2U * a0;
  uint64_t o1 = (uint64_t)2U * a1;
  uint64_t o2 = (uint64_t)2U * a2;
  uint64_t o3 = (uint64_t)2U * a3;
  uint64_t o4 = (uint64_t)2U * a4;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

static void Hacl_Bignum25519_times_d(uint64_t *out, uint64_t *a)
{
  uint64_t d1[5U] = { 0U };
  d1[0U] = (uint64_t)0x00034dca135978a3U;
  d1[1U] = (uint64_t)0x0001a8283b156ebdU;
  d1[2U] = (uint64_t)0x0005e7a26001c029U;
  d1[3U] = (uint64_t)0x000739c663a03cbbU;
  d1[4U] = (uint64_t)0x00052036cee2b6ffU;
  Hacl_Bignum25519_fmul(out, d1, a);
}

static void Hacl_Bignum25519_times_2d(uint64_t *out, uint64_t *a)
{
  uint64_t d2[5U] = { 0U };
  d2[0U] = (uint64_t)0x00069b9426b2f159U;
  d2[1U] = (uint64_t)0x00035050762add7aU;
  d2[2U] = (uint64_t)0x0003cf44c0038052U;
  d2[3U] = (uint64_t)0x0006738cc7407977U;
  d2[4U] = (uint64_t)0x0002406d9dc56dffU;
  Hacl_Bignum25519_fmul(out, d2, a);
}

static void Hacl_Bignum25519_fsquare(uint64_t *out, uint64_t *a)
{
  uint128_t tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = (uint128_t)(uint64_t)0U;
  Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp);
}

static void Hacl_Bignum25519_fsquare_times(uint64_t *output, uint64_t *input, uint32_t count1)
{
  uint128_t tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = (uint128_t)(uint64_t)0U;
  Hacl_Curve25519_51_fsquare_times(output, input, tmp, count1);
}

static void Hacl_Bignum25519_fsquare_times_inplace(uint64_t *output, uint32_t count1)
{
  uint128_t tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = (uint128_t)(uint64_t)0U;
  Hacl_Curve25519_51_fsquare_times(output, output, tmp, count1);
}

static void Hacl_Bignum25519_inverse(uint64_t *out, uint64_t *a)
{
  uint128_t tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = (uint128_t)(uint64_t)0U;
  Hacl_Curve25519_51_finv(out, a, tmp);
}

static void Hacl_Bignum25519_reduce(uint64_t *out)
{
  uint64_t t0 = out[0U];
  uint64_t t10 = out[1U];
  uint64_t t20 = out[2U];
  uint64_t t30 = out[3U];
  uint64_t t40 = out[4U];
  uint64_t t2_ = t20 + (t10 >> (uint32_t)51U);
  uint64_t t1__ = t10 & (uint64_t)0x7ffffffffffffU;
  uint64_t t3_ = t30 + (t2_ >> (uint32_t)51U);
  uint64_t t2__ = t2_ & (uint64_t)0x7ffffffffffffU;
  uint64_t t4_ = t40 + (t3_ >> (uint32_t)51U);
  uint64_t t3__ = t3_ & (uint64_t)0x7ffffffffffffU;
  out[0U] = t0;
  out[1U] = t1__;
  out[2U] = t2__;
  out[3U] = t3__;
  out[4U] = t4_;
  uint64_t b4 = out[4U];
  uint64_t b00 = out[0U];
  uint64_t b4_ = b4 & (uint64_t)0x7ffffffffffffU;
  uint64_t b0_ = b00 + (uint64_t)19U * (b4 >> (uint32_t)51U);
  out[4U] = b4_;
  out[0U] = b0_;
  uint64_t t00 = out[0U];
  uint64_t t1 = out[1U];
  uint64_t t2 = out[2U];
  uint64_t t3 = out[3U];
  uint64_t t4 = out[4U];
  uint64_t t1_ = t1 + (t00 >> (uint32_t)51U);
  uint64_t t0_ = t00 & (uint64_t)0x7ffffffffffffU;
  uint64_t t2_0 = t2 + (t1_ >> (uint32_t)51U);
  uint64_t t1__0 = t1_ & (uint64_t)0x7ffffffffffffU;
  uint64_t t3_0 = t3 + (t2_0 >> (uint32_t)51U);
  uint64_t t2__0 = t2_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t t4_0 = t4 + (t3_0 >> (uint32_t)51U);
  uint64_t t3__0 = t3_0 & (uint64_t)0x7ffffffffffffU;
  out[0U] = t0_;
  out[1U] = t1__0;
  out[2U] = t2__0;
  out[3U] = t3__0;
  out[4U] = t4_0;
  uint64_t b40 = out[4U];
  uint64_t b0 = out[0U];
  uint64_t b4_0 = b40 & (uint64_t)0x7ffffffffffffU;
  uint64_t b0_0 = b0 + (uint64_t)19U * (b40 >> (uint32_t)51U);
  out[4U] = b4_0;
  out[0U] = b0_0;
  uint64_t i0 = out[0U];
  uint64_t i1 = out[1U];
  uint64_t i0_ = i0 & (uint64_t)0x7ffffffffffffU;
  uint64_t i1_ = i1 + (i0 >> (uint32_t)51U);
  out[0U] = i0_;
  out[1U] = i1_;
  uint64_t a0 = out[0U];
  uint64_t a1 = out[1U];
  uint64_t a2 = out[2U];
  uint64_t a3 = out[3U];
  uint64_t a4 = out[4U];
  uint64_t m0 = FStar_UInt64_gte_mask(a0, (uint64_t)0x7ffffffffffedU);
  uint64_t m1 = FStar_UInt64_eq_mask(a1, (uint64_t)0x7ffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(a2, (uint64_t)0x7ffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(a3, (uint64_t)0x7ffffffffffffU);
  uint64_t m4 = FStar_UInt64_eq_mask(a4, (uint64_t)0x7ffffffffffffU);
  uint64_t mask = (((m0 & m1) & m2) & m3) & m4;
  uint64_t a0_ = a0 - ((uint64_t)0x7ffffffffffedU & mask);
  uint64_t a1_ = a1 - ((uint64_t)0x7ffffffffffffU & mask);
  uint64_t a2_ = a2 - ((uint64_t)0x7ffffffffffffU & mask);
  uint64_t a3_ = a3 - ((uint64_t)0x7ffffffffffffU & mask);
  uint64_t a4_ = a4 - ((uint64_t)0x7ffffffffffffU & mask);
  out[0U] = a0_;
  out[1U] = a1_;
  out[2U] = a2_;
  out[3U] = a3_;
  out[4U] = a4_;
}

static void Hacl_Bignum25519_load_51(uint64_t *output, uint8_t *input)
{
  uint64_t u0 = load64_le(input);
  uint64_t i0 = u0;
  uint64_t u1 = load64_le(input + (uint32_t)6U);
  uint64_t i1 = u1;
  uint64_t u2 = load64_le(input + (uint32_t)12U);
  uint64_t i2 = u2;
  uint64_t u3 = load64_le(input + (uint32_t)19U);
  uint64_t i3 = u3;
  uint64_t u = load64_le(input + (uint32_t)24U);
  uint64_t i4 = u;
  uint64_t output0 = i0 & (uint64_t)0x7ffffffffffffU;
  uint64_t output1 = i1 >> (uint32_t)3U & (uint64_t)0x7ffffffffffffU;
  uint64_t output2 = i2 >> (uint32_t)6U & (uint64_t)0x7ffffffffffffU;
  uint64_t output3 = i3 >> (uint32_t)1U & (uint64_t)0x7ffffffffffffU;
  uint64_t output4 = i4 >> (uint32_t)12U & (uint64_t)0x7ffffffffffffU;
  output[0U] = output0;
  output[1U] = output1;
  output[2U] = output2;
  output[3U] = output3;
  output[4U] = output4;
}

static void
Hacl_Bignum25519_store_4(uint8_t *output, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3)
{
  uint8_t *b0 = output;
  uint8_t *b1 = output + (uint32_t)8U;
  uint8_t *b2 = output + (uint32_t)16U;
  uint8_t *b3 = output + (uint32_t)24U;
  store64_le(b0, v0);
  store64_le(b1, v1);
  store64_le(b2, v2);
  store64_le(b3, v3);
}

static void Hacl_Bignum25519_store_51(uint8_t *output, uint64_t *input)
{
  uint64_t t0 = input[0U];
  uint64_t t1 = input[1U];
  uint64_t t2 = input[2U];
  uint64_t t3 = input[3U];
  uint64_t t4 = input[4U];
  uint64_t l_ = t0 + (uint64_t)0U;
  uint64_t tmp0 = l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = l_ >> (uint32_t)51U;
  uint64_t l_0 = t1 + c0;
  uint64_t tmp1 = l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = l_0 >> (uint32_t)51U;
  uint64_t l_1 = t2 + c1;
  uint64_t tmp2 = l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = l_1 >> (uint32_t)51U;
  uint64_t l_2 = t3 + c2;
  uint64_t tmp3 = l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = l_2 >> (uint32_t)51U;
  uint64_t l_3 = t4 + c3;
  uint64_t tmp4 = l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = l_3 >> (uint32_t)51U;
  uint64_t l_4 = tmp0 + c4 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_4 >> (uint32_t)51U;
  uint64_t f0 = tmp0_;
  uint64_t f1 = tmp1 + c5;
  uint64_t f2 = tmp2;
  uint64_t f3 = tmp3;
  uint64_t f4 = tmp4;
  uint64_t m0 = FStar_UInt64_gte_mask(f0, (uint64_t)0x7ffffffffffedU);
  uint64_t m1 = FStar_UInt64_eq_mask(f1, (uint64_t)0x7ffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(f2, (uint64_t)0x7ffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(f3, (uint64_t)0x7ffffffffffffU);
  uint64_t m4 = FStar_UInt64_eq_mask(f4, (uint64_t)0x7ffffffffffffU);
  uint64_t mask = (((m0 & m1) & m2) & m3) & m4;
  uint64_t f0_ = f0 - (mask & (uint64_t)0x7ffffffffffedU);
  uint64_t f1_ = f1 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f2_ = f2 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f3_ = f3 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f4_ = f4 - (mask & (uint64_t)0x7ffffffffffffU);
  uint64_t f01 = f0_;
  uint64_t f11 = f1_;
  uint64_t f21 = f2_;
  uint64_t f31 = f3_;
  uint64_t f41 = f4_;
  uint64_t o00 = f01 | f11 << (uint32_t)51U;
  uint64_t o10 = f11 >> (uint32_t)13U | f21 << (uint32_t)38U;
  uint64_t o20 = f21 >> (uint32_t)26U | f31 << (uint32_t)25U;
  uint64_t o30 = f31 >> (uint32_t)39U | f41 << (uint32_t)12U;
  uint64_t o0 = o00;
  uint64_t o1 = o10;
  uint64_t o2 = o20;
  uint64_t o3 = o30;
  Hacl_Bignum25519_store_4(output, o0, o1, o2, o3);
}

static void Hacl_Impl_Ed25519_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q1)
{
  uint64_t tmp[30U] = { 0U };
  uint64_t *tmp1 = tmp;
  uint64_t *tmp20 = tmp + (uint32_t)5U;
  uint64_t *tmp30 = tmp + (uint32_t)10U;
  uint64_t *tmp40 = tmp + (uint32_t)15U;
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *x2 = q1;
  uint64_t *y2 = q1 + (uint32_t)5U;
  memcpy(tmp1, x1, (uint32_t)5U * sizeof x1[0U]);
  memcpy(tmp20, x2, (uint32_t)5U * sizeof x2[0U]);
  Hacl_Bignum25519_fdifference(tmp1, y1);
  Hacl_Bignum25519_fdifference(tmp20, y2);
  Hacl_Bignum25519_fmul(tmp30, tmp1, tmp20);
  memcpy(tmp1, y1, (uint32_t)5U * sizeof y1[0U]);
  memcpy(tmp20, y2, (uint32_t)5U * sizeof y2[0U]);
  Hacl_Bignum25519_fsum(tmp1, x1);
  Hacl_Bignum25519_fsum(tmp20, x2);
  Hacl_Bignum25519_fmul(tmp40, tmp1, tmp20);
  uint64_t *tmp10 = tmp;
  uint64_t *tmp2 = tmp + (uint32_t)5U;
  uint64_t *tmp3 = tmp + (uint32_t)10U;
  uint64_t *tmp41 = tmp + (uint32_t)15U;
  uint64_t *tmp50 = tmp + (uint32_t)20U;
  uint64_t *tmp60 = tmp + (uint32_t)25U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t *t1 = p + (uint32_t)15U;
  uint64_t *z2 = q1 + (uint32_t)10U;
  uint64_t *t2 = q1 + (uint32_t)15U;
  Hacl_Bignum25519_times_2d(tmp10, t1);
  Hacl_Bignum25519_fmul(tmp2, tmp10, t2);
  Hacl_Bignum25519_times_2(tmp10, z1);
  Hacl_Bignum25519_fmul(tmp50, tmp10, z2);
  memcpy(tmp10, tmp3, (uint32_t)5U * sizeof tmp3[0U]);
  memcpy(tmp60, tmp2, (uint32_t)5U * sizeof tmp2[0U]);
  Hacl_Bignum25519_fdifference(tmp10, tmp41);
  Hacl_Bignum25519_fdifference(tmp60, tmp50);
  Hacl_Bignum25519_fsum(tmp50, tmp2);
  Hacl_Bignum25519_fsum(tmp41, tmp3);
  uint64_t *tmp11 = tmp;
  uint64_t *tmp4 = tmp + (uint32_t)15U;
  uint64_t *tmp5 = tmp + (uint32_t)20U;
  uint64_t *tmp6 = tmp + (uint32_t)25U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *t3 = out + (uint32_t)15U;
  Hacl_Bignum25519_fmul(x3, tmp11, tmp6);
  Hacl_Bignum25519_fmul(y3, tmp5, tmp4);
  Hacl_Bignum25519_fmul(t3, tmp11, tmp4);
  Hacl_Bignum25519_fmul(z3, tmp6, tmp5);
}

static void Hacl_Impl_Ed25519_PointDouble_point_double(uint64_t *out, uint64_t *p)
{
  uint64_t tmp[30U] = { 0U };
  uint64_t *tmp2 = tmp + (uint32_t)5U;
  uint64_t *tmp3 = tmp + (uint32_t)10U;
  uint64_t *tmp4 = tmp + (uint32_t)15U;
  uint64_t *tmp6 = tmp + (uint32_t)25U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *t3 = out + (uint32_t)15U;
  uint64_t *tmp11 = tmp;
  uint64_t *tmp210 = tmp + (uint32_t)5U;
  uint64_t *tmp310 = tmp + (uint32_t)10U;
  uint64_t *tmp410 = tmp + (uint32_t)15U;
  uint64_t *x10 = p;
  uint64_t *y10 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  Hacl_Bignum25519_fsquare(tmp11, x10);
  Hacl_Bignum25519_fsquare(tmp210, y10);
  Hacl_Bignum25519_fsquare(tmp310, z1);
  Hacl_Bignum25519_times_2(tmp410, tmp310);
  memcpy(tmp310, tmp11, (uint32_t)5U * sizeof tmp11[0U]);
  Hacl_Bignum25519_fsum(tmp310, tmp210);
  uint64_t *tmp110 = tmp;
  uint64_t *tmp21 = tmp + (uint32_t)5U;
  uint64_t *tmp31 = tmp + (uint32_t)10U;
  uint64_t *tmp41 = tmp + (uint32_t)15U;
  uint64_t *tmp51 = tmp + (uint32_t)20U;
  uint64_t *tmp61 = tmp + (uint32_t)25U;
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  memcpy(tmp51, x1, (uint32_t)5U * sizeof x1[0U]);
  Hacl_Bignum25519_fsum(tmp51, y1);
  Hacl_Bignum25519_fsquare(tmp61, tmp51);
  memcpy(tmp51, tmp31, (uint32_t)5U * sizeof tmp31[0U]);
  Hacl_Bignum25519_reduce_513(tmp51);
  Hacl_Bignum25519_fdifference(tmp61, tmp51);
  Hacl_Bignum25519_fdifference(tmp21, tmp110);
  Hacl_Bignum25519_reduce_513(tmp21);
  Hacl_Bignum25519_reduce_513(tmp41);
  Hacl_Bignum25519_fsum(tmp41, tmp21);
  Hacl_Bignum25519_fmul(x3, tmp4, tmp6);
  Hacl_Bignum25519_fmul(y3, tmp2, tmp3);
  Hacl_Bignum25519_fmul(t3, tmp6, tmp3);
  Hacl_Bignum25519_fmul(z3, tmp4, tmp2);
}

static void
Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(
  uint64_t *a_,
  uint64_t *b_,
  uint64_t *a,
  uint64_t *b,
  uint64_t swap1
)
{
  uint64_t a0 = a[0U];
  uint64_t a1 = a[1U];
  uint64_t a2 = a[2U];
  uint64_t a3 = a[3U];
  uint64_t a4 = a[4U];
  uint64_t b0 = b[0U];
  uint64_t b1 = b[1U];
  uint64_t b2 = b[2U];
  uint64_t b3 = b[3U];
  uint64_t b4 = b[4U];
  uint64_t x0 = (a0 ^ b0) & swap1;
  uint64_t x1 = (a1 ^ b1) & swap1;
  uint64_t x2 = (a2 ^ b2) & swap1;
  uint64_t x3 = (a3 ^ b3) & swap1;
  uint64_t x4 = (a4 ^ b4) & swap1;
  a_[0U] = a0 ^ x0;
  b_[0U] = b0 ^ x0;
  a_[1U] = a1 ^ x1;
  b_[1U] = b1 ^ x1;
  a_[2U] = a2 ^ x2;
  b_[2U] = b2 ^ x2;
  a_[3U] = a3 ^ x3;
  b_[3U] = b3 ^ x3;
  a_[4U] = a4 ^ x4;
  b_[4U] = b4 ^ x4;
}

static void
Hacl_Impl_Ed25519_SwapConditional_swap_conditional(
  uint64_t *a_,
  uint64_t *b_,
  uint64_t *a,
  uint64_t *b,
  uint64_t iswap
)
{
  uint64_t swap1 = (uint64_t)0U - iswap;
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a_, b_, a, b, swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a_ + (uint32_t)5U,
    b_ + (uint32_t)5U,
    a + (uint32_t)5U,
    b + (uint32_t)5U,
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a_ + (uint32_t)10U,
    b_ + (uint32_t)10U,
    a + (uint32_t)10U,
    b + (uint32_t)10U,
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a_ + (uint32_t)15U,
    b_ + (uint32_t)15U,
    a + (uint32_t)15U,
    b + (uint32_t)15U,
    swap1);
}

static void
Hacl_Impl_Ed25519_SwapConditional_swap_conditional_inplace(
  uint64_t *a,
  uint64_t *b,
  uint64_t iswap
)
{
  uint64_t swap1 = (uint64_t)0U - iswap;
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a, b, a, b, swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a + (uint32_t)5U,
    b + (uint32_t)5U,
    a + (uint32_t)5U,
    b + (uint32_t)5U,
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a + (uint32_t)10U,
    b + (uint32_t)10U,
    a + (uint32_t)10U,
    b + (uint32_t)10U,
    swap1);
  Hacl_Impl_Ed25519_SwapConditional_swap_conditional_step(a + (uint32_t)15U,
    b + (uint32_t)15U,
    a + (uint32_t)15U,
    b + (uint32_t)15U,
    swap1);
}

static void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *result, uint8_t *scalar, uint64_t *q1)
{
  uint64_t b[80U] = { 0U };
  uint64_t *nq = b;
  uint64_t *nqpq = b + (uint32_t)20U;
  uint64_t *x = nq;
  uint64_t *y = nq + (uint32_t)5U;
  uint64_t *z = nq + (uint32_t)10U;
  uint64_t *t = nq + (uint32_t)15U;
  x[0U] = (uint64_t)0U;
  x[1U] = (uint64_t)0U;
  x[2U] = (uint64_t)0U;
  x[3U] = (uint64_t)0U;
  x[4U] = (uint64_t)0U;
  y[0U] = (uint64_t)1U;
  y[1U] = (uint64_t)0U;
  y[2U] = (uint64_t)0U;
  y[3U] = (uint64_t)0U;
  y[4U] = (uint64_t)0U;
  z[0U] = (uint64_t)1U;
  z[1U] = (uint64_t)0U;
  z[2U] = (uint64_t)0U;
  z[3U] = (uint64_t)0U;
  z[4U] = (uint64_t)0U;
  t[0U] = (uint64_t)0U;
  t[1U] = (uint64_t)0U;
  t[2U] = (uint64_t)0U;
  t[3U] = (uint64_t)0U;
  t[4U] = (uint64_t)0U;
  memcpy(nqpq, q1, (uint32_t)20U * sizeof q1[0U]);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i = i + (uint32_t)1U)
  {
    uint64_t *nq1 = b;
    uint64_t *nqpq1 = b + (uint32_t)20U;
    uint64_t *nq2 = b + (uint32_t)40U;
    uint64_t *nqpq2 = b + (uint32_t)60U;
    uint32_t q2 = ((uint32_t)255U - i) >> (uint32_t)3U;
    uint32_t r = ((uint32_t)255U - i) & (uint32_t)7U;
    uint8_t kq = scalar[q2];
    uint8_t i1 = kq >> r & (uint8_t)1U;
    Hacl_Impl_Ed25519_SwapConditional_swap_conditional_inplace(nq1, nqpq1, (uint64_t)i1);
    Hacl_Impl_Ed25519_PointDouble_point_double(nq2, nq1);
    Hacl_Impl_Ed25519_PointAdd_point_add(nqpq2, nq1, nqpq1);
    Hacl_Impl_Ed25519_SwapConditional_swap_conditional(nq1, nqpq1, nq2, nqpq2, (uint64_t)i1);
  }
  memcpy(result, nq, (uint32_t)20U * sizeof nq[0U]);
}

static void Hacl_Impl_Ed25519_Ladder_point_mul_g(uint64_t *result, uint8_t *scalar)
{
  uint64_t g1[20U] = { 0U };
  uint64_t *gx = g1;
  uint64_t *gy = g1 + (uint32_t)5U;
  uint64_t *gz = g1 + (uint32_t)10U;
  uint64_t *gt1 = g1 + (uint32_t)15U;
  gx[0U] = (uint64_t)0x00062d608f25d51aU;
  gx[1U] = (uint64_t)0x000412a4b4f6592aU;
  gx[2U] = (uint64_t)0x00075b7171a4b31dU;
  gx[3U] = (uint64_t)0x0001ff60527118feU;
  gx[4U] = (uint64_t)0x000216936d3cd6e5U;
  gy[0U] = (uint64_t)0x0006666666666658U;
  gy[1U] = (uint64_t)0x0004ccccccccccccU;
  gy[2U] = (uint64_t)0x0001999999999999U;
  gy[3U] = (uint64_t)0x0003333333333333U;
  gy[4U] = (uint64_t)0x0006666666666666U;
  gz[0U] = (uint64_t)1U;
  gz[1U] = (uint64_t)0U;
  gz[2U] = (uint64_t)0U;
  gz[3U] = (uint64_t)0U;
  gz[4U] = (uint64_t)0U;
  gt1[0U] = (uint64_t)0x00068ab3a5b7dda3U;
  gt1[1U] = (uint64_t)0x00000eea2a5eadbbU;
  gt1[2U] = (uint64_t)0x0002af8df483c27eU;
  gt1[3U] = (uint64_t)0x000332b375274732U;
  gt1[4U] = (uint64_t)0x00067875f0fd78b7U;
  Hacl_Impl_Ed25519_Ladder_point_mul(result, scalar, g1);
}

static void Hacl_Impl_Ed25519_PointCompress_point_compress(uint8_t *z, uint64_t *p)
{
  uint64_t tmp[15U] = { 0U };
  uint64_t *x = tmp + (uint32_t)5U;
  uint64_t *out = tmp + (uint32_t)10U;
  uint64_t *zinv1 = tmp;
  uint64_t *x1 = tmp + (uint32_t)5U;
  uint64_t *out1 = tmp + (uint32_t)10U;
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  Hacl_Bignum25519_inverse(zinv1, pz);
  Hacl_Bignum25519_fmul(x1, px, zinv1);
  Hacl_Bignum25519_reduce(x1);
  Hacl_Bignum25519_fmul(out1, py, zinv1);
  Hacl_Bignum25519_reduce_513(out1);
  uint64_t x0 = x[0U];
  uint64_t b = x0 & (uint64_t)1U;
  Hacl_Bignum25519_store_51(z, out);
  uint8_t xbyte = (uint8_t)b;
  uint8_t o31 = z[31U];
  z[31U] = o31 + (xbyte << (uint32_t)7U);
}

static void Hacl_Impl_Ed25519_SecretExpand_secret_expand(uint8_t *expanded, uint8_t *secret1)
{
  Hacl_Hash_SHA2_hash_512(secret1, (uint32_t)32U, expanded);
  uint8_t *h_low = expanded;
  uint8_t h_low0 = h_low[0U];
  uint8_t h_low31 = h_low[31U];
  h_low[0U] = h_low0 & (uint8_t)0xf8U;
  h_low[31U] = (h_low31 & (uint8_t)127U) | (uint8_t)64U;
}

static void Hacl_Impl_Ed25519_SecretToPublic_secret_to_public(uint8_t *out, uint8_t *secret1)
{
  uint8_t expanded_secret[64U] = { 0U };
  uint64_t res[20U] = { 0U };
  Hacl_Impl_Ed25519_SecretExpand_secret_expand(expanded_secret, secret1);
  uint8_t *a = expanded_secret;
  Hacl_Impl_Ed25519_Ladder_point_mul_g(res, a);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, res);
}

static void Hacl_Impl_BignumQ_Mul_barrett_reduction(uint64_t *z, uint64_t *t)
{
  uint64_t t0 = t[0U];
  uint64_t t1 = t[1U];
  uint64_t t2 = t[2U];
  uint64_t t3 = t[3U];
  uint64_t t4 = t[4U];
  uint64_t t5 = t[5U];
  uint64_t t6 = t[6U];
  uint64_t t7 = t[7U];
  uint64_t t8 = t[8U];
  uint64_t t9 = t[9U];
  uint64_t m00 = (uint64_t)0x12631a5cf5d3edU;
  uint64_t m10 = (uint64_t)0xf9dea2f79cd658U;
  uint64_t m20 = (uint64_t)0x000000000014deU;
  uint64_t m30 = (uint64_t)0x00000000000000U;
  uint64_t m40 = (uint64_t)0x00000010000000U;
  uint64_t m0 = m00;
  uint64_t m1 = m10;
  uint64_t m2 = m20;
  uint64_t m3 = m30;
  uint64_t m4 = m40;
  uint64_t m010 = (uint64_t)0x9ce5a30a2c131bU;
  uint64_t m110 = (uint64_t)0x215d086329a7edU;
  uint64_t m210 = (uint64_t)0xffffffffeb2106U;
  uint64_t m310 = (uint64_t)0xffffffffffffffU;
  uint64_t m410 = (uint64_t)0x00000fffffffffU;
  uint64_t mu0 = m010;
  uint64_t mu1 = m110;
  uint64_t mu2 = m210;
  uint64_t mu3 = m310;
  uint64_t mu4 = m410;
  uint64_t y_ = (t5 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_ = t4 >> (uint32_t)24U;
  uint64_t z00 = x_ | y_;
  uint64_t y_0 = (t6 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_0 = t5 >> (uint32_t)24U;
  uint64_t z10 = x_0 | y_0;
  uint64_t y_1 = (t7 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_1 = t6 >> (uint32_t)24U;
  uint64_t z20 = x_1 | y_1;
  uint64_t y_2 = (t8 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_2 = t7 >> (uint32_t)24U;
  uint64_t z30 = x_2 | y_2;
  uint64_t y_3 = (t9 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_3 = t8 >> (uint32_t)24U;
  uint64_t z40 = x_3 | y_3;
  uint64_t q0 = z00;
  uint64_t q1 = z10;
  uint64_t q2 = z20;
  uint64_t q3 = z30;
  uint64_t q4 = z40;
  uint128_t xy000 = (uint128_t)q0 * mu0;
  uint128_t xy010 = (uint128_t)q0 * mu1;
  uint128_t xy020 = (uint128_t)q0 * mu2;
  uint128_t xy030 = (uint128_t)q0 * mu3;
  uint128_t xy040 = (uint128_t)q0 * mu4;
  uint128_t xy100 = (uint128_t)q1 * mu0;
  uint128_t xy110 = (uint128_t)q1 * mu1;
  uint128_t xy120 = (uint128_t)q1 * mu2;
  uint128_t xy130 = (uint128_t)q1 * mu3;
  uint128_t xy14 = (uint128_t)q1 * mu4;
  uint128_t xy200 = (uint128_t)q2 * mu0;
  uint128_t xy210 = (uint128_t)q2 * mu1;
  uint128_t xy220 = (uint128_t)q2 * mu2;
  uint128_t xy23 = (uint128_t)q2 * mu3;
  uint128_t xy24 = (uint128_t)q2 * mu4;
  uint128_t xy300 = (uint128_t)q3 * mu0;
  uint128_t xy310 = (uint128_t)q3 * mu1;
  uint128_t xy32 = (uint128_t)q3 * mu2;
  uint128_t xy33 = (uint128_t)q3 * mu3;
  uint128_t xy34 = (uint128_t)q3 * mu4;
  uint128_t xy400 = (uint128_t)q4 * mu0;
  uint128_t xy41 = (uint128_t)q4 * mu1;
  uint128_t xy42 = (uint128_t)q4 * mu2;
  uint128_t xy43 = (uint128_t)q4 * mu3;
  uint128_t xy44 = (uint128_t)q4 * mu4;
  uint128_t z01 = xy000;
  uint128_t z11 = xy010 + xy100;
  uint128_t z21 = xy020 + xy110 + xy200;
  uint128_t z31 = xy030 + xy120 + xy210 + xy300;
  uint128_t z41 = xy040 + xy130 + xy220 + xy310 + xy400;
  uint128_t z5 = xy14 + xy23 + xy32 + xy41;
  uint128_t z6 = xy24 + xy33 + xy42;
  uint128_t z7 = xy34 + xy43;
  uint128_t z8 = xy44;
  uint128_t carry0 = z01 >> (uint32_t)56U;
  uint64_t t100 = (uint64_t)z01 & (uint64_t)0xffffffffffffffU;
  uint128_t c00 = carry0;
  uint128_t carry1 = (z11 + c00) >> (uint32_t)56U;
  uint64_t t101 = (uint64_t)(z11 + c00) & (uint64_t)0xffffffffffffffU;
  uint128_t c10 = carry1;
  uint128_t carry2 = (z21 + c10) >> (uint32_t)56U;
  uint64_t t102 = (uint64_t)(z21 + c10) & (uint64_t)0xffffffffffffffU;
  uint128_t c20 = carry2;
  uint128_t carry3 = (z31 + c20) >> (uint32_t)56U;
  uint64_t t103 = (uint64_t)(z31 + c20) & (uint64_t)0xffffffffffffffU;
  uint128_t c30 = carry3;
  uint128_t carry4 = (z41 + c30) >> (uint32_t)56U;
  uint64_t t104 = (uint64_t)(z41 + c30) & (uint64_t)0xffffffffffffffU;
  uint128_t c40 = carry4;
  uint64_t t410 = t104;
  uint128_t carry5 = (z5 + c40) >> (uint32_t)56U;
  uint64_t t105 = (uint64_t)(z5 + c40) & (uint64_t)0xffffffffffffffU;
  uint128_t c5 = carry5;
  uint64_t t51 = t105;
  uint128_t carry6 = (z6 + c5) >> (uint32_t)56U;
  uint64_t t106 = (uint64_t)(z6 + c5) & (uint64_t)0xffffffffffffffU;
  uint128_t c6 = carry6;
  uint64_t t61 = t106;
  uint128_t carry7 = (z7 + c6) >> (uint32_t)56U;
  uint64_t t107 = (uint64_t)(z7 + c6) & (uint64_t)0xffffffffffffffU;
  uint128_t c7 = carry7;
  uint64_t t71 = t107;
  uint128_t carry8 = (z8 + c7) >> (uint32_t)56U;
  uint64_t t108 = (uint64_t)(z8 + c7) & (uint64_t)0xffffffffffffffU;
  uint128_t c8 = carry8;
  uint64_t t81 = t108;
  uint64_t t91 = (uint64_t)c8;
  uint64_t qmu4_ = t410;
  uint64_t qmu5_ = t51;
  uint64_t qmu6_ = t61;
  uint64_t qmu7_ = t71;
  uint64_t qmu8_ = t81;
  uint64_t qmu9_ = t91;
  uint64_t y_4 = (qmu5_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_4 = qmu4_ >> (uint32_t)40U;
  uint64_t z02 = x_4 | y_4;
  uint64_t y_5 = (qmu6_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_5 = qmu5_ >> (uint32_t)40U;
  uint64_t z12 = x_5 | y_5;
  uint64_t y_6 = (qmu7_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_6 = qmu6_ >> (uint32_t)40U;
  uint64_t z22 = x_6 | y_6;
  uint64_t y_7 = (qmu8_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_7 = qmu7_ >> (uint32_t)40U;
  uint64_t z32 = x_7 | y_7;
  uint64_t y_8 = (qmu9_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_8 = qmu8_ >> (uint32_t)40U;
  uint64_t z42 = x_8 | y_8;
  uint64_t qdiv0 = z02;
  uint64_t qdiv1 = z12;
  uint64_t qdiv2 = z22;
  uint64_t qdiv3 = z32;
  uint64_t qdiv4 = z42;
  uint64_t r0 = t0;
  uint64_t r1 = t1;
  uint64_t r2 = t2;
  uint64_t r3 = t3;
  uint64_t r4 = t4 & (uint64_t)0xffffffffffU;
  uint128_t xy00 = (uint128_t)qdiv0 * m0;
  uint128_t xy01 = (uint128_t)qdiv0 * m1;
  uint128_t xy02 = (uint128_t)qdiv0 * m2;
  uint128_t xy03 = (uint128_t)qdiv0 * m3;
  uint128_t xy04 = (uint128_t)qdiv0 * m4;
  uint128_t xy10 = (uint128_t)qdiv1 * m0;
  uint128_t xy11 = (uint128_t)qdiv1 * m1;
  uint128_t xy12 = (uint128_t)qdiv1 * m2;
  uint128_t xy13 = (uint128_t)qdiv1 * m3;
  uint128_t xy20 = (uint128_t)qdiv2 * m0;
  uint128_t xy21 = (uint128_t)qdiv2 * m1;
  uint128_t xy22 = (uint128_t)qdiv2 * m2;
  uint128_t xy30 = (uint128_t)qdiv3 * m0;
  uint128_t xy31 = (uint128_t)qdiv3 * m1;
  uint128_t xy40 = (uint128_t)qdiv4 * m0;
  uint128_t carry9 = xy00 >> (uint32_t)56U;
  uint64_t t109 = (uint64_t)xy00 & (uint64_t)0xffffffffffffffU;
  uint128_t c0 = carry9;
  uint64_t t010 = t109;
  uint128_t carry10 = (xy01 + xy10 + c0) >> (uint32_t)56U;
  uint64_t t1010 = (uint64_t)(xy01 + xy10 + c0) & (uint64_t)0xffffffffffffffU;
  uint128_t c11 = carry10;
  uint64_t t110 = t1010;
  uint128_t carry11 = (xy02 + xy11 + xy20 + c11) >> (uint32_t)56U;
  uint64_t t1011 = (uint64_t)(xy02 + xy11 + xy20 + c11) & (uint64_t)0xffffffffffffffU;
  uint128_t c21 = carry11;
  uint64_t t210 = t1011;
  uint128_t carry = (xy03 + xy12 + xy21 + xy30 + c21) >> (uint32_t)56U;
  uint64_t t1012 = (uint64_t)(xy03 + xy12 + xy21 + xy30 + c21) & (uint64_t)0xffffffffffffffU;
  uint128_t c31 = carry;
  uint64_t t310 = t1012;
  uint64_t t411 = (uint64_t)(xy04 + xy13 + xy22 + xy31 + xy40 + c31) & (uint64_t)0xffffffffffU;
  uint64_t qmul0 = t010;
  uint64_t qmul1 = t110;
  uint64_t qmul2 = t210;
  uint64_t qmul3 = t310;
  uint64_t qmul4 = t411;
  uint64_t b5 = (r0 - qmul0) >> (uint32_t)63U;
  uint64_t t1013 = (b5 << (uint32_t)56U) + r0 - qmul0;
  uint64_t c1 = b5;
  uint64_t t011 = t1013;
  uint64_t b6 = (r1 - (qmul1 + c1)) >> (uint32_t)63U;
  uint64_t t1014 = (b6 << (uint32_t)56U) + r1 - (qmul1 + c1);
  uint64_t c2 = b6;
  uint64_t t111 = t1014;
  uint64_t b7 = (r2 - (qmul2 + c2)) >> (uint32_t)63U;
  uint64_t t1015 = (b7 << (uint32_t)56U) + r2 - (qmul2 + c2);
  uint64_t c3 = b7;
  uint64_t t211 = t1015;
  uint64_t b8 = (r3 - (qmul3 + c3)) >> (uint32_t)63U;
  uint64_t t1016 = (b8 << (uint32_t)56U) + r3 - (qmul3 + c3);
  uint64_t c4 = b8;
  uint64_t t311 = t1016;
  uint64_t b9 = (r4 - (qmul4 + c4)) >> (uint32_t)63U;
  uint64_t t1017 = (b9 << (uint32_t)40U) + r4 - (qmul4 + c4);
  uint64_t t412 = t1017;
  uint64_t s0 = t011;
  uint64_t s1 = t111;
  uint64_t s2 = t211;
  uint64_t s3 = t311;
  uint64_t s4 = t412;
  uint64_t m01 = (uint64_t)0x12631a5cf5d3edU;
  uint64_t m11 = (uint64_t)0xf9dea2f79cd658U;
  uint64_t m21 = (uint64_t)0x000000000014deU;
  uint64_t m31 = (uint64_t)0x00000000000000U;
  uint64_t m41 = (uint64_t)0x00000010000000U;
  uint64_t y0 = m01;
  uint64_t y1 = m11;
  uint64_t y2 = m21;
  uint64_t y3 = m31;
  uint64_t y4 = m41;
  uint64_t b10 = (s0 - y0) >> (uint32_t)63U;
  uint64_t t1018 = (b10 << (uint32_t)56U) + s0 - y0;
  uint64_t b0 = b10;
  uint64_t t01 = t1018;
  uint64_t b11 = (s1 - (y1 + b0)) >> (uint32_t)63U;
  uint64_t t1019 = (b11 << (uint32_t)56U) + s1 - (y1 + b0);
  uint64_t b1 = b11;
  uint64_t t11 = t1019;
  uint64_t b12 = (s2 - (y2 + b1)) >> (uint32_t)63U;
  uint64_t t1020 = (b12 << (uint32_t)56U) + s2 - (y2 + b1);
  uint64_t b2 = b12;
  uint64_t t21 = t1020;
  uint64_t b13 = (s3 - (y3 + b2)) >> (uint32_t)63U;
  uint64_t t1021 = (b13 << (uint32_t)56U) + s3 - (y3 + b2);
  uint64_t b3 = b13;
  uint64_t t31 = t1021;
  uint64_t b = (s4 - (y4 + b3)) >> (uint32_t)63U;
  uint64_t t10 = (b << (uint32_t)56U) + s4 - (y4 + b3);
  uint64_t b4 = b;
  uint64_t t41 = t10;
  uint64_t mask = b4 - (uint64_t)1U;
  uint64_t z03 = s0 ^ (mask & (s0 ^ t01));
  uint64_t z13 = s1 ^ (mask & (s1 ^ t11));
  uint64_t z23 = s2 ^ (mask & (s2 ^ t21));
  uint64_t z33 = s3 ^ (mask & (s3 ^ t31));
  uint64_t z43 = s4 ^ (mask & (s4 ^ t41));
  uint64_t z04 = z03;
  uint64_t z14 = z13;
  uint64_t z24 = z23;
  uint64_t z34 = z33;
  uint64_t z44 = z43;
  uint64_t o0 = z04;
  uint64_t o1 = z14;
  uint64_t o2 = z24;
  uint64_t o3 = z34;
  uint64_t o4 = z44;
  uint64_t z0 = o0;
  uint64_t z1 = o1;
  uint64_t z2 = o2;
  uint64_t z3 = o3;
  uint64_t z4 = o4;
  z[0U] = z0;
  z[1U] = z1;
  z[2U] = z2;
  z[3U] = z3;
  z[4U] = z4;
}

static void Hacl_Impl_BignumQ_Mul_mul_modq(uint64_t *out, uint64_t *x, uint64_t *y)
{
  uint64_t x0 = x[0U];
  uint64_t x1 = x[1U];
  uint64_t x2 = x[2U];
  uint64_t x3 = x[3U];
  uint64_t x4 = x[4U];
  uint64_t y0 = y[0U];
  uint64_t y1 = y[1U];
  uint64_t y2 = y[2U];
  uint64_t y3 = y[3U];
  uint64_t y4 = y[4U];
  uint128_t xy000 = (uint128_t)x0 * y0;
  uint128_t xy010 = (uint128_t)x0 * y1;
  uint128_t xy020 = (uint128_t)x0 * y2;
  uint128_t xy030 = (uint128_t)x0 * y3;
  uint128_t xy040 = (uint128_t)x0 * y4;
  uint128_t xy100 = (uint128_t)x1 * y0;
  uint128_t xy110 = (uint128_t)x1 * y1;
  uint128_t xy120 = (uint128_t)x1 * y2;
  uint128_t xy130 = (uint128_t)x1 * y3;
  uint128_t xy140 = (uint128_t)x1 * y4;
  uint128_t xy200 = (uint128_t)x2 * y0;
  uint128_t xy210 = (uint128_t)x2 * y1;
  uint128_t xy220 = (uint128_t)x2 * y2;
  uint128_t xy230 = (uint128_t)x2 * y3;
  uint128_t xy240 = (uint128_t)x2 * y4;
  uint128_t xy300 = (uint128_t)x3 * y0;
  uint128_t xy310 = (uint128_t)x3 * y1;
  uint128_t xy320 = (uint128_t)x3 * y2;
  uint128_t xy330 = (uint128_t)x3 * y3;
  uint128_t xy340 = (uint128_t)x3 * y4;
  uint128_t xy400 = (uint128_t)x4 * y0;
  uint128_t xy410 = (uint128_t)x4 * y1;
  uint128_t xy420 = (uint128_t)x4 * y2;
  uint128_t xy430 = (uint128_t)x4 * y3;
  uint128_t xy440 = (uint128_t)x4 * y4;
  uint128_t z00 = xy000;
  uint128_t z10 = xy010 + xy100;
  uint128_t z20 = xy020 + xy110 + xy200;
  uint128_t z30 = xy030 + xy120 + xy210 + xy300;
  uint128_t z40 = xy040 + xy130 + xy220 + xy310 + xy400;
  uint128_t z50 = xy140 + xy230 + xy320 + xy410;
  uint128_t z60 = xy240 + xy330 + xy420;
  uint128_t z70 = xy340 + xy430;
  uint128_t z80 = xy440;
  uint128_t carry0 = z00 >> (uint32_t)56U;
  uint64_t t10 = (uint64_t)z00 & (uint64_t)0xffffffffffffffU;
  uint128_t c00 = carry0;
  uint64_t t00 = t10;
  uint128_t carry1 = (z10 + c00) >> (uint32_t)56U;
  uint64_t t11 = (uint64_t)(z10 + c00) & (uint64_t)0xffffffffffffffU;
  uint128_t c10 = carry1;
  uint64_t t12 = t11;
  uint128_t carry2 = (z20 + c10) >> (uint32_t)56U;
  uint64_t t13 = (uint64_t)(z20 + c10) & (uint64_t)0xffffffffffffffU;
  uint128_t c20 = carry2;
  uint64_t t20 = t13;
  uint128_t carry3 = (z30 + c20) >> (uint32_t)56U;
  uint64_t t14 = (uint64_t)(z30 + c20) & (uint64_t)0xffffffffffffffU;
  uint128_t c30 = carry3;
  uint64_t t30 = t14;
  uint128_t carry4 = (z40 + c30) >> (uint32_t)56U;
  uint64_t t15 = (uint64_t)(z40 + c30) & (uint64_t)0xffffffffffffffU;
  uint128_t c40 = carry4;
  uint64_t t40 = t15;
  uint128_t carry5 = (z50 + c40) >> (uint32_t)56U;
  uint64_t t16 = (uint64_t)(z50 + c40) & (uint64_t)0xffffffffffffffU;
  uint128_t c50 = carry5;
  uint64_t t50 = t16;
  uint128_t carry6 = (z60 + c50) >> (uint32_t)56U;
  uint64_t t17 = (uint64_t)(z60 + c50) & (uint64_t)0xffffffffffffffU;
  uint128_t c60 = carry6;
  uint64_t t60 = t17;
  uint128_t carry7 = (z70 + c60) >> (uint32_t)56U;
  uint64_t t18 = (uint64_t)(z70 + c60) & (uint64_t)0xffffffffffffffU;
  uint128_t c70 = carry7;
  uint64_t t70 = t18;
  uint128_t carry8 = (z80 + c70) >> (uint32_t)56U;
  uint64_t t19 = (uint64_t)(z80 + c70) & (uint64_t)0xffffffffffffffU;
  uint128_t c80 = carry8;
  uint64_t t80 = t19;
  uint64_t t90 = (uint64_t)c80;
  uint64_t r0 = t00;
  uint64_t r1 = t12;
  uint64_t r2 = t20;
  uint64_t r3 = t30;
  uint64_t r4 = t40;
  uint64_t r5 = t50;
  uint64_t r6 = t60;
  uint64_t r7 = t70;
  uint64_t r8 = t80;
  uint64_t r9 = t90;
  uint64_t m00 = (uint64_t)0x12631a5cf5d3edU;
  uint64_t m10 = (uint64_t)0xf9dea2f79cd658U;
  uint64_t m20 = (uint64_t)0x000000000014deU;
  uint64_t m30 = (uint64_t)0x00000000000000U;
  uint64_t m40 = (uint64_t)0x00000010000000U;
  uint64_t m0 = m00;
  uint64_t m1 = m10;
  uint64_t m2 = m20;
  uint64_t m3 = m30;
  uint64_t m4 = m40;
  uint64_t m010 = (uint64_t)0x9ce5a30a2c131bU;
  uint64_t m110 = (uint64_t)0x215d086329a7edU;
  uint64_t m210 = (uint64_t)0xffffffffeb2106U;
  uint64_t m310 = (uint64_t)0xffffffffffffffU;
  uint64_t m410 = (uint64_t)0x00000fffffffffU;
  uint64_t mu0 = m010;
  uint64_t mu1 = m110;
  uint64_t mu2 = m210;
  uint64_t mu3 = m310;
  uint64_t mu4 = m410;
  uint64_t y_ = (r5 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_ = r4 >> (uint32_t)24U;
  uint64_t z01 = x_ | y_;
  uint64_t y_0 = (r6 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_0 = r5 >> (uint32_t)24U;
  uint64_t z11 = x_0 | y_0;
  uint64_t y_1 = (r7 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_1 = r6 >> (uint32_t)24U;
  uint64_t z21 = x_1 | y_1;
  uint64_t y_2 = (r8 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_2 = r7 >> (uint32_t)24U;
  uint64_t z31 = x_2 | y_2;
  uint64_t y_3 = (r9 & (uint64_t)0xffffffU) << (uint32_t)32U;
  uint64_t x_3 = r8 >> (uint32_t)24U;
  uint64_t z41 = x_3 | y_3;
  uint64_t q0 = z01;
  uint64_t q1 = z11;
  uint64_t q2 = z21;
  uint64_t q3 = z31;
  uint64_t q4 = z41;
  uint128_t xy001 = (uint128_t)q0 * mu0;
  uint128_t xy011 = (uint128_t)q0 * mu1;
  uint128_t xy021 = (uint128_t)q0 * mu2;
  uint128_t xy031 = (uint128_t)q0 * mu3;
  uint128_t xy041 = (uint128_t)q0 * mu4;
  uint128_t xy101 = (uint128_t)q1 * mu0;
  uint128_t xy111 = (uint128_t)q1 * mu1;
  uint128_t xy121 = (uint128_t)q1 * mu2;
  uint128_t xy131 = (uint128_t)q1 * mu3;
  uint128_t xy14 = (uint128_t)q1 * mu4;
  uint128_t xy201 = (uint128_t)q2 * mu0;
  uint128_t xy211 = (uint128_t)q2 * mu1;
  uint128_t xy221 = (uint128_t)q2 * mu2;
  uint128_t xy23 = (uint128_t)q2 * mu3;
  uint128_t xy24 = (uint128_t)q2 * mu4;
  uint128_t xy301 = (uint128_t)q3 * mu0;
  uint128_t xy311 = (uint128_t)q3 * mu1;
  uint128_t xy32 = (uint128_t)q3 * mu2;
  uint128_t xy33 = (uint128_t)q3 * mu3;
  uint128_t xy34 = (uint128_t)q3 * mu4;
  uint128_t xy401 = (uint128_t)q4 * mu0;
  uint128_t xy41 = (uint128_t)q4 * mu1;
  uint128_t xy42 = (uint128_t)q4 * mu2;
  uint128_t xy43 = (uint128_t)q4 * mu3;
  uint128_t xy44 = (uint128_t)q4 * mu4;
  uint128_t z02 = xy001;
  uint128_t z12 = xy011 + xy101;
  uint128_t z22 = xy021 + xy111 + xy201;
  uint128_t z32 = xy031 + xy121 + xy211 + xy301;
  uint128_t z42 = xy041 + xy131 + xy221 + xy311 + xy401;
  uint128_t z5 = xy14 + xy23 + xy32 + xy41;
  uint128_t z6 = xy24 + xy33 + xy42;
  uint128_t z7 = xy34 + xy43;
  uint128_t z8 = xy44;
  uint128_t carry9 = z02 >> (uint32_t)56U;
  uint64_t t21 = (uint64_t)z02 & (uint64_t)0xffffffffffffffU;
  uint128_t c01 = carry9;
  uint128_t carry10 = (z12 + c01) >> (uint32_t)56U;
  uint64_t t22 = (uint64_t)(z12 + c01) & (uint64_t)0xffffffffffffffU;
  uint128_t c11 = carry10;
  uint128_t carry11 = (z22 + c11) >> (uint32_t)56U;
  uint64_t t23 = (uint64_t)(z22 + c11) & (uint64_t)0xffffffffffffffU;
  uint128_t c21 = carry11;
  uint128_t carry12 = (z32 + c21) >> (uint32_t)56U;
  uint64_t t24 = (uint64_t)(z32 + c21) & (uint64_t)0xffffffffffffffU;
  uint128_t c31 = carry12;
  uint128_t carry13 = (z42 + c31) >> (uint32_t)56U;
  uint64_t t25 = (uint64_t)(z42 + c31) & (uint64_t)0xffffffffffffffU;
  uint128_t c41 = carry13;
  uint64_t t41 = t25;
  uint128_t carry14 = (z5 + c41) >> (uint32_t)56U;
  uint64_t t26 = (uint64_t)(z5 + c41) & (uint64_t)0xffffffffffffffU;
  uint128_t c5 = carry14;
  uint64_t t5 = t26;
  uint128_t carry15 = (z6 + c5) >> (uint32_t)56U;
  uint64_t t27 = (uint64_t)(z6 + c5) & (uint64_t)0xffffffffffffffU;
  uint128_t c6 = carry15;
  uint64_t t6 = t27;
  uint128_t carry16 = (z7 + c6) >> (uint32_t)56U;
  uint64_t t28 = (uint64_t)(z7 + c6) & (uint64_t)0xffffffffffffffU;
  uint128_t c7 = carry16;
  uint64_t t7 = t28;
  uint128_t carry17 = (z8 + c7) >> (uint32_t)56U;
  uint64_t t29 = (uint64_t)(z8 + c7) & (uint64_t)0xffffffffffffffU;
  uint128_t c8 = carry17;
  uint64_t t8 = t29;
  uint64_t t9 = (uint64_t)c8;
  uint64_t qmu4_ = t41;
  uint64_t qmu5_ = t5;
  uint64_t qmu6_ = t6;
  uint64_t qmu7_ = t7;
  uint64_t qmu8_ = t8;
  uint64_t qmu9_ = t9;
  uint64_t y_4 = (qmu5_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_4 = qmu4_ >> (uint32_t)40U;
  uint64_t z03 = x_4 | y_4;
  uint64_t y_5 = (qmu6_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_5 = qmu5_ >> (uint32_t)40U;
  uint64_t z13 = x_5 | y_5;
  uint64_t y_6 = (qmu7_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_6 = qmu6_ >> (uint32_t)40U;
  uint64_t z23 = x_6 | y_6;
  uint64_t y_7 = (qmu8_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_7 = qmu7_ >> (uint32_t)40U;
  uint64_t z33 = x_7 | y_7;
  uint64_t y_8 = (qmu9_ & (uint64_t)0xffffffffffU) << (uint32_t)16U;
  uint64_t x_8 = qmu8_ >> (uint32_t)40U;
  uint64_t z43 = x_8 | y_8;
  uint64_t qdiv0 = z03;
  uint64_t qdiv1 = z13;
  uint64_t qdiv2 = z23;
  uint64_t qdiv3 = z33;
  uint64_t qdiv4 = z43;
  uint64_t r01 = r0;
  uint64_t r11 = r1;
  uint64_t r21 = r2;
  uint64_t r31 = r3;
  uint64_t r41 = r4 & (uint64_t)0xffffffffffU;
  uint128_t xy00 = (uint128_t)qdiv0 * m0;
  uint128_t xy01 = (uint128_t)qdiv0 * m1;
  uint128_t xy02 = (uint128_t)qdiv0 * m2;
  uint128_t xy03 = (uint128_t)qdiv0 * m3;
  uint128_t xy04 = (uint128_t)qdiv0 * m4;
  uint128_t xy10 = (uint128_t)qdiv1 * m0;
  uint128_t xy11 = (uint128_t)qdiv1 * m1;
  uint128_t xy12 = (uint128_t)qdiv1 * m2;
  uint128_t xy13 = (uint128_t)qdiv1 * m3;
  uint128_t xy20 = (uint128_t)qdiv2 * m0;
  uint128_t xy21 = (uint128_t)qdiv2 * m1;
  uint128_t xy22 = (uint128_t)qdiv2 * m2;
  uint128_t xy30 = (uint128_t)qdiv3 * m0;
  uint128_t xy31 = (uint128_t)qdiv3 * m1;
  uint128_t xy40 = (uint128_t)qdiv4 * m0;
  uint128_t carry18 = xy00 >> (uint32_t)56U;
  uint64_t t31 = (uint64_t)xy00 & (uint64_t)0xffffffffffffffU;
  uint128_t c0 = carry18;
  uint64_t t01 = t31;
  uint128_t carry19 = (xy01 + xy10 + c0) >> (uint32_t)56U;
  uint64_t t32 = (uint64_t)(xy01 + xy10 + c0) & (uint64_t)0xffffffffffffffU;
  uint128_t c12 = carry19;
  uint64_t t110 = t32;
  uint128_t carry20 = (xy02 + xy11 + xy20 + c12) >> (uint32_t)56U;
  uint64_t t33 = (uint64_t)(xy02 + xy11 + xy20 + c12) & (uint64_t)0xffffffffffffffU;
  uint128_t c22 = carry20;
  uint64_t t210 = t33;
  uint128_t carry = (xy03 + xy12 + xy21 + xy30 + c22) >> (uint32_t)56U;
  uint64_t t34 = (uint64_t)(xy03 + xy12 + xy21 + xy30 + c22) & (uint64_t)0xffffffffffffffU;
  uint128_t c32 = carry;
  uint64_t t35 = t34;
  uint64_t t42 = (uint64_t)(xy04 + xy13 + xy22 + xy31 + xy40 + c32) & (uint64_t)0xffffffffffU;
  uint64_t qmul0 = t01;
  uint64_t qmul1 = t110;
  uint64_t qmul2 = t210;
  uint64_t qmul3 = t35;
  uint64_t qmul4 = t42;
  uint64_t b5 = (r01 - qmul0) >> (uint32_t)63U;
  uint64_t t36 = (b5 << (uint32_t)56U) + r01 - qmul0;
  uint64_t c1 = b5;
  uint64_t t02 = t36;
  uint64_t b6 = (r11 - (qmul1 + c1)) >> (uint32_t)63U;
  uint64_t t37 = (b6 << (uint32_t)56U) + r11 - (qmul1 + c1);
  uint64_t c2 = b6;
  uint64_t t111 = t37;
  uint64_t b7 = (r21 - (qmul2 + c2)) >> (uint32_t)63U;
  uint64_t t38 = (b7 << (uint32_t)56U) + r21 - (qmul2 + c2);
  uint64_t c3 = b7;
  uint64_t t211 = t38;
  uint64_t b8 = (r31 - (qmul3 + c3)) >> (uint32_t)63U;
  uint64_t t39 = (b8 << (uint32_t)56U) + r31 - (qmul3 + c3);
  uint64_t c4 = b8;
  uint64_t t310 = t39;
  uint64_t b9 = (r41 - (qmul4 + c4)) >> (uint32_t)63U;
  uint64_t t43 = (b9 << (uint32_t)40U) + r41 - (qmul4 + c4);
  uint64_t t44 = t43;
  uint64_t s0 = t02;
  uint64_t s1 = t111;
  uint64_t s2 = t211;
  uint64_t s3 = t310;
  uint64_t s4 = t44;
  uint64_t m01 = (uint64_t)0x12631a5cf5d3edU;
  uint64_t m11 = (uint64_t)0xf9dea2f79cd658U;
  uint64_t m21 = (uint64_t)0x000000000014deU;
  uint64_t m31 = (uint64_t)0x00000000000000U;
  uint64_t m41 = (uint64_t)0x00000010000000U;
  uint64_t y01 = m01;
  uint64_t y11 = m11;
  uint64_t y21 = m21;
  uint64_t y31 = m31;
  uint64_t y41 = m41;
  uint64_t b10 = (s0 - y01) >> (uint32_t)63U;
  uint64_t t45 = (b10 << (uint32_t)56U) + s0 - y01;
  uint64_t b0 = b10;
  uint64_t t0 = t45;
  uint64_t b11 = (s1 - (y11 + b0)) >> (uint32_t)63U;
  uint64_t t46 = (b11 << (uint32_t)56U) + s1 - (y11 + b0);
  uint64_t b1 = b11;
  uint64_t t1 = t46;
  uint64_t b12 = (s2 - (y21 + b1)) >> (uint32_t)63U;
  uint64_t t47 = (b12 << (uint32_t)56U) + s2 - (y21 + b1);
  uint64_t b2 = b12;
  uint64_t t2 = t47;
  uint64_t b13 = (s3 - (y31 + b2)) >> (uint32_t)63U;
  uint64_t t48 = (b13 << (uint32_t)56U) + s3 - (y31 + b2);
  uint64_t b3 = b13;
  uint64_t t3 = t48;
  uint64_t b = (s4 - (y41 + b3)) >> (uint32_t)63U;
  uint64_t t = (b << (uint32_t)56U) + s4 - (y41 + b3);
  uint64_t b4 = b;
  uint64_t t4 = t;
  uint64_t mask = b4 - (uint64_t)1U;
  uint64_t z04 = s0 ^ (mask & (s0 ^ t0));
  uint64_t z14 = s1 ^ (mask & (s1 ^ t1));
  uint64_t z24 = s2 ^ (mask & (s2 ^ t2));
  uint64_t z34 = s3 ^ (mask & (s3 ^ t3));
  uint64_t z44 = s4 ^ (mask & (s4 ^ t4));
  uint64_t z05 = z04;
  uint64_t z15 = z14;
  uint64_t z25 = z24;
  uint64_t z35 = z34;
  uint64_t z45 = z44;
  uint64_t o00 = z05;
  uint64_t o10 = z15;
  uint64_t o20 = z25;
  uint64_t o30 = z35;
  uint64_t o40 = z45;
  uint64_t o0 = o00;
  uint64_t o1 = o10;
  uint64_t o2 = o20;
  uint64_t o3 = o30;
  uint64_t o4 = o40;
  uint64_t z0 = o0;
  uint64_t z1 = o1;
  uint64_t z2 = o2;
  uint64_t z3 = o3;
  uint64_t z4 = o4;
  out[0U] = z0;
  out[1U] = z1;
  out[2U] = z2;
  out[3U] = z3;
  out[4U] = z4;
}

static void Hacl_Impl_BignumQ_Mul_add_modq(uint64_t *out, uint64_t *x, uint64_t *y)
{
  uint64_t x0 = x[0U];
  uint64_t x1 = x[1U];
  uint64_t x2 = x[2U];
  uint64_t x3 = x[3U];
  uint64_t x4 = x[4U];
  uint64_t y0 = y[0U];
  uint64_t y1 = y[1U];
  uint64_t y2 = y[2U];
  uint64_t y3 = y[3U];
  uint64_t y4 = y[4U];
  uint64_t carry0 = (x0 + y0) >> (uint32_t)56U;
  uint64_t t0 = (x0 + y0) & (uint64_t)0xffffffffffffffU;
  uint64_t t00 = t0;
  uint64_t c0 = carry0;
  uint64_t carry1 = (x1 + y1 + c0) >> (uint32_t)56U;
  uint64_t t1 = (x1 + y1 + c0) & (uint64_t)0xffffffffffffffU;
  uint64_t t10 = t1;
  uint64_t c1 = carry1;
  uint64_t carry2 = (x2 + y2 + c1) >> (uint32_t)56U;
  uint64_t t2 = (x2 + y2 + c1) & (uint64_t)0xffffffffffffffU;
  uint64_t t20 = t2;
  uint64_t c2 = carry2;
  uint64_t carry = (x3 + y3 + c2) >> (uint32_t)56U;
  uint64_t t3 = (x3 + y3 + c2) & (uint64_t)0xffffffffffffffU;
  uint64_t t30 = t3;
  uint64_t c3 = carry;
  uint64_t t4 = x4 + y4 + c3;
  uint64_t m0 = (uint64_t)0x12631a5cf5d3edU;
  uint64_t m1 = (uint64_t)0xf9dea2f79cd658U;
  uint64_t m2 = (uint64_t)0x000000000014deU;
  uint64_t m3 = (uint64_t)0x00000000000000U;
  uint64_t m4 = (uint64_t)0x00000010000000U;
  uint64_t y01 = m0;
  uint64_t y11 = m1;
  uint64_t y21 = m2;
  uint64_t y31 = m3;
  uint64_t y41 = m4;
  uint64_t b5 = (t00 - y01) >> (uint32_t)63U;
  uint64_t t5 = (b5 << (uint32_t)56U) + t00 - y01;
  uint64_t b0 = b5;
  uint64_t t01 = t5;
  uint64_t b6 = (t10 - (y11 + b0)) >> (uint32_t)63U;
  uint64_t t6 = (b6 << (uint32_t)56U) + t10 - (y11 + b0);
  uint64_t b1 = b6;
  uint64_t t11 = t6;
  uint64_t b7 = (t20 - (y21 + b1)) >> (uint32_t)63U;
  uint64_t t7 = (b7 << (uint32_t)56U) + t20 - (y21 + b1);
  uint64_t b2 = b7;
  uint64_t t21 = t7;
  uint64_t b8 = (t30 - (y31 + b2)) >> (uint32_t)63U;
  uint64_t t8 = (b8 << (uint32_t)56U) + t30 - (y31 + b2);
  uint64_t b3 = b8;
  uint64_t t31 = t8;
  uint64_t b = (t4 - (y41 + b3)) >> (uint32_t)63U;
  uint64_t t = (b << (uint32_t)56U) + t4 - (y41 + b3);
  uint64_t b4 = b;
  uint64_t t41 = t;
  uint64_t mask = b4 - (uint64_t)1U;
  uint64_t z00 = t00 ^ (mask & (t00 ^ t01));
  uint64_t z10 = t10 ^ (mask & (t10 ^ t11));
  uint64_t z20 = t20 ^ (mask & (t20 ^ t21));
  uint64_t z30 = t30 ^ (mask & (t30 ^ t31));
  uint64_t z40 = t4 ^ (mask & (t4 ^ t41));
  uint64_t z01 = z00;
  uint64_t z11 = z10;
  uint64_t z21 = z20;
  uint64_t z31 = z30;
  uint64_t z41 = z40;
  uint64_t o0 = z01;
  uint64_t o1 = z11;
  uint64_t o2 = z21;
  uint64_t o3 = z31;
  uint64_t o4 = z41;
  uint64_t z0 = o0;
  uint64_t z1 = o1;
  uint64_t z2 = o2;
  uint64_t z3 = o3;
  uint64_t z4 = o4;
  out[0U] = z0;
  out[1U] = z1;
  out[2U] = z2;
  out[3U] = z3;
  out[4U] = z4;
}

static uint64_t Hacl_Impl_Load56_hload56_le(uint8_t *b, uint32_t off)
{
  uint8_t *b8 = b + off;
  uint64_t u = load64_le(b8);
  uint64_t z = u;
  return z & (uint64_t)0xffffffffffffffU;
}

static void Hacl_Impl_Load56_load_64_bytes(uint64_t *out, uint8_t *b)
{
  uint64_t b0 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)0U);
  uint64_t b1 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)7U);
  uint64_t b2 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)14U);
  uint64_t b3 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)21U);
  uint64_t b4 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)28U);
  uint64_t b5 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)35U);
  uint64_t b6 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)42U);
  uint64_t b7 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)49U);
  uint64_t b8 = Hacl_Impl_Load56_hload56_le(b, (uint32_t)56U);
  uint8_t b63 = b[63U];
  uint64_t b9 = (uint64_t)b63;
  out[0U] = b0;
  out[1U] = b1;
  out[2U] = b2;
  out[3U] = b3;
  out[4U] = b4;
  out[5U] = b5;
  out[6U] = b6;
  out[7U] = b7;
  out[8U] = b8;
  out[9U] = b9;
}

static uint64_t Hacl_Impl_Load56_hload56_le_(uint8_t *b, uint32_t off)
{
  uint8_t *b8 = b + off;
  uint64_t u = load64_le(b8);
  uint64_t z = u;
  return z & (uint64_t)0xffffffffffffffU;
}

static void Hacl_Impl_Load56_load_32_bytes(uint64_t *out, uint8_t *b)
{
  uint64_t b0 = Hacl_Impl_Load56_hload56_le_(b, (uint32_t)0U);
  uint64_t b1 = Hacl_Impl_Load56_hload56_le_(b, (uint32_t)7U);
  uint64_t b2 = Hacl_Impl_Load56_hload56_le_(b, (uint32_t)14U);
  uint64_t b3 = Hacl_Impl_Load56_hload56_le_(b, (uint32_t)21U);
  uint32_t u = load32_le(b + (uint32_t)28U);
  uint32_t b4 = u;
  uint64_t b41 = (uint64_t)b4;
  out[0U] = b0;
  out[1U] = b1;
  out[2U] = b2;
  out[3U] = b3;
  out[4U] = b41;
}

static void Hacl_Impl_Store56_hstore56_le(uint8_t *out, uint32_t off, uint64_t x)
{
  uint8_t *b8 = out + off;
  store64_le(b8, x);
}

static void Hacl_Impl_Store56_store_56(uint8_t *out, uint64_t *b)
{
  uint64_t b0 = b[0U];
  uint64_t b1 = b[1U];
  uint64_t b2 = b[2U];
  uint64_t b3 = b[3U];
  uint64_t b4 = b[4U];
  uint32_t b4_ = (uint32_t)b4;
  Hacl_Impl_Store56_hstore56_le(out, (uint32_t)0U, b0);
  Hacl_Impl_Store56_hstore56_le(out, (uint32_t)7U, b1);
  Hacl_Impl_Store56_hstore56_le(out, (uint32_t)14U, b2);
  Hacl_Impl_Store56_hstore56_le(out, (uint32_t)21U, b3);
  store32_le(out + (uint32_t)28U, b4_);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_pre_msg(
  uint8_t *h1,
  uint8_t *prefix,
  uint32_t len,
  uint8_t *input
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)32U);
  uint8_t pre_msg[len + (uint32_t)32U];
  memset(pre_msg, 0U, (len + (uint32_t)32U) * sizeof pre_msg[0U]);
  memcpy(pre_msg, prefix, (uint32_t)32U * sizeof prefix[0U]);
  memcpy(pre_msg + (uint32_t)32U, input, len * sizeof input[0U]);
  Hacl_Hash_SHA2_hash_512(pre_msg, len + (uint32_t)32U, h1);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_pre_pre2_msg(
  uint8_t *h1,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint32_t len,
  uint8_t *input
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)64U);
  uint8_t pre_msg[len + (uint32_t)64U];
  memset(pre_msg, 0U, (len + (uint32_t)64U) * sizeof pre_msg[0U]);
  memcpy(pre_msg, prefix, (uint32_t)32U * sizeof prefix[0U]);
  memcpy(pre_msg + (uint32_t)32U, prefix2, (uint32_t)32U * sizeof prefix2[0U]);
  memcpy(pre_msg + (uint32_t)64U, input, len * sizeof input[0U]);
  Hacl_Hash_SHA2_hash_512(pre_msg, len + (uint32_t)64U, h1);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_modq_pre(
  uint64_t *out,
  uint8_t *prefix,
  uint32_t len,
  uint8_t *input
)
{
  uint64_t tmp[10U] = { 0U };
  uint8_t hash1[64U] = { 0U };
  Hacl_Impl_SHA512_ModQ_sha512_pre_msg(hash1, prefix, len, input);
  Hacl_Impl_Load56_load_64_bytes(tmp, hash1);
  Hacl_Impl_BignumQ_Mul_barrett_reduction(out, tmp);
}

static void
Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2(
  uint64_t *out,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint32_t len,
  uint8_t *input
)
{
  uint64_t tmp[10U] = { 0U };
  uint8_t hash1[64U] = { 0U };
  Hacl_Impl_SHA512_ModQ_sha512_pre_pre2_msg(hash1, prefix, prefix2, len, input);
  Hacl_Impl_Load56_load_64_bytes(tmp, hash1);
  Hacl_Impl_BignumQ_Mul_barrett_reduction(out, tmp);
}

static void Hacl_Impl_Ed25519_Sign_Steps_point_mul_g_compress(uint8_t *out, uint8_t *s)
{
  uint64_t tmp[20U] = { 0U };
  Hacl_Impl_Ed25519_Ladder_point_mul_g(tmp, s);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, tmp);
}

static void Hacl_Impl_Ed25519_Sign_Steps_sign_step_1(uint8_t *secret1, uint8_t *tmp_bytes)
{
  uint8_t *a__ = tmp_bytes + (uint32_t)96U;
  uint8_t *apre = tmp_bytes + (uint32_t)224U;
  uint8_t *a = apre;
  Hacl_Impl_Ed25519_SecretExpand_secret_expand(apre, secret1);
  Hacl_Impl_Ed25519_Sign_Steps_point_mul_g_compress(a__, a);
}

static void
Hacl_Impl_Ed25519_Sign_Steps_sign_step_2(
  uint32_t len,
  uint8_t *msg,
  uint8_t *tmp_bytes,
  uint64_t *tmp_ints
)
{
  uint64_t *r = tmp_ints + (uint32_t)20U;
  uint8_t *apre = tmp_bytes + (uint32_t)224U;
  uint8_t *prefix = apre + (uint32_t)32U;
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre(r, prefix, len, msg);
}

static void Hacl_Impl_Ed25519_Sign_Steps_sign_step_3(uint8_t *tmp_bytes, uint64_t *tmp_ints)
{
  uint8_t rb[32U] = { 0U };
  uint64_t *r = tmp_ints + (uint32_t)20U;
  uint8_t *rs_ = tmp_bytes + (uint32_t)160U;
  Hacl_Impl_Store56_store_56(rb, r);
  Hacl_Impl_Ed25519_Sign_Steps_point_mul_g_compress(rs_, rb);
}

static void
Hacl_Impl_Ed25519_Sign_Steps_sign_step_4(
  uint32_t len,
  uint8_t *msg,
  uint8_t *tmp_bytes,
  uint64_t *tmp_ints
)
{
  uint64_t *h1 = tmp_ints + (uint32_t)60U;
  uint8_t *a__ = tmp_bytes + (uint32_t)96U;
  uint8_t *rs_ = tmp_bytes + (uint32_t)160U;
  Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2(h1, rs_, a__, len, msg);
}

static void Hacl_Impl_Ed25519_Sign_Steps_sign_step_5(uint8_t *tmp_bytes, uint64_t *tmp_ints)
{
  uint64_t *r = tmp_ints + (uint32_t)20U;
  uint64_t *aq = tmp_ints + (uint32_t)45U;
  uint64_t *ha = tmp_ints + (uint32_t)50U;
  uint64_t *s = tmp_ints + (uint32_t)55U;
  uint64_t *h1 = tmp_ints + (uint32_t)60U;
  uint8_t *s_ = tmp_bytes + (uint32_t)192U;
  uint8_t *a = tmp_bytes + (uint32_t)224U;
  Hacl_Impl_Load56_load_32_bytes(aq, a);
  Hacl_Impl_BignumQ_Mul_mul_modq(ha, h1, aq);
  Hacl_Impl_BignumQ_Mul_add_modq(s, r, ha);
  Hacl_Impl_Store56_store_56(s_, s);
}

static void Hacl_Impl_Ed25519_Pow2_252m2_pow2_252m2(uint64_t *out, uint64_t *z)
{
  uint64_t buf1[20U] = { 0U };
  uint64_t *a = buf1;
  uint64_t *t00 = buf1 + (uint32_t)5U;
  uint64_t *b0 = buf1 + (uint32_t)10U;
  uint64_t *c0 = buf1 + (uint32_t)15U;
  Hacl_Bignum25519_fsquare_times(a, z, (uint32_t)1U);
  Hacl_Bignum25519_fsquare_times(t00, a, (uint32_t)2U);
  Hacl_Bignum25519_fmul(b0, t00, z);
  Hacl_Bignum25519_fmul(a, b0, a);
  Hacl_Bignum25519_fsquare_times(t00, a, (uint32_t)1U);
  Hacl_Bignum25519_fmul(b0, t00, b0);
  Hacl_Bignum25519_fsquare_times(t00, b0, (uint32_t)5U);
  Hacl_Bignum25519_fmul(b0, t00, b0);
  Hacl_Bignum25519_fsquare_times(t00, b0, (uint32_t)10U);
  Hacl_Bignum25519_fmul(c0, t00, b0);
  Hacl_Bignum25519_fsquare_times(t00, c0, (uint32_t)20U);
  Hacl_Bignum25519_fmul(t00, t00, c0);
  Hacl_Bignum25519_fsquare_times_inplace(t00, (uint32_t)10U);
  Hacl_Bignum25519_fmul(b0, t00, b0);
  Hacl_Bignum25519_fsquare_times(t00, b0, (uint32_t)50U);
  uint64_t *a0 = buf1;
  uint64_t *t0 = buf1 + (uint32_t)5U;
  uint64_t *b = buf1 + (uint32_t)10U;
  uint64_t *c = buf1 + (uint32_t)15U;
  Hacl_Bignum25519_fsquare_times(a0, z, (uint32_t)1U);
  Hacl_Bignum25519_fmul(c, t0, b);
  Hacl_Bignum25519_fsquare_times(t0, c, (uint32_t)100U);
  Hacl_Bignum25519_fmul(t0, t0, c);
  Hacl_Bignum25519_fsquare_times_inplace(t0, (uint32_t)50U);
  Hacl_Bignum25519_fmul(t0, t0, b);
  Hacl_Bignum25519_fsquare_times_inplace(t0, (uint32_t)2U);
  Hacl_Bignum25519_fmul(out, t0, a0);
}

static bool Hacl_Impl_Ed25519_RecoverX_is_0(uint64_t *x)
{
  uint64_t x0 = x[0U];
  uint64_t x1 = x[1U];
  uint64_t x2 = x[2U];
  uint64_t x3 = x[3U];
  uint64_t x4 = x[4U];
  return
    x0
    == (uint64_t)0U
    && x1 == (uint64_t)0U
    && x2 == (uint64_t)0U
    && x3 == (uint64_t)0U
    && x4 == (uint64_t)0U;
}

static void Hacl_Impl_Ed25519_RecoverX_mul_modp_sqrt_m1(uint64_t *x)
{
  uint64_t sqrt_m1[5U] = { 0U };
  sqrt_m1[0U] = (uint64_t)0x00061b274a0ea0b0U;
  sqrt_m1[1U] = (uint64_t)0x0000d5a5fc8f189dU;
  sqrt_m1[2U] = (uint64_t)0x0007ef5e9cbd0c60U;
  sqrt_m1[3U] = (uint64_t)0x00078595a6804c9eU;
  sqrt_m1[4U] = (uint64_t)0x0002b8324804fc1dU;
  Hacl_Bignum25519_fmul(x, x, sqrt_m1);
}

static bool Hacl_Impl_Ed25519_RecoverX_recover_x(uint64_t *x, uint64_t *y, uint64_t sign1)
{
  uint64_t tmp[20U] = { 0U };
  uint64_t *x2 = tmp;
  uint64_t x00 = y[0U];
  uint64_t x1 = y[1U];
  uint64_t x21 = y[2U];
  uint64_t x30 = y[3U];
  uint64_t x4 = y[4U];
  bool
  b =
    x00
    >= (uint64_t)0x7ffffffffffedU
    && x1 == (uint64_t)0x7ffffffffffffU
    && x21 == (uint64_t)0x7ffffffffffffU
    && x30 == (uint64_t)0x7ffffffffffffU
    && x4 == (uint64_t)0x7ffffffffffffU;
  bool res;
  if (b)
  {
    res = false;
  }
  else
  {
    uint64_t tmp1[25U] = { 0U };
    uint64_t *one1 = tmp1;
    uint64_t *y2 = tmp1 + (uint32_t)5U;
    uint64_t *dyyi = tmp1 + (uint32_t)10U;
    uint64_t *dyy = tmp1 + (uint32_t)15U;
    one1[0U] = (uint64_t)1U;
    one1[1U] = (uint64_t)0U;
    one1[2U] = (uint64_t)0U;
    one1[3U] = (uint64_t)0U;
    one1[4U] = (uint64_t)0U;
    Hacl_Bignum25519_fsquare(y2, y);
    Hacl_Bignum25519_times_d(dyy, y2);
    Hacl_Bignum25519_fsum(dyy, one1);
    Hacl_Bignum25519_reduce_513(dyy);
    Hacl_Bignum25519_inverse(dyyi, dyy);
    Hacl_Bignum25519_fdifference(one1, y2);
    Hacl_Bignum25519_fmul(x2, one1, dyyi);
    Hacl_Bignum25519_reduce(x2);
    bool x2_is_0 = Hacl_Impl_Ed25519_RecoverX_is_0(x2);
    uint8_t z;
    if (x2_is_0)
    {
      if (sign1 == (uint64_t)0U)
      {
        x[0U] = (uint64_t)0U;
        x[1U] = (uint64_t)0U;
        x[2U] = (uint64_t)0U;
        x[3U] = (uint64_t)0U;
        x[4U] = (uint64_t)0U;
        z = (uint8_t)1U;
      }
      else
      {
        z = (uint8_t)0U;
      }
    }
    else
    {
      z = (uint8_t)2U;
    }
    if (z == (uint8_t)0U)
    {
      res = false;
    }
    else if (z == (uint8_t)1U)
    {
      res = true;
    }
    else
    {
      uint64_t *x210 = tmp;
      uint64_t *x31 = tmp + (uint32_t)5U;
      uint64_t *t00 = tmp + (uint32_t)10U;
      uint64_t *t10 = tmp + (uint32_t)15U;
      Hacl_Impl_Ed25519_Pow2_252m2_pow2_252m2(x31, x210);
      Hacl_Bignum25519_fsquare(t00, x31);
      memcpy(t10, x210, (uint32_t)5U * sizeof x210[0U]);
      Hacl_Bignum25519_fdifference(t10, t00);
      Hacl_Bignum25519_reduce_513(t10);
      Hacl_Bignum25519_reduce(t10);
      bool t1_is_0 = Hacl_Impl_Ed25519_RecoverX_is_0(t10);
      if (!t1_is_0)
      {
        Hacl_Impl_Ed25519_RecoverX_mul_modp_sqrt_m1(x31);
      }
      uint64_t *x211 = tmp;
      uint64_t *x3 = tmp + (uint32_t)5U;
      uint64_t *t01 = tmp + (uint32_t)10U;
      uint64_t *t1 = tmp + (uint32_t)15U;
      Hacl_Bignum25519_fsquare(t01, x3);
      memcpy(t1, x211, (uint32_t)5U * sizeof x211[0U]);
      Hacl_Bignum25519_fdifference(t1, t01);
      Hacl_Bignum25519_reduce_513(t1);
      Hacl_Bignum25519_reduce(t1);
      bool z1 = Hacl_Impl_Ed25519_RecoverX_is_0(t1);
      if (z1 == false)
      {
        res = false;
      }
      else
      {
        uint64_t *x32 = tmp + (uint32_t)5U;
        uint64_t *t0 = tmp + (uint32_t)10U;
        Hacl_Bignum25519_reduce(x32);
        uint64_t x0 = x32[0U];
        uint64_t x01 = x0 & (uint64_t)1U;
        if (!(x01 == sign1))
        {
          t0[0U] = (uint64_t)0U;
          t0[1U] = (uint64_t)0U;
          t0[2U] = (uint64_t)0U;
          t0[3U] = (uint64_t)0U;
          t0[4U] = (uint64_t)0U;
          Hacl_Bignum25519_fdifference(x32, t0);
          Hacl_Bignum25519_reduce_513(x32);
          Hacl_Bignum25519_reduce(x32);
        }
        memcpy(x, x32, (uint32_t)5U * sizeof x32[0U]);
        res = true;
      }
    }
  }
  bool res0 = res;
  return res0;
}

static bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(uint64_t *out, uint8_t *s)
{
  uint64_t tmp[10U] = { 0U };
  uint64_t *y = tmp;
  uint64_t *x = tmp + (uint32_t)5U;
  uint8_t s31 = s[31U];
  uint8_t z = s31 >> (uint32_t)7U;
  uint64_t sign1 = (uint64_t)z;
  Hacl_Bignum25519_load_51(y, s);
  bool z0 = Hacl_Impl_Ed25519_RecoverX_recover_x(x, y, sign1);
  bool res;
  if (z0 == false)
  {
    res = false;
  }
  else
  {
    uint64_t *outx = out;
    uint64_t *outy = out + (uint32_t)5U;
    uint64_t *outz = out + (uint32_t)10U;
    uint64_t *outt = out + (uint32_t)15U;
    memcpy(outx, x, (uint32_t)5U * sizeof x[0U]);
    memcpy(outy, y, (uint32_t)5U * sizeof y[0U]);
    outz[0U] = (uint64_t)1U;
    outz[1U] = (uint64_t)0U;
    outz[2U] = (uint64_t)0U;
    outz[3U] = (uint64_t)0U;
    outz[4U] = (uint64_t)0U;
    Hacl_Bignum25519_fmul(outt, x, y);
    res = true;
  }
  bool res0 = res;
  return res0;
}

static bool Hacl_Impl_Ed25519_PointEqual_gte_q(uint64_t *s)
{
  uint64_t s0 = s[0U];
  uint64_t s1 = s[1U];
  uint64_t s2 = s[2U];
  uint64_t s3 = s[3U];
  uint64_t s4 = s[4U];
  if (s4 > (uint64_t)0x00000010000000U)
  {
    return true;
  }
  if (s4 < (uint64_t)0x00000010000000U)
  {
    return false;
  }
  if (s3 > (uint64_t)0x00000000000000U)
  {
    return true;
  }
  if (s2 > (uint64_t)0x000000000014deU)
  {
    return true;
  }
  if (s2 < (uint64_t)0x000000000014deU)
  {
    return false;
  }
  if (s1 > (uint64_t)0xf9dea2f79cd658U)
  {
    return true;
  }
  if (s1 < (uint64_t)0xf9dea2f79cd658U)
  {
    return false;
  }
  if (s0 >= (uint64_t)0x12631a5cf5d3edU)
  {
    return true;
  }
  return false;
}

static bool Hacl_Impl_Ed25519_PointEqual_eq(uint64_t *a, uint64_t *b)
{
  uint64_t a0 = a[0U];
  uint64_t a1 = a[1U];
  uint64_t a2 = a[2U];
  uint64_t a3 = a[3U];
  uint64_t a4 = a[4U];
  uint64_t b0 = b[0U];
  uint64_t b1 = b[1U];
  uint64_t b2 = b[2U];
  uint64_t b3 = b[3U];
  uint64_t b4 = b[4U];
  return a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4;
}

static bool
Hacl_Impl_Ed25519_PointEqual_point_equal_1(uint64_t *p, uint64_t *q1, uint64_t *tmp)
{
  uint64_t *pxqz = tmp;
  uint64_t *qxpz = tmp + (uint32_t)5U;
  Hacl_Bignum25519_fmul(pxqz, p, q1 + (uint32_t)10U);
  Hacl_Bignum25519_reduce(pxqz);
  Hacl_Bignum25519_fmul(qxpz, q1, p + (uint32_t)10U);
  Hacl_Bignum25519_reduce(qxpz);
  return Hacl_Impl_Ed25519_PointEqual_eq(pxqz, qxpz);
}

static bool
Hacl_Impl_Ed25519_PointEqual_point_equal_2(uint64_t *p, uint64_t *q1, uint64_t *tmp)
{
  uint64_t *pyqz = tmp + (uint32_t)10U;
  uint64_t *qypz = tmp + (uint32_t)15U;
  Hacl_Bignum25519_fmul(pyqz, p + (uint32_t)5U, q1 + (uint32_t)10U);
  Hacl_Bignum25519_reduce(pyqz);
  Hacl_Bignum25519_fmul(qypz, q1 + (uint32_t)5U, p + (uint32_t)10U);
  Hacl_Bignum25519_reduce(qypz);
  return Hacl_Impl_Ed25519_PointEqual_eq(pyqz, qypz);
}

static bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q1)
{
  uint64_t tmp[20U] = { 0U };
  bool b = Hacl_Impl_Ed25519_PointEqual_point_equal_1(p, q1, tmp);
  if (b)
  {
    return Hacl_Impl_Ed25519_PointEqual_point_equal_2(p, q1, tmp);
  }
  return false;
}

void Hacl_Ed25519_sign(uint8_t *signature, uint8_t *secret1, uint32_t len, uint8_t *msg)
{
  uint8_t tmp_bytes[352U] = { 0U };
  uint64_t tmp_ints[65U] = { 0U };
  uint8_t *rs_ = tmp_bytes + (uint32_t)160U;
  uint8_t *s_ = tmp_bytes + (uint32_t)192U;
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_1(secret1, tmp_bytes);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_2(len, msg, tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_3(tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_4(len, msg, tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_5(tmp_bytes, tmp_ints);
  memcpy(signature, rs_, (uint32_t)32U * sizeof rs_[0U]);
  memcpy(signature + (uint32_t)32U, s_, (uint32_t)32U * sizeof s_[0U]);
}

bool Hacl_Ed25519_verify(uint8_t *output, uint32_t len, uint8_t *msg, uint8_t *signature)
{
  uint64_t tmp[45U] = { 0U };
  uint8_t tmp_[32U] = { 0U };
  uint64_t *a_ = tmp;
  uint64_t *r_ = tmp + (uint32_t)20U;
  bool b = Hacl_Impl_Ed25519_PointDecompress_point_decompress(a_, output);
  bool res;
  if (b)
  {
    uint8_t *rs = signature;
    bool b_ = Hacl_Impl_Ed25519_PointDecompress_point_decompress(r_, rs);
    if (b_)
    {
      uint8_t *rs1 = signature;
      uint64_t *a_1 = tmp;
      uint64_t *r_1 = tmp + (uint32_t)20U;
      uint64_t *s1 = tmp + (uint32_t)40U;
      Hacl_Impl_Load56_load_32_bytes(s1, signature + (uint32_t)32U);
      bool b__ = Hacl_Impl_Ed25519_PointEqual_gte_q(s1);
      if (b__)
      {
        res = false;
      }
      else
      {
        uint64_t r_2[5U] = { 0U };
        Hacl_Impl_SHA512_ModQ_sha512_modq_pre_pre2(r_2, rs1, output, len, msg);
        Hacl_Impl_Store56_store_56(tmp_, r_2);
        uint8_t *uu____0 = signature + (uint32_t)32U;
        uint64_t tmp1[60U] = { 0U };
        uint64_t *hA = tmp1;
        uint64_t *rhA = tmp1 + (uint32_t)20U;
        uint64_t *sB = tmp1 + (uint32_t)40U;
        Hacl_Impl_Ed25519_Ladder_point_mul_g(sB, uu____0);
        Hacl_Impl_Ed25519_Ladder_point_mul(hA, tmp_, a_1);
        Hacl_Impl_Ed25519_PointAdd_point_add(rhA, r_1, hA);
        bool b1 = Hacl_Impl_Ed25519_PointEqual_point_equal(sB, rhA);
        bool b10 = b1;
        res = b10;
      }
    }
    else
    {
      res = false;
    }
  }
  else
  {
    res = false;
  }
  bool res0 = res;
  return res0;
}

void Hacl_Ed25519_secret_to_public(uint8_t *output, uint8_t *secret1)
{
  Hacl_Impl_Ed25519_SecretToPublic_secret_to_public(output, secret1);
}

void Hacl_Ed25519_expand_keys(uint8_t *ks, uint8_t *secret1)
{
  Hacl_Impl_Ed25519_SecretExpand_secret_expand(ks + (uint32_t)32U, secret1);
  Hacl_Impl_Ed25519_SecretToPublic_secret_to_public(ks, secret1);
}

void Hacl_Ed25519_sign_expanded(uint8_t *signature, uint8_t *ks, uint32_t len, uint8_t *msg)
{
  uint8_t tmp_bytes[352U] = { 0U };
  uint64_t tmp_ints[65U] = { 0U };
  uint8_t *rs_ = tmp_bytes + (uint32_t)160U;
  uint8_t *s_ = tmp_bytes + (uint32_t)192U;
  uint8_t *tmp_public = tmp_bytes + (uint32_t)96U;
  uint8_t *tmp_xsecret = tmp_bytes + (uint32_t)224U;
  memcpy(tmp_public, ks, (uint32_t)32U * sizeof ks[0U]);
  memcpy(tmp_xsecret, ks + (uint32_t)32U, (uint32_t)64U * sizeof (ks + (uint32_t)32U)[0U]);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_2(len, msg, tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_3(tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_4(len, msg, tmp_bytes, tmp_ints);
  Hacl_Impl_Ed25519_Sign_Steps_sign_step_5(tmp_bytes, tmp_ints);
  memcpy(signature, rs_, (uint32_t)32U * sizeof rs_[0U]);
  memcpy(signature + (uint32_t)32U, s_, (uint32_t)32U * sizeof s_[0U]);
}

