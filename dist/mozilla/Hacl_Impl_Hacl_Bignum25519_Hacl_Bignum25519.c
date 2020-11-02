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


#include "Hacl_Impl_Hacl_Bignum25519_Hacl_Bignum25519.h"

static void fsum(uint64_t *a, uint64_t *b)
{
  Hacl_Impl_Curve25519_Field51_fadd(a, a, b);
}

void Hacl_Bignum25519_fdifference(uint64_t *a, uint64_t *b)
{
  Hacl_Impl_Curve25519_Field51_fsub(a, b, a);
}

void Hacl_Bignum25519_reduce_513(uint64_t *a)
{
  Hacl_Impl_Curve25519_Field51_fmul1(a, a, (uint64_t)1U);
}

static void fmul0(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fmul(output, input, input2, tmp);
}

static void times_2(uint64_t *out, uint64_t *a)
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

static void times_d(uint64_t *out, uint64_t *a)
{
  uint64_t d[5U] = { 0U };
  d[0U] = (uint64_t)0x00034dca135978a3U;
  d[1U] = (uint64_t)0x0001a8283b156ebdU;
  d[2U] = (uint64_t)0x0005e7a26001c029U;
  d[3U] = (uint64_t)0x000739c663a03cbbU;
  d[4U] = (uint64_t)0x00052036cee2b6ffU;
  fmul0(out, d, a);
}

static void times_2d(uint64_t *out, uint64_t *a)
{
  uint64_t d2[5U] = { 0U };
  d2[0U] = (uint64_t)0x00069b9426b2f159U;
  d2[1U] = (uint64_t)0x00035050762add7aU;
  d2[2U] = (uint64_t)0x0003cf44c0038052U;
  d2[3U] = (uint64_t)0x0006738cc7407977U;
  d2[4U] = (uint64_t)0x0002406d9dc56dffU;
  fmul0(out, d2, a);
}

static void fsquare(uint64_t *out, uint64_t *a)
{
  FStar_UInt128_uint128 tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp);
}

static void fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  FStar_UInt128_uint128 tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Curve25519_51_fsquare_times(output, input, tmp, count);
}

static void fsquare_times_inplace(uint64_t *output, uint32_t count)
{
  FStar_UInt128_uint128 tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Curve25519_51_fsquare_times(output, output, tmp, count);
}

void Hacl_Bignum25519_inverse(uint64_t *out, uint64_t *a)
{
  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Curve25519_51_finv(out, a, tmp);
}

static void reduce(uint64_t *out)
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

void Hacl_Bignum25519_load_51(uint64_t *output, uint8_t *input)
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

static void store_4(uint8_t *output, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3)
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

void Hacl_Bignum25519_store_51(uint8_t *output, uint64_t *input)
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
  store_4(output, o0, o1, o2, o3);
}

void Hacl_Impl_Ed25519_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q)
{
  uint64_t tmp[30U] = { 0U };
  uint64_t *tmp1 = tmp;
  uint64_t *tmp20 = tmp + (uint32_t)5U;
  uint64_t *tmp30 = tmp + (uint32_t)10U;
  uint64_t *tmp40 = tmp + (uint32_t)15U;
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *x2 = q;
  uint64_t *y2 = q + (uint32_t)5U;
  memcpy(tmp1, x1, (uint32_t)5U * sizeof (uint64_t));
  memcpy(tmp20, x2, (uint32_t)5U * sizeof (uint64_t));
  Hacl_Bignum25519_fdifference(tmp1, y1);
  Hacl_Bignum25519_fdifference(tmp20, y2);
  fmul0(tmp30, tmp1, tmp20);
  memcpy(tmp1, y1, (uint32_t)5U * sizeof (uint64_t));
  memcpy(tmp20, y2, (uint32_t)5U * sizeof (uint64_t));
  fsum(tmp1, x1);
  fsum(tmp20, x2);
  fmul0(tmp40, tmp1, tmp20);
  uint64_t *tmp10 = tmp;
  uint64_t *tmp2 = tmp + (uint32_t)5U;
  uint64_t *tmp3 = tmp + (uint32_t)10U;
  uint64_t *tmp41 = tmp + (uint32_t)15U;
  uint64_t *tmp50 = tmp + (uint32_t)20U;
  uint64_t *tmp60 = tmp + (uint32_t)25U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t *t1 = p + (uint32_t)15U;
  uint64_t *z2 = q + (uint32_t)10U;
  uint64_t *t2 = q + (uint32_t)15U;
  times_2d(tmp10, t1);
  fmul0(tmp2, tmp10, t2);
  times_2(tmp10, z1);
  fmul0(tmp50, tmp10, z2);
  memcpy(tmp10, tmp3, (uint32_t)5U * sizeof (uint64_t));
  memcpy(tmp60, tmp2, (uint32_t)5U * sizeof (uint64_t));
  Hacl_Bignum25519_fdifference(tmp10, tmp41);
  Hacl_Bignum25519_fdifference(tmp60, tmp50);
  fsum(tmp50, tmp2);
  fsum(tmp41, tmp3);
  uint64_t *tmp11 = tmp;
  uint64_t *tmp4 = tmp + (uint32_t)15U;
  uint64_t *tmp5 = tmp + (uint32_t)20U;
  uint64_t *tmp6 = tmp + (uint32_t)25U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *t3 = out + (uint32_t)15U;
  fmul0(x3, tmp11, tmp6);
  fmul0(y3, tmp5, tmp4);
  fmul0(t3, tmp11, tmp4);
  fmul0(z3, tmp6, tmp5);
}

static void point_double(uint64_t *out, uint64_t *p)
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
  fsquare(tmp11, x10);
  fsquare(tmp210, y10);
  fsquare(tmp310, z1);
  times_2(tmp410, tmp310);
  memcpy(tmp310, tmp11, (uint32_t)5U * sizeof (uint64_t));
  fsum(tmp310, tmp210);
  uint64_t *tmp110 = tmp;
  uint64_t *tmp21 = tmp + (uint32_t)5U;
  uint64_t *tmp31 = tmp + (uint32_t)10U;
  uint64_t *tmp41 = tmp + (uint32_t)15U;
  uint64_t *tmp51 = tmp + (uint32_t)20U;
  uint64_t *tmp61 = tmp + (uint32_t)25U;
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  memcpy(tmp51, x1, (uint32_t)5U * sizeof (uint64_t));
  fsum(tmp51, y1);
  fsquare(tmp61, tmp51);
  memcpy(tmp51, tmp31, (uint32_t)5U * sizeof (uint64_t));
  Hacl_Bignum25519_reduce_513(tmp51);
  Hacl_Bignum25519_fdifference(tmp61, tmp51);
  Hacl_Bignum25519_fdifference(tmp21, tmp110);
  Hacl_Bignum25519_reduce_513(tmp21);
  Hacl_Bignum25519_reduce_513(tmp41);
  fsum(tmp41, tmp21);
  fmul0(x3, tmp4, tmp6);
  fmul0(y3, tmp2, tmp3);
  fmul0(t3, tmp6, tmp3);
  fmul0(z3, tmp4, tmp2);
}

static void
swap_conditional_step(uint64_t *a_, uint64_t *b_, uint64_t *a, uint64_t *b, uint64_t swap)
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
  uint64_t x0 = (a0 ^ b0) & swap;
  uint64_t x1 = (a1 ^ b1) & swap;
  uint64_t x2 = (a2 ^ b2) & swap;
  uint64_t x3 = (a3 ^ b3) & swap;
  uint64_t x4 = (a4 ^ b4) & swap;
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
swap_conditional(uint64_t *a_, uint64_t *b_, uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = (uint64_t)0U - iswap;
  swap_conditional_step(a_, b_, a, b, swap);
  swap_conditional_step(a_ + (uint32_t)5U,
    b_ + (uint32_t)5U,
    a + (uint32_t)5U,
    b + (uint32_t)5U,
    swap);
  swap_conditional_step(a_ + (uint32_t)10U,
    b_ + (uint32_t)10U,
    a + (uint32_t)10U,
    b + (uint32_t)10U,
    swap);
  swap_conditional_step(a_ + (uint32_t)15U,
    b_ + (uint32_t)15U,
    a + (uint32_t)15U,
    b + (uint32_t)15U,
    swap);
}

static void swap_conditional_inplace(uint64_t *a, uint64_t *b, uint64_t iswap)
{
  uint64_t swap = (uint64_t)0U - iswap;
  swap_conditional_step(a, b, a, b, swap);
  swap_conditional_step(a + (uint32_t)5U,
    b + (uint32_t)5U,
    a + (uint32_t)5U,
    b + (uint32_t)5U,
    swap);
  swap_conditional_step(a + (uint32_t)10U,
    b + (uint32_t)10U,
    a + (uint32_t)10U,
    b + (uint32_t)10U,
    swap);
  swap_conditional_step(a + (uint32_t)15U,
    b + (uint32_t)15U,
    a + (uint32_t)15U,
    b + (uint32_t)15U,
    swap);
}

void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *result, uint8_t *scalar, uint64_t *q)
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
  memcpy(nqpq, q, (uint32_t)20U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)256U; i++)
  {
    uint64_t *nq1 = b;
    uint64_t *nqpq1 = b + (uint32_t)20U;
    uint64_t *nq2 = b + (uint32_t)40U;
    uint64_t *nqpq2 = b + (uint32_t)60U;
    uint32_t q1 = ((uint32_t)255U - i) >> (uint32_t)3U;
    uint32_t r = ((uint32_t)255U - i) & (uint32_t)7U;
    uint8_t kq = scalar[q1];
    uint8_t i1 = kq >> r & (uint8_t)1U;
    swap_conditional_inplace(nq1, nqpq1, (uint64_t)i1);
    point_double(nq2, nq1);
    Hacl_Impl_Ed25519_PointAdd_point_add(nqpq2, nq1, nqpq1);
    swap_conditional(nq1, nqpq1, nq2, nqpq2, (uint64_t)i1);
  }
  memcpy(result, nq, (uint32_t)20U * sizeof (uint64_t));
}

void Hacl_Impl_Ed25519_PointCompress_point_compress(uint8_t *z, uint64_t *p)
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
  fmul0(x1, px, zinv1);
  reduce(x1);
  fmul0(out1, py, zinv1);
  Hacl_Bignum25519_reduce_513(out1);
  uint64_t x0 = x[0U];
  uint64_t b = x0 & (uint64_t)1U;
  Hacl_Bignum25519_store_51(z, out);
  uint8_t xbyte = (uint8_t)b;
  uint8_t o31 = z[31U];
  z[31U] = o31 + (xbyte << (uint32_t)7U);
}

static void pow2_252m2(uint64_t *out, uint64_t *z)
{
  uint64_t buf[20U] = { 0U };
  uint64_t *a = buf;
  uint64_t *t00 = buf + (uint32_t)5U;
  uint64_t *b0 = buf + (uint32_t)10U;
  uint64_t *c0 = buf + (uint32_t)15U;
  fsquare_times(a, z, (uint32_t)1U);
  fsquare_times(t00, a, (uint32_t)2U);
  fmul0(b0, t00, z);
  fmul0(a, b0, a);
  fsquare_times(t00, a, (uint32_t)1U);
  fmul0(b0, t00, b0);
  fsquare_times(t00, b0, (uint32_t)5U);
  fmul0(b0, t00, b0);
  fsquare_times(t00, b0, (uint32_t)10U);
  fmul0(c0, t00, b0);
  fsquare_times(t00, c0, (uint32_t)20U);
  fmul0(t00, t00, c0);
  fsquare_times_inplace(t00, (uint32_t)10U);
  fmul0(b0, t00, b0);
  fsquare_times(t00, b0, (uint32_t)50U);
  uint64_t *a0 = buf;
  uint64_t *t0 = buf + (uint32_t)5U;
  uint64_t *b = buf + (uint32_t)10U;
  uint64_t *c = buf + (uint32_t)15U;
  fsquare_times(a0, z, (uint32_t)1U);
  fmul0(c, t0, b);
  fsquare_times(t0, c, (uint32_t)100U);
  fmul0(t0, t0, c);
  fsquare_times_inplace(t0, (uint32_t)50U);
  fmul0(t0, t0, b);
  fsquare_times_inplace(t0, (uint32_t)2U);
  fmul0(out, t0, a0);
}

static bool is_0(uint64_t *x)
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

static void mul_modp_sqrt_m1(uint64_t *x)
{
  uint64_t sqrt_m1[5U] = { 0U };
  sqrt_m1[0U] = (uint64_t)0x00061b274a0ea0b0U;
  sqrt_m1[1U] = (uint64_t)0x0000d5a5fc8f189dU;
  sqrt_m1[2U] = (uint64_t)0x0007ef5e9cbd0c60U;
  sqrt_m1[3U] = (uint64_t)0x00078595a6804c9eU;
  sqrt_m1[4U] = (uint64_t)0x0002b8324804fc1dU;
  fmul0(x, x, sqrt_m1);
}

static bool recover_x(uint64_t *x, uint64_t *y, uint64_t sign)
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
    uint64_t *one = tmp1;
    uint64_t *y2 = tmp1 + (uint32_t)5U;
    uint64_t *dyyi = tmp1 + (uint32_t)10U;
    uint64_t *dyy = tmp1 + (uint32_t)15U;
    one[0U] = (uint64_t)1U;
    one[1U] = (uint64_t)0U;
    one[2U] = (uint64_t)0U;
    one[3U] = (uint64_t)0U;
    one[4U] = (uint64_t)0U;
    fsquare(y2, y);
    times_d(dyy, y2);
    fsum(dyy, one);
    Hacl_Bignum25519_reduce_513(dyy);
    Hacl_Bignum25519_inverse(dyyi, dyy);
    Hacl_Bignum25519_fdifference(one, y2);
    fmul0(x2, one, dyyi);
    reduce(x2);
    bool x2_is_0 = is_0(x2);
    uint8_t z;
    if (x2_is_0)
    {
      if (sign == (uint64_t)0U)
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
      pow2_252m2(x31, x210);
      fsquare(t00, x31);
      memcpy(t10, x210, (uint32_t)5U * sizeof (uint64_t));
      Hacl_Bignum25519_fdifference(t10, t00);
      Hacl_Bignum25519_reduce_513(t10);
      reduce(t10);
      bool t1_is_0 = is_0(t10);
      if (!t1_is_0)
      {
        mul_modp_sqrt_m1(x31);
      }
      uint64_t *x211 = tmp;
      uint64_t *x3 = tmp + (uint32_t)5U;
      uint64_t *t01 = tmp + (uint32_t)10U;
      uint64_t *t1 = tmp + (uint32_t)15U;
      fsquare(t01, x3);
      memcpy(t1, x211, (uint32_t)5U * sizeof (uint64_t));
      Hacl_Bignum25519_fdifference(t1, t01);
      Hacl_Bignum25519_reduce_513(t1);
      reduce(t1);
      bool z1 = is_0(t1);
      if (z1 == false)
      {
        res = false;
      }
      else
      {
        uint64_t *x32 = tmp + (uint32_t)5U;
        uint64_t *t0 = tmp + (uint32_t)10U;
        reduce(x32);
        uint64_t x0 = x32[0U];
        uint64_t x01 = x0 & (uint64_t)1U;
        if (!(x01 == sign))
        {
          t0[0U] = (uint64_t)0U;
          t0[1U] = (uint64_t)0U;
          t0[2U] = (uint64_t)0U;
          t0[3U] = (uint64_t)0U;
          t0[4U] = (uint64_t)0U;
          Hacl_Bignum25519_fdifference(x32, t0);
          Hacl_Bignum25519_reduce_513(x32);
          reduce(x32);
        }
        memcpy(x, x32, (uint32_t)5U * sizeof (uint64_t));
        res = true;
      }
    }
  }
  bool res0 = res;
  return res0;
}

bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(uint64_t *out, uint8_t *s)
{
  uint64_t tmp[10U] = { 0U };
  uint64_t *y = tmp;
  uint64_t *x = tmp + (uint32_t)5U;
  uint8_t s31 = s[31U];
  uint8_t z = s31 >> (uint32_t)7U;
  uint64_t sign = (uint64_t)z;
  Hacl_Bignum25519_load_51(y, s);
  bool z0 = recover_x(x, y, sign);
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
    memcpy(outx, x, (uint32_t)5U * sizeof (uint64_t));
    memcpy(outy, y, (uint32_t)5U * sizeof (uint64_t));
    outz[0U] = (uint64_t)1U;
    outz[1U] = (uint64_t)0U;
    outz[2U] = (uint64_t)0U;
    outz[3U] = (uint64_t)0U;
    outz[4U] = (uint64_t)0U;
    fmul0(outt, x, y);
    res = true;
  }
  bool res0 = res;
  return res0;
}

static bool eq(uint64_t *a, uint64_t *b)
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

static bool point_equal_1(uint64_t *p, uint64_t *q, uint64_t *tmp)
{
  uint64_t *pxqz = tmp;
  uint64_t *qxpz = tmp + (uint32_t)5U;
  fmul0(pxqz, p, q + (uint32_t)10U);
  reduce(pxqz);
  fmul0(qxpz, q, p + (uint32_t)10U);
  reduce(qxpz);
  return eq(pxqz, qxpz);
}

static bool point_equal_2(uint64_t *p, uint64_t *q, uint64_t *tmp)
{
  uint64_t *pyqz = tmp + (uint32_t)10U;
  uint64_t *qypz = tmp + (uint32_t)15U;
  fmul0(pyqz, p + (uint32_t)5U, q + (uint32_t)10U);
  reduce(pyqz);
  fmul0(qypz, q + (uint32_t)5U, p + (uint32_t)10U);
  reduce(qypz);
  return eq(pyqz, qypz);
}

bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q)
{
  uint64_t tmp[20U] = { 0U };
  bool b = point_equal_1(p, q, tmp);
  if (b)
  {
    return point_equal_2(p, q, tmp);
  }
  return false;
}

