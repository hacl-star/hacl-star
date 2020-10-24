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

static void fsum(u64 *a, u64 *b)
{
  Hacl_Impl_Curve25519_Field51_fadd(a, a, b);
}

void Hacl_Bignum25519_fdifference(u64 *a, u64 *b)
{
  Hacl_Impl_Curve25519_Field51_fsub(a, b, a);
}

void Hacl_Bignum25519_reduce_513(u64 *a)
{
  Hacl_Impl_Curve25519_Field51_fmul1(a, a, (u64)1U);
}

static void fmul(u64 *output, u64 *input, u64 *input2)
{
  uint128_t tmp[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Impl_Curve25519_Field51_fmul(output, input, input2, tmp);
}

static void times_2(u64 *out, u64 *a)
{
  u64 a0 = a[0U];
  u64 a1 = a[1U];
  u64 a2 = a[2U];
  u64 a3 = a[3U];
  u64 a4 = a[4U];
  u64 o0 = (u64)2U * a0;
  u64 o1 = (u64)2U * a1;
  u64 o2 = (u64)2U * a2;
  u64 o3 = (u64)2U * a3;
  u64 o4 = (u64)2U * a4;
  out[0U] = o0;
  out[1U] = o1;
  out[2U] = o2;
  out[3U] = o3;
  out[4U] = o4;
}

static void times_d(u64 *out, u64 *a)
{
  u64 d[5U] = { 0U };
  d[0U] = (u64)0x00034dca135978a3U;
  d[1U] = (u64)0x0001a8283b156ebdU;
  d[2U] = (u64)0x0005e7a26001c029U;
  d[3U] = (u64)0x000739c663a03cbbU;
  d[4U] = (u64)0x00052036cee2b6ffU;
  fmul(out, d, a);
}

static void times_2d(u64 *out, u64 *a)
{
  u64 d2[5U] = { 0U };
  d2[0U] = (u64)0x00069b9426b2f159U;
  d2[1U] = (u64)0x00035050762add7aU;
  d2[2U] = (u64)0x0003cf44c0038052U;
  d2[3U] = (u64)0x0006738cc7407977U;
  d2[4U] = (u64)0x0002406d9dc56dffU;
  fmul(out, d2, a);
}

static void fsquare(u64 *out, u64 *a)
{
  uint128_t tmp[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp);
}

static void fsquare_times(u64 *output, u64 *input, u32 count)
{
  uint128_t tmp[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Curve25519_51_fsquare_times(output, input, tmp, count);
}

static void fsquare_times_inplace(u64 *output, u32 count)
{
  uint128_t tmp[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Curve25519_51_fsquare_times(output, output, tmp, count);
}

void Hacl_Bignum25519_inverse(u64 *out, u64 *a)
{
  uint128_t tmp[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Curve25519_51_finv(out, a, tmp);
}

static void reduce(u64 *out)
{
  u64 t00 = out[0U];
  u64 t10 = out[1U];
  u64 t20 = out[2U];
  u64 t30 = out[3U];
  u64 t40 = out[4U];
  u64 t2_ = t20 + (t10 >> (u32)51U);
  u64 t1__ = t10 & (u64)0x7ffffffffffffU;
  u64 t3_ = t30 + (t2_ >> (u32)51U);
  u64 t2__ = t2_ & (u64)0x7ffffffffffffU;
  u64 t4_ = t40 + (t3_ >> (u32)51U);
  u64 t3__ = t3_ & (u64)0x7ffffffffffffU;
  u64 b40;
  u64 b00;
  u64 b4_;
  u64 b0_;
  u64 t0;
  u64 t1;
  u64 t2;
  u64 t3;
  u64 t4;
  u64 t1_;
  u64 t0_;
  u64 t2_0;
  u64 t1__0;
  u64 t3_0;
  u64 t2__0;
  u64 t4_0;
  u64 t3__0;
  u64 b4;
  u64 b0;
  u64 b4_0;
  u64 b0_0;
  u64 i0;
  u64 i1;
  u64 i0_;
  u64 i1_;
  u64 a0;
  u64 a1;
  u64 a2;
  u64 a3;
  u64 a4;
  u64 m0;
  u64 m1;
  u64 m2;
  u64 m3;
  u64 m4;
  u64 mask;
  u64 a0_;
  u64 a1_;
  u64 a2_;
  u64 a3_;
  u64 a4_;
  out[0U] = t00;
  out[1U] = t1__;
  out[2U] = t2__;
  out[3U] = t3__;
  out[4U] = t4_;
  b40 = out[4U];
  b00 = out[0U];
  b4_ = b40 & (u64)0x7ffffffffffffU;
  b0_ = b00 + (u64)19U * (b40 >> (u32)51U);
  out[4U] = b4_;
  out[0U] = b0_;
  t0 = out[0U];
  t1 = out[1U];
  t2 = out[2U];
  t3 = out[3U];
  t4 = out[4U];
  t1_ = t1 + (t0 >> (u32)51U);
  t0_ = t0 & (u64)0x7ffffffffffffU;
  t2_0 = t2 + (t1_ >> (u32)51U);
  t1__0 = t1_ & (u64)0x7ffffffffffffU;
  t3_0 = t3 + (t2_0 >> (u32)51U);
  t2__0 = t2_0 & (u64)0x7ffffffffffffU;
  t4_0 = t4 + (t3_0 >> (u32)51U);
  t3__0 = t3_0 & (u64)0x7ffffffffffffU;
  out[0U] = t0_;
  out[1U] = t1__0;
  out[2U] = t2__0;
  out[3U] = t3__0;
  out[4U] = t4_0;
  b4 = out[4U];
  b0 = out[0U];
  b4_0 = b4 & (u64)0x7ffffffffffffU;
  b0_0 = b0 + (u64)19U * (b4 >> (u32)51U);
  out[4U] = b4_0;
  out[0U] = b0_0;
  i0 = out[0U];
  i1 = out[1U];
  i0_ = i0 & (u64)0x7ffffffffffffU;
  i1_ = i1 + (i0 >> (u32)51U);
  out[0U] = i0_;
  out[1U] = i1_;
  a0 = out[0U];
  a1 = out[1U];
  a2 = out[2U];
  a3 = out[3U];
  a4 = out[4U];
  m0 = FStar_UInt64_gte_mask(a0, (u64)0x7ffffffffffedU);
  m1 = FStar_UInt64_eq_mask(a1, (u64)0x7ffffffffffffU);
  m2 = FStar_UInt64_eq_mask(a2, (u64)0x7ffffffffffffU);
  m3 = FStar_UInt64_eq_mask(a3, (u64)0x7ffffffffffffU);
  m4 = FStar_UInt64_eq_mask(a4, (u64)0x7ffffffffffffU);
  mask = (((m0 & m1) & m2) & m3) & m4;
  a0_ = a0 - ((u64)0x7ffffffffffedU & mask);
  a1_ = a1 - ((u64)0x7ffffffffffffU & mask);
  a2_ = a2 - ((u64)0x7ffffffffffffU & mask);
  a3_ = a3 - ((u64)0x7ffffffffffffU & mask);
  a4_ = a4 - ((u64)0x7ffffffffffffU & mask);
  out[0U] = a0_;
  out[1U] = a1_;
  out[2U] = a2_;
  out[3U] = a3_;
  out[4U] = a4_;
}

void Hacl_Bignum25519_load_51(u64 *output, u8 *input)
{
  u64 u0 = load64_le(input);
  u64 i0 = u0;
  u64 u1 = load64_le(input + (u32)6U);
  u64 i1 = u1;
  u64 u2 = load64_le(input + (u32)12U);
  u64 i2 = u2;
  u64 u3 = load64_le(input + (u32)19U);
  u64 i3 = u3;
  u64 u = load64_le(input + (u32)24U);
  u64 i4 = u;
  u64 output0 = i0 & (u64)0x7ffffffffffffU;
  u64 output1 = i1 >> (u32)3U & (u64)0x7ffffffffffffU;
  u64 output2 = i2 >> (u32)6U & (u64)0x7ffffffffffffU;
  u64 output3 = i3 >> (u32)1U & (u64)0x7ffffffffffffU;
  u64 output4 = i4 >> (u32)12U & (u64)0x7ffffffffffffU;
  output[0U] = output0;
  output[1U] = output1;
  output[2U] = output2;
  output[3U] = output3;
  output[4U] = output4;
}

static void store_4(u8 *output, u64 v0, u64 v1, u64 v2, u64 v3)
{
  u8 *b0 = output;
  u8 *b1 = output + (u32)8U;
  u8 *b2 = output + (u32)16U;
  u8 *b3 = output + (u32)24U;
  store64_le(b0, v0);
  store64_le(b1, v1);
  store64_le(b2, v2);
  store64_le(b3, v3);
}

void Hacl_Bignum25519_store_51(u8 *output, u64 *input)
{
  u64 t0 = input[0U];
  u64 t1 = input[1U];
  u64 t2 = input[2U];
  u64 t3 = input[3U];
  u64 t4 = input[4U];
  u64 l_ = t0 + (u64)0U;
  u64 tmp0 = l_ & (u64)0x7ffffffffffffU;
  u64 c0 = l_ >> (u32)51U;
  u64 l_0 = t1 + c0;
  u64 tmp1 = l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = l_0 >> (u32)51U;
  u64 l_1 = t2 + c1;
  u64 tmp2 = l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = l_1 >> (u32)51U;
  u64 l_2 = t3 + c2;
  u64 tmp3 = l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = l_2 >> (u32)51U;
  u64 l_3 = t4 + c3;
  u64 tmp4 = l_3 & (u64)0x7ffffffffffffU;
  u64 c4 = l_3 >> (u32)51U;
  u64 l_4 = tmp0 + c4 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c5 = l_4 >> (u32)51U;
  u64 f0 = tmp0_;
  u64 f1 = tmp1 + c5;
  u64 f2 = tmp2;
  u64 f3 = tmp3;
  u64 f4 = tmp4;
  u64 m0 = FStar_UInt64_gte_mask(f0, (u64)0x7ffffffffffedU);
  u64 m1 = FStar_UInt64_eq_mask(f1, (u64)0x7ffffffffffffU);
  u64 m2 = FStar_UInt64_eq_mask(f2, (u64)0x7ffffffffffffU);
  u64 m3 = FStar_UInt64_eq_mask(f3, (u64)0x7ffffffffffffU);
  u64 m4 = FStar_UInt64_eq_mask(f4, (u64)0x7ffffffffffffU);
  u64 mask = (((m0 & m1) & m2) & m3) & m4;
  u64 f0_ = f0 - (mask & (u64)0x7ffffffffffedU);
  u64 f1_ = f1 - (mask & (u64)0x7ffffffffffffU);
  u64 f2_ = f2 - (mask & (u64)0x7ffffffffffffU);
  u64 f3_ = f3 - (mask & (u64)0x7ffffffffffffU);
  u64 f4_ = f4 - (mask & (u64)0x7ffffffffffffU);
  u64 f01 = f0_;
  u64 f11 = f1_;
  u64 f21 = f2_;
  u64 f31 = f3_;
  u64 f41 = f4_;
  u64 o00 = f01 | f11 << (u32)51U;
  u64 o10 = f11 >> (u32)13U | f21 << (u32)38U;
  u64 o20 = f21 >> (u32)26U | f31 << (u32)25U;
  u64 o30 = f31 >> (u32)39U | f41 << (u32)12U;
  u64 o0 = o00;
  u64 o1 = o10;
  u64 o2 = o20;
  u64 o3 = o30;
  store_4(output, o0, o1, o2, o3);
}

void Hacl_Impl_Ed25519_PointAdd_point_add(u64 *out, u64 *p, u64 *q)
{
  u64 tmp[30U] = { 0U };
  u64 *tmp10 = tmp;
  u64 *tmp20 = tmp + (u32)5U;
  u64 *tmp30 = tmp + (u32)10U;
  u64 *tmp40 = tmp + (u32)15U;
  u64 *x1 = p;
  u64 *y1 = p + (u32)5U;
  u64 *x2 = q;
  u64 *y2 = q + (u32)5U;
  u64 *tmp11;
  u64 *tmp2;
  u64 *tmp3;
  u64 *tmp41;
  u64 *tmp50;
  u64 *tmp60;
  u64 *z1;
  u64 *t1;
  u64 *z2;
  u64 *t2;
  u64 *tmp1;
  u64 *tmp4;
  u64 *tmp5;
  u64 *tmp6;
  u64 *x3;
  u64 *y3;
  u64 *z3;
  u64 *t3;
  memcpy(tmp10, x1, (u32)5U * sizeof (u64));
  memcpy(tmp20, x2, (u32)5U * sizeof (u64));
  Hacl_Bignum25519_fdifference(tmp10, y1);
  Hacl_Bignum25519_fdifference(tmp20, y2);
  fmul(tmp30, tmp10, tmp20);
  memcpy(tmp10, y1, (u32)5U * sizeof (u64));
  memcpy(tmp20, y2, (u32)5U * sizeof (u64));
  fsum(tmp10, x1);
  fsum(tmp20, x2);
  fmul(tmp40, tmp10, tmp20);
  tmp11 = tmp;
  tmp2 = tmp + (u32)5U;
  tmp3 = tmp + (u32)10U;
  tmp41 = tmp + (u32)15U;
  tmp50 = tmp + (u32)20U;
  tmp60 = tmp + (u32)25U;
  z1 = p + (u32)10U;
  t1 = p + (u32)15U;
  z2 = q + (u32)10U;
  t2 = q + (u32)15U;
  times_2d(tmp11, t1);
  fmul(tmp2, tmp11, t2);
  times_2(tmp11, z1);
  fmul(tmp50, tmp11, z2);
  memcpy(tmp11, tmp3, (u32)5U * sizeof (u64));
  memcpy(tmp60, tmp2, (u32)5U * sizeof (u64));
  Hacl_Bignum25519_fdifference(tmp11, tmp41);
  Hacl_Bignum25519_fdifference(tmp60, tmp50);
  fsum(tmp50, tmp2);
  fsum(tmp41, tmp3);
  tmp1 = tmp;
  tmp4 = tmp + (u32)15U;
  tmp5 = tmp + (u32)20U;
  tmp6 = tmp + (u32)25U;
  x3 = out;
  y3 = out + (u32)5U;
  z3 = out + (u32)10U;
  t3 = out + (u32)15U;
  fmul(x3, tmp1, tmp6);
  fmul(y3, tmp5, tmp4);
  fmul(t3, tmp1, tmp4);
  fmul(z3, tmp6, tmp5);
}

static void point_double(u64 *out, u64 *p)
{
  u64 tmp[30U] = { 0U };
  u64 *tmp2 = tmp + (u32)5U;
  u64 *tmp3 = tmp + (u32)10U;
  u64 *tmp4 = tmp + (u32)15U;
  u64 *tmp6 = tmp + (u32)25U;
  u64 *x3 = out;
  u64 *y3 = out + (u32)5U;
  u64 *z3 = out + (u32)10U;
  u64 *t3 = out + (u32)15U;
  u64 *tmp110 = tmp;
  u64 *tmp210 = tmp + (u32)5U;
  u64 *tmp310 = tmp + (u32)10U;
  u64 *tmp410 = tmp + (u32)15U;
  u64 *x10 = p;
  u64 *y10 = p + (u32)5U;
  u64 *z1 = p + (u32)10U;
  u64 *tmp11;
  u64 *tmp21;
  u64 *tmp31;
  u64 *tmp41;
  u64 *tmp51;
  u64 *tmp61;
  u64 *x1;
  u64 *y1;
  fsquare(tmp110, x10);
  fsquare(tmp210, y10);
  fsquare(tmp310, z1);
  times_2(tmp410, tmp310);
  memcpy(tmp310, tmp110, (u32)5U * sizeof (u64));
  fsum(tmp310, tmp210);
  tmp11 = tmp;
  tmp21 = tmp + (u32)5U;
  tmp31 = tmp + (u32)10U;
  tmp41 = tmp + (u32)15U;
  tmp51 = tmp + (u32)20U;
  tmp61 = tmp + (u32)25U;
  x1 = p;
  y1 = p + (u32)5U;
  memcpy(tmp51, x1, (u32)5U * sizeof (u64));
  fsum(tmp51, y1);
  fsquare(tmp61, tmp51);
  memcpy(tmp51, tmp31, (u32)5U * sizeof (u64));
  Hacl_Bignum25519_reduce_513(tmp51);
  Hacl_Bignum25519_fdifference(tmp61, tmp51);
  Hacl_Bignum25519_fdifference(tmp21, tmp11);
  Hacl_Bignum25519_reduce_513(tmp21);
  Hacl_Bignum25519_reduce_513(tmp41);
  fsum(tmp41, tmp21);
  fmul(x3, tmp4, tmp6);
  fmul(y3, tmp2, tmp3);
  fmul(t3, tmp6, tmp3);
  fmul(z3, tmp4, tmp2);
}

static void swap_conditional_step(u64 *a_, u64 *b_, u64 *a, u64 *b, u64 swap)
{
  u64 a0 = a[0U];
  u64 a1 = a[1U];
  u64 a2 = a[2U];
  u64 a3 = a[3U];
  u64 a4 = a[4U];
  u64 b0 = b[0U];
  u64 b1 = b[1U];
  u64 b2 = b[2U];
  u64 b3 = b[3U];
  u64 b4 = b[4U];
  u64 x0 = (a0 ^ b0) & swap;
  u64 x1 = (a1 ^ b1) & swap;
  u64 x2 = (a2 ^ b2) & swap;
  u64 x3 = (a3 ^ b3) & swap;
  u64 x4 = (a4 ^ b4) & swap;
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

static void swap_conditional(u64 *a_, u64 *b_, u64 *a, u64 *b, u64 iswap)
{
  u64 swap = (u64)0U - iswap;
  swap_conditional_step(a_, b_, a, b, swap);
  swap_conditional_step(a_ + (u32)5U, b_ + (u32)5U, a + (u32)5U, b + (u32)5U, swap);
  swap_conditional_step(a_ + (u32)10U, b_ + (u32)10U, a + (u32)10U, b + (u32)10U, swap);
  swap_conditional_step(a_ + (u32)15U, b_ + (u32)15U, a + (u32)15U, b + (u32)15U, swap);
}

static void swap_conditional_inplace(u64 *a, u64 *b, u64 iswap)
{
  u64 swap = (u64)0U - iswap;
  swap_conditional_step(a, b, a, b, swap);
  swap_conditional_step(a + (u32)5U, b + (u32)5U, a + (u32)5U, b + (u32)5U, swap);
  swap_conditional_step(a + (u32)10U, b + (u32)10U, a + (u32)10U, b + (u32)10U, swap);
  swap_conditional_step(a + (u32)15U, b + (u32)15U, a + (u32)15U, b + (u32)15U, swap);
}

void Hacl_Impl_Ed25519_Ladder_point_mul(u64 *result, u8 *scalar, u64 *q)
{
  u64 b[80U] = { 0U };
  u64 *nq = b;
  u64 *nqpq = b + (u32)20U;
  u64 *x = nq;
  u64 *y = nq + (u32)5U;
  u64 *z = nq + (u32)10U;
  u64 *t = nq + (u32)15U;
  x[0U] = (u64)0U;
  x[1U] = (u64)0U;
  x[2U] = (u64)0U;
  x[3U] = (u64)0U;
  x[4U] = (u64)0U;
  y[0U] = (u64)1U;
  y[1U] = (u64)0U;
  y[2U] = (u64)0U;
  y[3U] = (u64)0U;
  y[4U] = (u64)0U;
  z[0U] = (u64)1U;
  z[1U] = (u64)0U;
  z[2U] = (u64)0U;
  z[3U] = (u64)0U;
  z[4U] = (u64)0U;
  t[0U] = (u64)0U;
  t[1U] = (u64)0U;
  t[2U] = (u64)0U;
  t[3U] = (u64)0U;
  t[4U] = (u64)0U;
  memcpy(nqpq, q, (u32)20U * sizeof (u64));
  {
    u32 i;
    for (i = (u32)0U; i < (u32)256U; i++)
    {
      u64 *nq1 = b;
      u64 *nqpq1 = b + (u32)20U;
      u64 *nq2 = b + (u32)40U;
      u64 *nqpq2 = b + (u32)60U;
      u32 q1 = ((u32)255U - i) >> (u32)3U;
      u32 r = ((u32)255U - i) & (u32)7U;
      u8 kq = scalar[q1];
      u8 i1 = kq >> r & (u8)1U;
      swap_conditional_inplace(nq1, nqpq1, (u64)i1);
      point_double(nq2, nq1);
      Hacl_Impl_Ed25519_PointAdd_point_add(nqpq2, nq1, nqpq1);
      swap_conditional(nq1, nqpq1, nq2, nqpq2, (u64)i1);
    }
  }
  memcpy(result, nq, (u32)20U * sizeof (u64));
}

static void point_mul_g(u64 *result, u8 *scalar)
{
  u64 g[20U] = { 0U };
  u64 *gx = g;
  u64 *gy = g + (u32)5U;
  u64 *gz = g + (u32)10U;
  u64 *gt = g + (u32)15U;
  gx[0U] = (u64)0x00062d608f25d51aU;
  gx[1U] = (u64)0x000412a4b4f6592aU;
  gx[2U] = (u64)0x00075b7171a4b31dU;
  gx[3U] = (u64)0x0001ff60527118feU;
  gx[4U] = (u64)0x000216936d3cd6e5U;
  gy[0U] = (u64)0x0006666666666658U;
  gy[1U] = (u64)0x0004ccccccccccccU;
  gy[2U] = (u64)0x0001999999999999U;
  gy[3U] = (u64)0x0003333333333333U;
  gy[4U] = (u64)0x0006666666666666U;
  gz[0U] = (u64)1U;
  gz[1U] = (u64)0U;
  gz[2U] = (u64)0U;
  gz[3U] = (u64)0U;
  gz[4U] = (u64)0U;
  gt[0U] = (u64)0x00068ab3a5b7dda3U;
  gt[1U] = (u64)0x00000eea2a5eadbbU;
  gt[2U] = (u64)0x0002af8df483c27eU;
  gt[3U] = (u64)0x000332b375274732U;
  gt[4U] = (u64)0x00067875f0fd78b7U;
  Hacl_Impl_Ed25519_Ladder_point_mul(result, scalar, g);
}

void Hacl_Impl_Ed25519_PointCompress_point_compress(u8 *z, u64 *p)
{
  u64 tmp[15U] = { 0U };
  u64 *x = tmp + (u32)5U;
  u64 *out = tmp + (u32)10U;
  u64 *zinv1 = tmp;
  u64 *x1 = tmp + (u32)5U;
  u64 *out1 = tmp + (u32)10U;
  u64 *px = p;
  u64 *py = p + (u32)5U;
  u64 *pz = p + (u32)10U;
  u64 x0;
  u64 b;
  u8 xbyte;
  u8 o31;
  Hacl_Bignum25519_inverse(zinv1, pz);
  fmul(x1, px, zinv1);
  reduce(x1);
  fmul(out1, py, zinv1);
  Hacl_Bignum25519_reduce_513(out1);
  x0 = x[0U];
  b = x0 & (u64)1U;
  Hacl_Bignum25519_store_51(z, out);
  xbyte = (u8)b;
  o31 = z[31U];
  z[31U] = o31 + (xbyte << (u32)7U);
}

static void secret_expand(u8 *expanded, u8 *secret)
{
  u8 *h_low;
  u8 h_low0;
  u8 h_low31;
  Hacl_Hash_SHA2_hash_512(secret, (u32)32U, expanded);
  h_low = expanded;
  h_low0 = h_low[0U];
  h_low31 = h_low[31U];
  h_low[0U] = h_low0 & (u8)0xf8U;
  h_low[31U] = (h_low31 & (u8)127U) | (u8)64U;
}

static void secret_to_public(u8 *out, u8 *secret)
{
  u8 expanded_secret[64U] = { 0U };
  u64 res[20U] = { 0U };
  u8 *a;
  secret_expand(expanded_secret, secret);
  a = expanded_secret;
  point_mul_g(res, a);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, res);
}

static void barrett_reduction(u64 *z, u64 *t)
{
  u64 t0 = t[0U];
  u64 t1 = t[1U];
  u64 t2 = t[2U];
  u64 t3 = t[3U];
  u64 t4 = t[4U];
  u64 t5 = t[5U];
  u64 t6 = t[6U];
  u64 t7 = t[7U];
  u64 t8 = t[8U];
  u64 t9 = t[9U];
  u64 m00 = (u64)0x12631a5cf5d3edU;
  u64 m10 = (u64)0xf9dea2f79cd658U;
  u64 m20 = (u64)0x000000000014deU;
  u64 m30 = (u64)0x00000000000000U;
  u64 m40 = (u64)0x00000010000000U;
  u64 m0 = m00;
  u64 m1 = m10;
  u64 m2 = m20;
  u64 m3 = m30;
  u64 m4 = m40;
  u64 m010 = (u64)0x9ce5a30a2c131bU;
  u64 m110 = (u64)0x215d086329a7edU;
  u64 m210 = (u64)0xffffffffeb2106U;
  u64 m310 = (u64)0xffffffffffffffU;
  u64 m410 = (u64)0x00000fffffffffU;
  u64 mu0 = m010;
  u64 mu1 = m110;
  u64 mu2 = m210;
  u64 mu3 = m310;
  u64 mu4 = m410;
  u64 y_ = (t5 & (u64)0xffffffU) << (u32)32U;
  u64 x_ = t4 >> (u32)24U;
  u64 z00 = x_ | y_;
  u64 y_0 = (t6 & (u64)0xffffffU) << (u32)32U;
  u64 x_0 = t5 >> (u32)24U;
  u64 z10 = x_0 | y_0;
  u64 y_1 = (t7 & (u64)0xffffffU) << (u32)32U;
  u64 x_1 = t6 >> (u32)24U;
  u64 z20 = x_1 | y_1;
  u64 y_2 = (t8 & (u64)0xffffffU) << (u32)32U;
  u64 x_2 = t7 >> (u32)24U;
  u64 z30 = x_2 | y_2;
  u64 y_3 = (t9 & (u64)0xffffffU) << (u32)32U;
  u64 x_3 = t8 >> (u32)24U;
  u64 z40 = x_3 | y_3;
  u64 q0 = z00;
  u64 q1 = z10;
  u64 q2 = z20;
  u64 q3 = z30;
  u64 q4 = z40;
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
  uint128_t carry0 = z01 >> (u32)56U;
  uint128_t c00 = carry0;
  uint128_t carry1 = (z11 + c00) >> (u32)56U;
  u64 t100 = (uint64_t)(z11 + c00) & (u64)0xffffffffffffffU;
  uint128_t c10 = carry1;
  uint128_t carry2 = (z21 + c10) >> (u32)56U;
  u64 t101 = (uint64_t)(z21 + c10) & (u64)0xffffffffffffffU;
  uint128_t c20 = carry2;
  uint128_t carry3 = (z31 + c20) >> (u32)56U;
  u64 t102 = (uint64_t)(z31 + c20) & (u64)0xffffffffffffffU;
  uint128_t c30 = carry3;
  uint128_t carry4 = (z41 + c30) >> (u32)56U;
  u64 t103 = (uint64_t)(z41 + c30) & (u64)0xffffffffffffffU;
  uint128_t c40 = carry4;
  u64 t410 = t103;
  uint128_t carry5 = (z5 + c40) >> (u32)56U;
  u64 t104 = (uint64_t)(z5 + c40) & (u64)0xffffffffffffffU;
  uint128_t c5 = carry5;
  u64 t51 = t104;
  uint128_t carry6 = (z6 + c5) >> (u32)56U;
  u64 t105 = (uint64_t)(z6 + c5) & (u64)0xffffffffffffffU;
  uint128_t c6 = carry6;
  u64 t61 = t105;
  uint128_t carry7 = (z7 + c6) >> (u32)56U;
  u64 t106 = (uint64_t)(z7 + c6) & (u64)0xffffffffffffffU;
  uint128_t c7 = carry7;
  u64 t71 = t106;
  uint128_t carry8 = (z8 + c7) >> (u32)56U;
  u64 t107 = (uint64_t)(z8 + c7) & (u64)0xffffffffffffffU;
  uint128_t c8 = carry8;
  u64 t81 = t107;
  u64 t91 = (uint64_t)c8;
  u64 qmu4_ = t410;
  u64 qmu5_ = t51;
  u64 qmu6_ = t61;
  u64 qmu7_ = t71;
  u64 qmu8_ = t81;
  u64 qmu9_ = t91;
  u64 y_4 = (qmu5_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_4 = qmu4_ >> (u32)40U;
  u64 z02 = x_4 | y_4;
  u64 y_5 = (qmu6_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_5 = qmu5_ >> (u32)40U;
  u64 z12 = x_5 | y_5;
  u64 y_6 = (qmu7_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_6 = qmu6_ >> (u32)40U;
  u64 z22 = x_6 | y_6;
  u64 y_7 = (qmu8_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_7 = qmu7_ >> (u32)40U;
  u64 z32 = x_7 | y_7;
  u64 y_8 = (qmu9_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_8 = qmu8_ >> (u32)40U;
  u64 z42 = x_8 | y_8;
  u64 qdiv0 = z02;
  u64 qdiv1 = z12;
  u64 qdiv2 = z22;
  u64 qdiv3 = z32;
  u64 qdiv4 = z42;
  u64 r0 = t0;
  u64 r1 = t1;
  u64 r2 = t2;
  u64 r3 = t3;
  u64 r4 = t4 & (u64)0xffffffffffU;
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
  uint128_t carry9 = xy00 >> (u32)56U;
  u64 t108 = (uint64_t)xy00 & (u64)0xffffffffffffffU;
  uint128_t c0 = carry9;
  u64 t010 = t108;
  uint128_t carry10 = (xy01 + xy10 + c0) >> (u32)56U;
  u64 t109 = (uint64_t)(xy01 + xy10 + c0) & (u64)0xffffffffffffffU;
  uint128_t c11 = carry10;
  u64 t110 = t109;
  uint128_t carry11 = (xy02 + xy11 + xy20 + c11) >> (u32)56U;
  u64 t1010 = (uint64_t)(xy02 + xy11 + xy20 + c11) & (u64)0xffffffffffffffU;
  uint128_t c21 = carry11;
  u64 t210 = t1010;
  uint128_t carry = (xy03 + xy12 + xy21 + xy30 + c21) >> (u32)56U;
  u64 t1011 = (uint64_t)(xy03 + xy12 + xy21 + xy30 + c21) & (u64)0xffffffffffffffU;
  uint128_t c31 = carry;
  u64 t310 = t1011;
  u64 t411 = (uint64_t)(xy04 + xy13 + xy22 + xy31 + xy40 + c31) & (u64)0xffffffffffU;
  u64 qmul0 = t010;
  u64 qmul1 = t110;
  u64 qmul2 = t210;
  u64 qmul3 = t310;
  u64 qmul4 = t411;
  u64 b5 = (r0 - qmul0) >> (u32)63U;
  u64 t1012 = (b5 << (u32)56U) + r0 - qmul0;
  u64 c1 = b5;
  u64 t011 = t1012;
  u64 b6 = (r1 - (qmul1 + c1)) >> (u32)63U;
  u64 t1013 = (b6 << (u32)56U) + r1 - (qmul1 + c1);
  u64 c2 = b6;
  u64 t111 = t1013;
  u64 b7 = (r2 - (qmul2 + c2)) >> (u32)63U;
  u64 t1014 = (b7 << (u32)56U) + r2 - (qmul2 + c2);
  u64 c3 = b7;
  u64 t211 = t1014;
  u64 b8 = (r3 - (qmul3 + c3)) >> (u32)63U;
  u64 t1015 = (b8 << (u32)56U) + r3 - (qmul3 + c3);
  u64 c4 = b8;
  u64 t311 = t1015;
  u64 b9 = (r4 - (qmul4 + c4)) >> (u32)63U;
  u64 t1016 = (b9 << (u32)40U) + r4 - (qmul4 + c4);
  u64 t412 = t1016;
  u64 s0 = t011;
  u64 s1 = t111;
  u64 s2 = t211;
  u64 s3 = t311;
  u64 s4 = t412;
  u64 m01 = (u64)0x12631a5cf5d3edU;
  u64 m11 = (u64)0xf9dea2f79cd658U;
  u64 m21 = (u64)0x000000000014deU;
  u64 m31 = (u64)0x00000000000000U;
  u64 m41 = (u64)0x00000010000000U;
  u64 y0 = m01;
  u64 y1 = m11;
  u64 y2 = m21;
  u64 y3 = m31;
  u64 y4 = m41;
  u64 b10 = (s0 - y0) >> (u32)63U;
  u64 t1017 = (b10 << (u32)56U) + s0 - y0;
  u64 b0 = b10;
  u64 t01 = t1017;
  u64 b11 = (s1 - (y1 + b0)) >> (u32)63U;
  u64 t1018 = (b11 << (u32)56U) + s1 - (y1 + b0);
  u64 b1 = b11;
  u64 t11 = t1018;
  u64 b12 = (s2 - (y2 + b1)) >> (u32)63U;
  u64 t1019 = (b12 << (u32)56U) + s2 - (y2 + b1);
  u64 b2 = b12;
  u64 t21 = t1019;
  u64 b13 = (s3 - (y3 + b2)) >> (u32)63U;
  u64 t1020 = (b13 << (u32)56U) + s3 - (y3 + b2);
  u64 b3 = b13;
  u64 t31 = t1020;
  u64 b = (s4 - (y4 + b3)) >> (u32)63U;
  u64 t10 = (b << (u32)56U) + s4 - (y4 + b3);
  u64 b4 = b;
  u64 t41 = t10;
  u64 mask = b4 - (u64)1U;
  u64 z03 = s0 ^ (mask & (s0 ^ t01));
  u64 z13 = s1 ^ (mask & (s1 ^ t11));
  u64 z23 = s2 ^ (mask & (s2 ^ t21));
  u64 z33 = s3 ^ (mask & (s3 ^ t31));
  u64 z43 = s4 ^ (mask & (s4 ^ t41));
  u64 z04 = z03;
  u64 z14 = z13;
  u64 z24 = z23;
  u64 z34 = z33;
  u64 z44 = z43;
  u64 o0 = z04;
  u64 o1 = z14;
  u64 o2 = z24;
  u64 o3 = z34;
  u64 o4 = z44;
  u64 z0 = o0;
  u64 z1 = o1;
  u64 z2 = o2;
  u64 z3 = o3;
  u64 z4 = o4;
  z[0U] = z0;
  z[1U] = z1;
  z[2U] = z2;
  z[3U] = z3;
  z[4U] = z4;
}

static void mul_modq(u64 *out, u64 *x, u64 *y)
{
  u64 x0 = x[0U];
  u64 x1 = x[1U];
  u64 x2 = x[2U];
  u64 x3 = x[3U];
  u64 x4 = x[4U];
  u64 y0 = y[0U];
  u64 y1 = y[1U];
  u64 y2 = y[2U];
  u64 y3 = y[3U];
  u64 y4 = y[4U];
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
  uint128_t carry0 = z00 >> (u32)56U;
  u64 t10 = (uint64_t)z00 & (u64)0xffffffffffffffU;
  uint128_t c00 = carry0;
  u64 t00 = t10;
  uint128_t carry1 = (z10 + c00) >> (u32)56U;
  u64 t11 = (uint64_t)(z10 + c00) & (u64)0xffffffffffffffU;
  uint128_t c10 = carry1;
  u64 t12 = t11;
  uint128_t carry2 = (z20 + c10) >> (u32)56U;
  u64 t13 = (uint64_t)(z20 + c10) & (u64)0xffffffffffffffU;
  uint128_t c20 = carry2;
  u64 t20 = t13;
  uint128_t carry3 = (z30 + c20) >> (u32)56U;
  u64 t14 = (uint64_t)(z30 + c20) & (u64)0xffffffffffffffU;
  uint128_t c30 = carry3;
  u64 t30 = t14;
  uint128_t carry4 = (z40 + c30) >> (u32)56U;
  u64 t15 = (uint64_t)(z40 + c30) & (u64)0xffffffffffffffU;
  uint128_t c40 = carry4;
  u64 t40 = t15;
  uint128_t carry5 = (z50 + c40) >> (u32)56U;
  u64 t16 = (uint64_t)(z50 + c40) & (u64)0xffffffffffffffU;
  uint128_t c50 = carry5;
  u64 t50 = t16;
  uint128_t carry6 = (z60 + c50) >> (u32)56U;
  u64 t17 = (uint64_t)(z60 + c50) & (u64)0xffffffffffffffU;
  uint128_t c60 = carry6;
  u64 t60 = t17;
  uint128_t carry7 = (z70 + c60) >> (u32)56U;
  u64 t18 = (uint64_t)(z70 + c60) & (u64)0xffffffffffffffU;
  uint128_t c70 = carry7;
  u64 t70 = t18;
  uint128_t carry8 = (z80 + c70) >> (u32)56U;
  u64 t19 = (uint64_t)(z80 + c70) & (u64)0xffffffffffffffU;
  uint128_t c80 = carry8;
  u64 t80 = t19;
  u64 t90 = (uint64_t)c80;
  u64 r0 = t00;
  u64 r1 = t12;
  u64 r2 = t20;
  u64 r3 = t30;
  u64 r4 = t40;
  u64 r5 = t50;
  u64 r6 = t60;
  u64 r7 = t70;
  u64 r8 = t80;
  u64 r9 = t90;
  u64 m00 = (u64)0x12631a5cf5d3edU;
  u64 m10 = (u64)0xf9dea2f79cd658U;
  u64 m20 = (u64)0x000000000014deU;
  u64 m30 = (u64)0x00000000000000U;
  u64 m40 = (u64)0x00000010000000U;
  u64 m0 = m00;
  u64 m1 = m10;
  u64 m2 = m20;
  u64 m3 = m30;
  u64 m4 = m40;
  u64 m010 = (u64)0x9ce5a30a2c131bU;
  u64 m110 = (u64)0x215d086329a7edU;
  u64 m210 = (u64)0xffffffffeb2106U;
  u64 m310 = (u64)0xffffffffffffffU;
  u64 m410 = (u64)0x00000fffffffffU;
  u64 mu0 = m010;
  u64 mu1 = m110;
  u64 mu2 = m210;
  u64 mu3 = m310;
  u64 mu4 = m410;
  u64 y_ = (r5 & (u64)0xffffffU) << (u32)32U;
  u64 x_ = r4 >> (u32)24U;
  u64 z01 = x_ | y_;
  u64 y_0 = (r6 & (u64)0xffffffU) << (u32)32U;
  u64 x_0 = r5 >> (u32)24U;
  u64 z11 = x_0 | y_0;
  u64 y_1 = (r7 & (u64)0xffffffU) << (u32)32U;
  u64 x_1 = r6 >> (u32)24U;
  u64 z21 = x_1 | y_1;
  u64 y_2 = (r8 & (u64)0xffffffU) << (u32)32U;
  u64 x_2 = r7 >> (u32)24U;
  u64 z31 = x_2 | y_2;
  u64 y_3 = (r9 & (u64)0xffffffU) << (u32)32U;
  u64 x_3 = r8 >> (u32)24U;
  u64 z41 = x_3 | y_3;
  u64 q0 = z01;
  u64 q1 = z11;
  u64 q2 = z21;
  u64 q3 = z31;
  u64 q4 = z41;
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
  uint128_t carry9 = z02 >> (u32)56U;
  uint128_t c01 = carry9;
  uint128_t carry10 = (z12 + c01) >> (u32)56U;
  u64 t21 = (uint64_t)(z12 + c01) & (u64)0xffffffffffffffU;
  uint128_t c11 = carry10;
  uint128_t carry11 = (z22 + c11) >> (u32)56U;
  u64 t22 = (uint64_t)(z22 + c11) & (u64)0xffffffffffffffU;
  uint128_t c21 = carry11;
  uint128_t carry12 = (z32 + c21) >> (u32)56U;
  u64 t23 = (uint64_t)(z32 + c21) & (u64)0xffffffffffffffU;
  uint128_t c31 = carry12;
  uint128_t carry13 = (z42 + c31) >> (u32)56U;
  u64 t24 = (uint64_t)(z42 + c31) & (u64)0xffffffffffffffU;
  uint128_t c41 = carry13;
  u64 t41 = t24;
  uint128_t carry14 = (z5 + c41) >> (u32)56U;
  u64 t25 = (uint64_t)(z5 + c41) & (u64)0xffffffffffffffU;
  uint128_t c5 = carry14;
  u64 t5 = t25;
  uint128_t carry15 = (z6 + c5) >> (u32)56U;
  u64 t26 = (uint64_t)(z6 + c5) & (u64)0xffffffffffffffU;
  uint128_t c6 = carry15;
  u64 t6 = t26;
  uint128_t carry16 = (z7 + c6) >> (u32)56U;
  u64 t27 = (uint64_t)(z7 + c6) & (u64)0xffffffffffffffU;
  uint128_t c7 = carry16;
  u64 t7 = t27;
  uint128_t carry17 = (z8 + c7) >> (u32)56U;
  u64 t28 = (uint64_t)(z8 + c7) & (u64)0xffffffffffffffU;
  uint128_t c8 = carry17;
  u64 t8 = t28;
  u64 t9 = (uint64_t)c8;
  u64 qmu4_ = t41;
  u64 qmu5_ = t5;
  u64 qmu6_ = t6;
  u64 qmu7_ = t7;
  u64 qmu8_ = t8;
  u64 qmu9_ = t9;
  u64 y_4 = (qmu5_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_4 = qmu4_ >> (u32)40U;
  u64 z03 = x_4 | y_4;
  u64 y_5 = (qmu6_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_5 = qmu5_ >> (u32)40U;
  u64 z13 = x_5 | y_5;
  u64 y_6 = (qmu7_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_6 = qmu6_ >> (u32)40U;
  u64 z23 = x_6 | y_6;
  u64 y_7 = (qmu8_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_7 = qmu7_ >> (u32)40U;
  u64 z33 = x_7 | y_7;
  u64 y_8 = (qmu9_ & (u64)0xffffffffffU) << (u32)16U;
  u64 x_8 = qmu8_ >> (u32)40U;
  u64 z43 = x_8 | y_8;
  u64 qdiv0 = z03;
  u64 qdiv1 = z13;
  u64 qdiv2 = z23;
  u64 qdiv3 = z33;
  u64 qdiv4 = z43;
  u64 r01 = r0;
  u64 r11 = r1;
  u64 r21 = r2;
  u64 r31 = r3;
  u64 r41 = r4 & (u64)0xffffffffffU;
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
  uint128_t carry18 = xy00 >> (u32)56U;
  u64 t29 = (uint64_t)xy00 & (u64)0xffffffffffffffU;
  uint128_t c0 = carry18;
  u64 t01 = t29;
  uint128_t carry19 = (xy01 + xy10 + c0) >> (u32)56U;
  u64 t31 = (uint64_t)(xy01 + xy10 + c0) & (u64)0xffffffffffffffU;
  uint128_t c12 = carry19;
  u64 t110 = t31;
  uint128_t carry20 = (xy02 + xy11 + xy20 + c12) >> (u32)56U;
  u64 t32 = (uint64_t)(xy02 + xy11 + xy20 + c12) & (u64)0xffffffffffffffU;
  uint128_t c22 = carry20;
  u64 t210 = t32;
  uint128_t carry = (xy03 + xy12 + xy21 + xy30 + c22) >> (u32)56U;
  u64 t33 = (uint64_t)(xy03 + xy12 + xy21 + xy30 + c22) & (u64)0xffffffffffffffU;
  uint128_t c32 = carry;
  u64 t34 = t33;
  u64 t42 = (uint64_t)(xy04 + xy13 + xy22 + xy31 + xy40 + c32) & (u64)0xffffffffffU;
  u64 qmul0 = t01;
  u64 qmul1 = t110;
  u64 qmul2 = t210;
  u64 qmul3 = t34;
  u64 qmul4 = t42;
  u64 b5 = (r01 - qmul0) >> (u32)63U;
  u64 t35 = (b5 << (u32)56U) + r01 - qmul0;
  u64 c1 = b5;
  u64 t02 = t35;
  u64 b6 = (r11 - (qmul1 + c1)) >> (u32)63U;
  u64 t36 = (b6 << (u32)56U) + r11 - (qmul1 + c1);
  u64 c2 = b6;
  u64 t111 = t36;
  u64 b7 = (r21 - (qmul2 + c2)) >> (u32)63U;
  u64 t37 = (b7 << (u32)56U) + r21 - (qmul2 + c2);
  u64 c3 = b7;
  u64 t211 = t37;
  u64 b8 = (r31 - (qmul3 + c3)) >> (u32)63U;
  u64 t38 = (b8 << (u32)56U) + r31 - (qmul3 + c3);
  u64 c4 = b8;
  u64 t39 = t38;
  u64 b9 = (r41 - (qmul4 + c4)) >> (u32)63U;
  u64 t43 = (b9 << (u32)40U) + r41 - (qmul4 + c4);
  u64 t44 = t43;
  u64 s0 = t02;
  u64 s1 = t111;
  u64 s2 = t211;
  u64 s3 = t39;
  u64 s4 = t44;
  u64 m01 = (u64)0x12631a5cf5d3edU;
  u64 m11 = (u64)0xf9dea2f79cd658U;
  u64 m21 = (u64)0x000000000014deU;
  u64 m31 = (u64)0x00000000000000U;
  u64 m41 = (u64)0x00000010000000U;
  u64 y01 = m01;
  u64 y11 = m11;
  u64 y21 = m21;
  u64 y31 = m31;
  u64 y41 = m41;
  u64 b10 = (s0 - y01) >> (u32)63U;
  u64 t45 = (b10 << (u32)56U) + s0 - y01;
  u64 b0 = b10;
  u64 t0 = t45;
  u64 b11 = (s1 - (y11 + b0)) >> (u32)63U;
  u64 t46 = (b11 << (u32)56U) + s1 - (y11 + b0);
  u64 b1 = b11;
  u64 t1 = t46;
  u64 b12 = (s2 - (y21 + b1)) >> (u32)63U;
  u64 t47 = (b12 << (u32)56U) + s2 - (y21 + b1);
  u64 b2 = b12;
  u64 t2 = t47;
  u64 b13 = (s3 - (y31 + b2)) >> (u32)63U;
  u64 t48 = (b13 << (u32)56U) + s3 - (y31 + b2);
  u64 b3 = b13;
  u64 t3 = t48;
  u64 b = (s4 - (y41 + b3)) >> (u32)63U;
  u64 t = (b << (u32)56U) + s4 - (y41 + b3);
  u64 b4 = b;
  u64 t4 = t;
  u64 mask = b4 - (u64)1U;
  u64 z04 = s0 ^ (mask & (s0 ^ t0));
  u64 z14 = s1 ^ (mask & (s1 ^ t1));
  u64 z24 = s2 ^ (mask & (s2 ^ t2));
  u64 z34 = s3 ^ (mask & (s3 ^ t3));
  u64 z44 = s4 ^ (mask & (s4 ^ t4));
  u64 z05 = z04;
  u64 z15 = z14;
  u64 z25 = z24;
  u64 z35 = z34;
  u64 z45 = z44;
  u64 o00 = z05;
  u64 o10 = z15;
  u64 o20 = z25;
  u64 o30 = z35;
  u64 o40 = z45;
  u64 o0 = o00;
  u64 o1 = o10;
  u64 o2 = o20;
  u64 o3 = o30;
  u64 o4 = o40;
  u64 z0 = o0;
  u64 z1 = o1;
  u64 z2 = o2;
  u64 z3 = o3;
  u64 z4 = o4;
  out[0U] = z0;
  out[1U] = z1;
  out[2U] = z2;
  out[3U] = z3;
  out[4U] = z4;
}

static void add_modq(u64 *out, u64 *x, u64 *y)
{
  u64 x0 = x[0U];
  u64 x1 = x[1U];
  u64 x2 = x[2U];
  u64 x3 = x[3U];
  u64 x4 = x[4U];
  u64 y0 = y[0U];
  u64 y1 = y[1U];
  u64 y2 = y[2U];
  u64 y3 = y[3U];
  u64 y4 = y[4U];
  u64 carry0 = (x0 + y0) >> (u32)56U;
  u64 t0 = (x0 + y0) & (u64)0xffffffffffffffU;
  u64 t00 = t0;
  u64 c0 = carry0;
  u64 carry1 = (x1 + y1 + c0) >> (u32)56U;
  u64 t1 = (x1 + y1 + c0) & (u64)0xffffffffffffffU;
  u64 t10 = t1;
  u64 c1 = carry1;
  u64 carry2 = (x2 + y2 + c1) >> (u32)56U;
  u64 t2 = (x2 + y2 + c1) & (u64)0xffffffffffffffU;
  u64 t20 = t2;
  u64 c2 = carry2;
  u64 carry = (x3 + y3 + c2) >> (u32)56U;
  u64 t3 = (x3 + y3 + c2) & (u64)0xffffffffffffffU;
  u64 t30 = t3;
  u64 c3 = carry;
  u64 t4 = x4 + y4 + c3;
  u64 m0 = (u64)0x12631a5cf5d3edU;
  u64 m1 = (u64)0xf9dea2f79cd658U;
  u64 m2 = (u64)0x000000000014deU;
  u64 m3 = (u64)0x00000000000000U;
  u64 m4 = (u64)0x00000010000000U;
  u64 y01 = m0;
  u64 y11 = m1;
  u64 y21 = m2;
  u64 y31 = m3;
  u64 y41 = m4;
  u64 b5 = (t00 - y01) >> (u32)63U;
  u64 t5 = (b5 << (u32)56U) + t00 - y01;
  u64 b0 = b5;
  u64 t01 = t5;
  u64 b6 = (t10 - (y11 + b0)) >> (u32)63U;
  u64 t6 = (b6 << (u32)56U) + t10 - (y11 + b0);
  u64 b1 = b6;
  u64 t11 = t6;
  u64 b7 = (t20 - (y21 + b1)) >> (u32)63U;
  u64 t7 = (b7 << (u32)56U) + t20 - (y21 + b1);
  u64 b2 = b7;
  u64 t21 = t7;
  u64 b8 = (t30 - (y31 + b2)) >> (u32)63U;
  u64 t8 = (b8 << (u32)56U) + t30 - (y31 + b2);
  u64 b3 = b8;
  u64 t31 = t8;
  u64 b = (t4 - (y41 + b3)) >> (u32)63U;
  u64 t = (b << (u32)56U) + t4 - (y41 + b3);
  u64 b4 = b;
  u64 t41 = t;
  u64 mask = b4 - (u64)1U;
  u64 z00 = t00 ^ (mask & (t00 ^ t01));
  u64 z10 = t10 ^ (mask & (t10 ^ t11));
  u64 z20 = t20 ^ (mask & (t20 ^ t21));
  u64 z30 = t30 ^ (mask & (t30 ^ t31));
  u64 z40 = t4 ^ (mask & (t4 ^ t41));
  u64 z01 = z00;
  u64 z11 = z10;
  u64 z21 = z20;
  u64 z31 = z30;
  u64 z41 = z40;
  u64 o0 = z01;
  u64 o1 = z11;
  u64 o2 = z21;
  u64 o3 = z31;
  u64 o4 = z41;
  u64 z0 = o0;
  u64 z1 = o1;
  u64 z2 = o2;
  u64 z3 = o3;
  u64 z4 = o4;
  out[0U] = z0;
  out[1U] = z1;
  out[2U] = z2;
  out[3U] = z3;
  out[4U] = z4;
}

static u64 hload56_le(u8 *b, u32 off)
{
  u8 *b8 = b + off;
  u64 u = load64_le(b8);
  u64 z = u;
  return z & (u64)0xffffffffffffffU;
}

static void load_64_bytes(u64 *out, u8 *b)
{
  u64 b0 = hload56_le(b, (u32)0U);
  u64 b1 = hload56_le(b, (u32)7U);
  u64 b2 = hload56_le(b, (u32)14U);
  u64 b3 = hload56_le(b, (u32)21U);
  u64 b4 = hload56_le(b, (u32)28U);
  u64 b5 = hload56_le(b, (u32)35U);
  u64 b6 = hload56_le(b, (u32)42U);
  u64 b7 = hload56_le(b, (u32)49U);
  u64 b8 = hload56_le(b, (u32)56U);
  u8 b63 = b[63U];
  u64 b9 = (u64)b63;
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

static u64 hload56_le_(u8 *b, u32 off)
{
  u8 *b8 = b + off;
  u64 u = load64_le(b8);
  u64 z = u;
  return z & (u64)0xffffffffffffffU;
}

static void load_32_bytes(u64 *out, u8 *b)
{
  u64 b0 = hload56_le_(b, (u32)0U);
  u64 b1 = hload56_le_(b, (u32)7U);
  u64 b2 = hload56_le_(b, (u32)14U);
  u64 b3 = hload56_le_(b, (u32)21U);
  u32 u = load32_le(b + (u32)28U);
  u32 b4 = u;
  u64 b41 = (u64)b4;
  out[0U] = b0;
  out[1U] = b1;
  out[2U] = b2;
  out[3U] = b3;
  out[4U] = b41;
}

static void hstore56_le(u8 *out, u32 off, u64 x)
{
  u8 *b8 = out + off;
  store64_le(b8, x);
}

static void store_56(u8 *out, u64 *b)
{
  u64 b0 = b[0U];
  u64 b1 = b[1U];
  u64 b2 = b[2U];
  u64 b3 = b[3U];
  u64 b4 = b[4U];
  u32 b4_ = (u32)b4;
  hstore56_le(out, (u32)0U, b0);
  hstore56_le(out, (u32)7U, b1);
  hstore56_le(out, (u32)14U, b2);
  hstore56_le(out, (u32)21U, b3);
  store32_le(out + (u32)28U, b4_);
}

static void sha512_pre_msg(u8 *h, u8 *prefix, u32 len, u8 *input)
{
  KRML_CHECK_SIZE(sizeof (u8), len + (u32)32U);
  {
    u8 pre_msg[len + (u32)32U];
    memset(pre_msg, 0U, (len + (u32)32U) * sizeof (u8));
    memcpy(pre_msg, prefix, (u32)32U * sizeof (u8));
    memcpy(pre_msg + (u32)32U, input, len * sizeof (u8));
    Hacl_Hash_SHA2_hash_512(pre_msg, len + (u32)32U, h);
  }
}

static void sha512_pre_pre2_msg(u8 *h, u8 *prefix, u8 *prefix2, u32 len, u8 *input)
{
  KRML_CHECK_SIZE(sizeof (u8), len + (u32)64U);
  {
    u8 pre_msg[len + (u32)64U];
    memset(pre_msg, 0U, (len + (u32)64U) * sizeof (u8));
    memcpy(pre_msg, prefix, (u32)32U * sizeof (u8));
    memcpy(pre_msg + (u32)32U, prefix2, (u32)32U * sizeof (u8));
    memcpy(pre_msg + (u32)64U, input, len * sizeof (u8));
    Hacl_Hash_SHA2_hash_512(pre_msg, len + (u32)64U, h);
  }
}

static void sha512_modq_pre(u64 *out, u8 *prefix, u32 len, u8 *input)
{
  u64 tmp[10U] = { 0U };
  u8 hash[64U] = { 0U };
  sha512_pre_msg(hash, prefix, len, input);
  load_64_bytes(tmp, hash);
  barrett_reduction(out, tmp);
}

static void sha512_modq_pre_pre2(u64 *out, u8 *prefix, u8 *prefix2, u32 len, u8 *input)
{
  u64 tmp[10U] = { 0U };
  u8 hash[64U] = { 0U };
  sha512_pre_pre2_msg(hash, prefix, prefix2, len, input);
  load_64_bytes(tmp, hash);
  barrett_reduction(out, tmp);
}

static void point_mul_g_compress(u8 *out, u8 *s)
{
  u64 tmp[20U] = { 0U };
  point_mul_g(tmp, s);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, tmp);
}

static void sign_step_1(u8 *secret, u8 *tmp_bytes)
{
  u8 *a__ = tmp_bytes + (u32)96U;
  u8 *apre = tmp_bytes + (u32)224U;
  u8 *a = apre;
  secret_expand(apre, secret);
  point_mul_g_compress(a__, a);
}

static void sign_step_2(u32 len, u8 *msg, u8 *tmp_bytes, u64 *tmp_ints)
{
  u64 *r = tmp_ints + (u32)20U;
  u8 *apre = tmp_bytes + (u32)224U;
  u8 *prefix = apre + (u32)32U;
  sha512_modq_pre(r, prefix, len, msg);
}

static void sign_step_3(u8 *tmp_bytes, u64 *tmp_ints)
{
  u8 rb[32U] = { 0U };
  u64 *r = tmp_ints + (u32)20U;
  u8 *rs_ = tmp_bytes + (u32)160U;
  store_56(rb, r);
  point_mul_g_compress(rs_, rb);
}

static void sign_step_4(u32 len, u8 *msg, u8 *tmp_bytes, u64 *tmp_ints)
{
  u64 *h = tmp_ints + (u32)60U;
  u8 *a__ = tmp_bytes + (u32)96U;
  u8 *rs_ = tmp_bytes + (u32)160U;
  sha512_modq_pre_pre2(h, rs_, a__, len, msg);
}

static void sign_step_5(u8 *tmp_bytes, u64 *tmp_ints)
{
  u64 *r = tmp_ints + (u32)20U;
  u64 *aq = tmp_ints + (u32)45U;
  u64 *ha = tmp_ints + (u32)50U;
  u64 *s = tmp_ints + (u32)55U;
  u64 *h = tmp_ints + (u32)60U;
  u8 *s_ = tmp_bytes + (u32)192U;
  u8 *a = tmp_bytes + (u32)224U;
  load_32_bytes(aq, a);
  mul_modq(ha, h, aq);
  add_modq(s, r, ha);
  store_56(s_, s);
}

static void pow2_252m2(u64 *out, u64 *z)
{
  u64 buf[20U] = { 0U };
  u64 *a0 = buf;
  u64 *t00 = buf + (u32)5U;
  u64 *b0 = buf + (u32)10U;
  u64 *c0 = buf + (u32)15U;
  u64 *a;
  u64 *t0;
  u64 *b;
  u64 *c;
  fsquare_times(a0, z, (u32)1U);
  fsquare_times(t00, a0, (u32)2U);
  fmul(b0, t00, z);
  fmul(a0, b0, a0);
  fsquare_times(t00, a0, (u32)1U);
  fmul(b0, t00, b0);
  fsquare_times(t00, b0, (u32)5U);
  fmul(b0, t00, b0);
  fsquare_times(t00, b0, (u32)10U);
  fmul(c0, t00, b0);
  fsquare_times(t00, c0, (u32)20U);
  fmul(t00, t00, c0);
  fsquare_times_inplace(t00, (u32)10U);
  fmul(b0, t00, b0);
  fsquare_times(t00, b0, (u32)50U);
  a = buf;
  t0 = buf + (u32)5U;
  b = buf + (u32)10U;
  c = buf + (u32)15U;
  fsquare_times(a, z, (u32)1U);
  fmul(c, t0, b);
  fsquare_times(t0, c, (u32)100U);
  fmul(t0, t0, c);
  fsquare_times_inplace(t0, (u32)50U);
  fmul(t0, t0, b);
  fsquare_times_inplace(t0, (u32)2U);
  fmul(out, t0, a);
}

static bool is_0(u64 *x)
{
  u64 x0 = x[0U];
  u64 x1 = x[1U];
  u64 x2 = x[2U];
  u64 x3 = x[3U];
  u64 x4 = x[4U];
  return x0 == (u64)0U && x1 == (u64)0U && x2 == (u64)0U && x3 == (u64)0U && x4 == (u64)0U;
}

static void mul_modp_sqrt_m1(u64 *x)
{
  u64 sqrt_m1[5U] = { 0U };
  sqrt_m1[0U] = (u64)0x00061b274a0ea0b0U;
  sqrt_m1[1U] = (u64)0x0000d5a5fc8f189dU;
  sqrt_m1[2U] = (u64)0x0007ef5e9cbd0c60U;
  sqrt_m1[3U] = (u64)0x00078595a6804c9eU;
  sqrt_m1[4U] = (u64)0x0002b8324804fc1dU;
  fmul(x, x, sqrt_m1);
}

static bool recover_x(u64 *x, u64 *y, u64 sign)
{
  u64 tmp[20U] = { 0U };
  u64 *x2 = tmp;
  u64 x00 = y[0U];
  u64 x1 = y[1U];
  u64 x21 = y[2U];
  u64 x30 = y[3U];
  u64 x4 = y[4U];
  bool
  b =
    x00
    >= (u64)0x7ffffffffffedU
    && x1 == (u64)0x7ffffffffffffU
    && x21 == (u64)0x7ffffffffffffU
    && x30 == (u64)0x7ffffffffffffU
    && x4 == (u64)0x7ffffffffffffU;
  bool res;
  if (b)
    res = false;
  else
  {
    u64 tmp1[25U] = { 0U };
    u64 *one = tmp1;
    u64 *y2 = tmp1 + (u32)5U;
    u64 *dyyi = tmp1 + (u32)10U;
    u64 *dyy = tmp1 + (u32)15U;
    one[0U] = (u64)1U;
    one[1U] = (u64)0U;
    one[2U] = (u64)0U;
    one[3U] = (u64)0U;
    one[4U] = (u64)0U;
    fsquare(y2, y);
    times_d(dyy, y2);
    fsum(dyy, one);
    Hacl_Bignum25519_reduce_513(dyy);
    Hacl_Bignum25519_inverse(dyyi, dyy);
    Hacl_Bignum25519_fdifference(one, y2);
    fmul(x2, one, dyyi);
    reduce(x2);
    {
      bool x2_is_0 = is_0(x2);
      u8 z;
      if (x2_is_0)
        if (sign == (u64)0U)
        {
          x[0U] = (u64)0U;
          x[1U] = (u64)0U;
          x[2U] = (u64)0U;
          x[3U] = (u64)0U;
          x[4U] = (u64)0U;
          z = (u8)1U;
        }
        else
          z = (u8)0U;
      else
        z = (u8)2U;
      if (z == (u8)0U)
        res = false;
      else if (z == (u8)1U)
        res = true;
      else
      {
        u64 *x210 = tmp;
        u64 *x31 = tmp + (u32)5U;
        u64 *t00 = tmp + (u32)10U;
        u64 *t10 = tmp + (u32)15U;
        pow2_252m2(x31, x210);
        fsquare(t00, x31);
        memcpy(t10, x210, (u32)5U * sizeof (u64));
        Hacl_Bignum25519_fdifference(t10, t00);
        Hacl_Bignum25519_reduce_513(t10);
        reduce(t10);
        {
          bool t1_is_0 = is_0(t10);
          if (!t1_is_0)
            mul_modp_sqrt_m1(x31);
          {
            u64 *x211 = tmp;
            u64 *x3 = tmp + (u32)5U;
            u64 *t01 = tmp + (u32)10U;
            u64 *t1 = tmp + (u32)15U;
            fsquare(t01, x3);
            memcpy(t1, x211, (u32)5U * sizeof (u64));
            Hacl_Bignum25519_fdifference(t1, t01);
            Hacl_Bignum25519_reduce_513(t1);
            reduce(t1);
            {
              bool z1 = is_0(t1);
              if (z1 == false)
                res = false;
              else
              {
                u64 *x32 = tmp + (u32)5U;
                u64 *t0 = tmp + (u32)10U;
                reduce(x32);
                {
                  u64 x0 = x32[0U];
                  u64 x01 = x0 & (u64)1U;
                  if (!(x01 == sign))
                  {
                    t0[0U] = (u64)0U;
                    t0[1U] = (u64)0U;
                    t0[2U] = (u64)0U;
                    t0[3U] = (u64)0U;
                    t0[4U] = (u64)0U;
                    Hacl_Bignum25519_fdifference(x32, t0);
                    Hacl_Bignum25519_reduce_513(x32);
                    reduce(x32);
                  }
                  memcpy(x, x32, (u32)5U * sizeof (u64));
                  res = true;
                }
              }
            }
          }
        }
      }
    }
  }
  {
    bool res0 = res;
    return res0;
  }
}

bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(u64 *out, u8 *s)
{
  u64 tmp[10U] = { 0U };
  u64 *y = tmp;
  u64 *x = tmp + (u32)5U;
  u8 s31 = s[31U];
  u8 z0 = s31 >> (u32)7U;
  u64 sign = (u64)z0;
  bool z;
  bool res0;
  bool res;
  Hacl_Bignum25519_load_51(y, s);
  z = recover_x(x, y, sign);
  if (z == false)
    res0 = false;
  else
  {
    u64 *outx = out;
    u64 *outy = out + (u32)5U;
    u64 *outz = out + (u32)10U;
    u64 *outt = out + (u32)15U;
    memcpy(outx, x, (u32)5U * sizeof (u64));
    memcpy(outy, y, (u32)5U * sizeof (u64));
    outz[0U] = (u64)1U;
    outz[1U] = (u64)0U;
    outz[2U] = (u64)0U;
    outz[3U] = (u64)0U;
    outz[4U] = (u64)0U;
    fmul(outt, x, y);
    res0 = true;
  }
  res = res0;
  return res;
}

static bool gte_q(u64 *s)
{
  u64 s0 = s[0U];
  u64 s1 = s[1U];
  u64 s2 = s[2U];
  u64 s3 = s[3U];
  u64 s4 = s[4U];
  if (s4 > (u64)0x00000010000000U)
    return true;
  if (s4 < (u64)0x00000010000000U)
    return false;
  if (s3 > (u64)0x00000000000000U)
    return true;
  if (s2 > (u64)0x000000000014deU)
    return true;
  if (s2 < (u64)0x000000000014deU)
    return false;
  if (s1 > (u64)0xf9dea2f79cd658U)
    return true;
  if (s1 < (u64)0xf9dea2f79cd658U)
    return false;
  if (s0 >= (u64)0x12631a5cf5d3edU)
    return true;
  return false;
}

static bool eq(u64 *a, u64 *b)
{
  u64 a0 = a[0U];
  u64 a1 = a[1U];
  u64 a2 = a[2U];
  u64 a3 = a[3U];
  u64 a4 = a[4U];
  u64 b0 = b[0U];
  u64 b1 = b[1U];
  u64 b2 = b[2U];
  u64 b3 = b[3U];
  u64 b4 = b[4U];
  return a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4;
}

static bool point_equal_1(u64 *p, u64 *q, u64 *tmp)
{
  u64 *pxqz = tmp;
  u64 *qxpz = tmp + (u32)5U;
  fmul(pxqz, p, q + (u32)10U);
  reduce(pxqz);
  fmul(qxpz, q, p + (u32)10U);
  reduce(qxpz);
  return eq(pxqz, qxpz);
}

static bool point_equal_2(u64 *p, u64 *q, u64 *tmp)
{
  u64 *pyqz = tmp + (u32)10U;
  u64 *qypz = tmp + (u32)15U;
  fmul(pyqz, p + (u32)5U, q + (u32)10U);
  reduce(pyqz);
  fmul(qypz, q + (u32)5U, p + (u32)10U);
  reduce(qypz);
  return eq(pyqz, qypz);
}

bool Hacl_Impl_Ed25519_PointEqual_point_equal(u64 *p, u64 *q)
{
  u64 tmp[20U] = { 0U };
  bool b = point_equal_1(p, q, tmp);
  if (b)
    return point_equal_2(p, q, tmp);
  return false;
}

void Hacl_Ed25519_sign(u8 *signature, u8 *priv, u32 len, u8 *msg)
{
  u8 tmp_bytes[352U] = { 0U };
  u64 tmp_ints[65U] = { 0U };
  u8 *rs_ = tmp_bytes + (u32)160U;
  u8 *s_ = tmp_bytes + (u32)192U;
  sign_step_1(priv, tmp_bytes);
  sign_step_2(len, msg, tmp_bytes, tmp_ints);
  sign_step_3(tmp_bytes, tmp_ints);
  sign_step_4(len, msg, tmp_bytes, tmp_ints);
  sign_step_5(tmp_bytes, tmp_ints);
  memcpy(signature, rs_, (u32)32U * sizeof (u8));
  memcpy(signature + (u32)32U, s_, (u32)32U * sizeof (u8));
}

bool Hacl_Ed25519_verify(u8 *pub, u32 len, u8 *msg, u8 *signature)
{
  u64 tmp[45U] = { 0U };
  u8 tmp_[32U] = { 0U };
  u64 *a_ = tmp;
  u64 *r_ = tmp + (u32)20U;
  bool b = Hacl_Impl_Ed25519_PointDecompress_point_decompress(a_, pub);
  bool res;
  if (b)
  {
    u8 *rs = signature;
    bool b_ = Hacl_Impl_Ed25519_PointDecompress_point_decompress(r_, rs);
    if (b_)
    {
      u8 *rs1 = signature;
      u64 *a_1 = tmp;
      u64 *r_1 = tmp + (u32)20U;
      u64 *s1 = tmp + (u32)40U;
      load_32_bytes(s1, signature + (u32)32U);
      {
        bool b__ = gte_q(s1);
        if (b__)
          res = false;
        else
        {
          u64 r_2[5U] = { 0U };
          sha512_modq_pre_pre2(r_2, rs1, pub, len, msg);
          store_56(tmp_, r_2);
          {
            u8 *uu____0 = signature + (u32)32U;
            u64 tmp1[60U] = { 0U };
            u64 *hA = tmp1;
            u64 *rhA = tmp1 + (u32)20U;
            u64 *sB = tmp1 + (u32)40U;
            point_mul_g(sB, uu____0);
            Hacl_Impl_Ed25519_Ladder_point_mul(hA, tmp_, a_1);
            Hacl_Impl_Ed25519_PointAdd_point_add(rhA, r_1, hA);
            {
              bool b1 = Hacl_Impl_Ed25519_PointEqual_point_equal(sB, rhA);
              bool b10 = b1;
              res = b10;
            }
          }
        }
      }
    }
    else
      res = false;
  }
  else
    res = false;
  {
    bool res0 = res;
    return res0;
  }
}

void Hacl_Ed25519_secret_to_public(u8 *pub, u8 *priv)
{
  secret_to_public(pub, priv);
}

void Hacl_Ed25519_expand_keys(u8 *ks, u8 *priv)
{
  secret_expand(ks + (u32)32U, priv);
  secret_to_public(ks, priv);
}

void Hacl_Ed25519_sign_expanded(u8 *signature, u8 *ks, u32 len, u8 *msg)
{
  u8 tmp_bytes[352U] = { 0U };
  u64 tmp_ints[65U] = { 0U };
  u8 *rs_ = tmp_bytes + (u32)160U;
  u8 *s_ = tmp_bytes + (u32)192U;
  u8 *tmp_public = tmp_bytes + (u32)96U;
  u8 *tmp_xsecret = tmp_bytes + (u32)224U;
  memcpy(tmp_public, ks, (u32)32U * sizeof (u8));
  memcpy(tmp_xsecret, ks + (u32)32U, (u32)64U * sizeof (u8));
  sign_step_2(len, msg, tmp_bytes, tmp_ints);
  sign_step_3(tmp_bytes, tmp_ints);
  sign_step_4(len, msg, tmp_bytes, tmp_ints);
  sign_step_5(tmp_bytes, tmp_ints);
  memcpy(signature, rs_, (u32)32U * sizeof (u8));
  memcpy(signature + (u32)32U, s_, (u32)32U * sizeof (u8));
}

