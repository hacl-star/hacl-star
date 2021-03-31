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

static inline void fsum(uint64_t *a, uint64_t *b)
{
  Hacl_Impl_Curve25519_Field51_fadd(a, a, b);
}

static inline void fdifference(uint64_t *a, uint64_t *b)
{
  Hacl_Impl_Curve25519_Field51_fsub(a, b, a);
}

void Hacl_Bignum25519_reduce_513(uint64_t *a)
{
  uint64_t f0 = a[0U];
  uint64_t f1 = a[1U];
  uint64_t f2 = a[2U];
  uint64_t f3 = a[3U];
  uint64_t f4 = a[4U];
  uint64_t l_ = f0 + (uint64_t)0U;
  uint64_t tmp0 = l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = l_ >> (uint32_t)51U;
  uint64_t l_0 = f1 + c0;
  uint64_t tmp1 = l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = l_0 >> (uint32_t)51U;
  uint64_t l_1 = f2 + c1;
  uint64_t tmp2 = l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = l_1 >> (uint32_t)51U;
  uint64_t l_2 = f3 + c2;
  uint64_t tmp3 = l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = l_2 >> (uint32_t)51U;
  uint64_t l_3 = f4 + c3;
  uint64_t tmp4 = l_3 & (uint64_t)0x7ffffffffffffU;
  uint64_t c4 = l_3 >> (uint32_t)51U;
  uint64_t l_4 = tmp0 + c4 * (uint64_t)19U;
  uint64_t tmp0_ = l_4 & (uint64_t)0x7ffffffffffffU;
  uint64_t c5 = l_4 >> (uint32_t)51U;
  a[0U] = tmp0_;
  a[1U] = tmp1 + c5;
  a[2U] = tmp2;
  a[3U] = tmp3;
  a[4U] = tmp4;
}

static inline void fmul0(uint64_t *output, uint64_t *input, uint64_t *input2)
{
  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fmul(output, input, input2, tmp);
}

static inline void times_2(uint64_t *out, uint64_t *a)
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

static inline void times_d(uint64_t *out, uint64_t *a)
{
  uint64_t d[5U] = { 0U };
  d[0U] = (uint64_t)0x00034dca135978a3U;
  d[1U] = (uint64_t)0x0001a8283b156ebdU;
  d[2U] = (uint64_t)0x0005e7a26001c029U;
  d[3U] = (uint64_t)0x000739c663a03cbbU;
  d[4U] = (uint64_t)0x00052036cee2b6ffU;
  fmul0(out, d, a);
}

static inline void times_2d(uint64_t *out, uint64_t *a)
{
  uint64_t d2[5U] = { 0U };
  d2[0U] = (uint64_t)0x00069b9426b2f159U;
  d2[1U] = (uint64_t)0x00035050762add7aU;
  d2[2U] = (uint64_t)0x0003cf44c0038052U;
  d2[3U] = (uint64_t)0x0006738cc7407977U;
  d2[4U] = (uint64_t)0x0002406d9dc56dffU;
  fmul0(out, d2, a);
}

static inline void fsquare(uint64_t *out, uint64_t *a)
{
  FStar_UInt128_uint128 tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp);
}

static inline void fsquare_times(uint64_t *output, uint64_t *input, uint32_t count)
{
  FStar_UInt128_uint128 tmp[5U];
  for (uint32_t _i = 0U; _i < (uint32_t)5U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Curve25519_51_fsquare_times(output, input, tmp, count);
}

static inline void fsquare_times_inplace(uint64_t *output, uint32_t count)
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

static inline void reduce(uint64_t *out)
{
  uint64_t o0 = out[0U];
  uint64_t o1 = out[1U];
  uint64_t o2 = out[2U];
  uint64_t o3 = out[3U];
  uint64_t o4 = out[4U];
  uint64_t l_ = o0 + (uint64_t)0U;
  uint64_t tmp0 = l_ & (uint64_t)0x7ffffffffffffU;
  uint64_t c0 = l_ >> (uint32_t)51U;
  uint64_t l_0 = o1 + c0;
  uint64_t tmp1 = l_0 & (uint64_t)0x7ffffffffffffU;
  uint64_t c1 = l_0 >> (uint32_t)51U;
  uint64_t l_1 = o2 + c1;
  uint64_t tmp2 = l_1 & (uint64_t)0x7ffffffffffffU;
  uint64_t c2 = l_1 >> (uint32_t)51U;
  uint64_t l_2 = o3 + c2;
  uint64_t tmp3 = l_2 & (uint64_t)0x7ffffffffffffU;
  uint64_t c3 = l_2 >> (uint32_t)51U;
  uint64_t l_3 = o4 + c3;
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
  out[0U] = f01;
  out[1U] = f11;
  out[2U] = f21;
  out[3U] = f31;
  out[4U] = f41;
}

void Hacl_Bignum25519_load_51(uint64_t *output, uint8_t *input)
{
  uint64_t u64s[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = u64s;
    uint8_t *bj = input + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t u64s3 = u64s[3U];
  u64s[3U] = u64s3 & (uint64_t)0x7fffffffffffffffU;
  output[0U] = u64s[0U] & (uint64_t)0x7ffffffffffffU;
  output[1U] = u64s[0U] >> (uint32_t)51U | (u64s[1U] & (uint64_t)0x3fffffffffU) << (uint32_t)13U;
  output[2U] = u64s[1U] >> (uint32_t)38U | (u64s[2U] & (uint64_t)0x1ffffffU) << (uint32_t)26U;
  output[3U] = u64s[2U] >> (uint32_t)25U | (u64s[3U] & (uint64_t)0xfffU) << (uint32_t)39U;
  output[4U] = u64s[3U] >> (uint32_t)12U;
}

void Hacl_Bignum25519_store_51(uint8_t *output, uint64_t *input)
{
  uint64_t u64s[4U] = { 0U };
  Hacl_Impl_Curve25519_Field51_store_felem(u64s, input);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store64_le(output + i * (uint32_t)8U, u64s[i]);
  }
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
  fdifference(tmp1, y1);
  fdifference(tmp20, y2);
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
  fdifference(tmp10, tmp41);
  fdifference(tmp60, tmp50);
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

static inline void point_double(uint64_t *out, uint64_t *p)
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
  fdifference(tmp61, tmp51);
  fdifference(tmp21, tmp110);
  Hacl_Bignum25519_reduce_513(tmp21);
  Hacl_Bignum25519_reduce_513(tmp41);
  fsum(tmp41, tmp21);
  fmul0(x3, tmp4, tmp6);
  fmul0(y3, tmp2, tmp3);
  fmul0(t3, tmp6, tmp3);
  fmul0(z3, tmp4, tmp2);
}

static inline void
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

static inline void
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

static inline void swap_conditional_inplace(uint64_t *a, uint64_t *b, uint64_t iswap)
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

static inline void point_mul_g(uint64_t *result, uint8_t *scalar)
{
  uint64_t g[20U] = { 0U };
  uint64_t *gx = g;
  uint64_t *gy = g + (uint32_t)5U;
  uint64_t *gz = g + (uint32_t)10U;
  uint64_t *gt = g + (uint32_t)15U;
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
  gt[0U] = (uint64_t)0x00068ab3a5b7dda3U;
  gt[1U] = (uint64_t)0x00000eea2a5eadbbU;
  gt[2U] = (uint64_t)0x0002af8df483c27eU;
  gt[3U] = (uint64_t)0x000332b375274732U;
  gt[4U] = (uint64_t)0x00067875f0fd78b7U;
  Hacl_Impl_Ed25519_Ladder_point_mul(result, scalar, g);
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

static inline void secret_expand(uint8_t *expanded, uint8_t *secret)
{
  Hacl_Hash_SHA2_hash_512(secret, (uint32_t)32U, expanded);
  uint8_t *h_low = expanded;
  uint8_t h_low0 = h_low[0U];
  uint8_t h_low31 = h_low[31U];
  h_low[0U] = h_low0 & (uint8_t)0xf8U;
  h_low[31U] = (h_low31 & (uint8_t)127U) | (uint8_t)64U;
}

static inline void secret_to_public(uint8_t *out, uint8_t *secret)
{
  uint8_t expanded_secret[64U] = { 0U };
  uint64_t res[20U] = { 0U };
  secret_expand(expanded_secret, secret);
  uint8_t *a = expanded_secret;
  point_mul_g(res, a);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, res);
}

static inline void make_q(uint64_t *q)
{
  q[0U] = (uint64_t)0x5812631a5cf5d3edU;
  q[1U] = (uint64_t)0x14def9dea2f79cd6U;
  q[2U] = (uint64_t)0x0U;
  q[3U] = (uint64_t)0x1000000000000000U;
}

static inline void make_r2_modq(uint64_t *r2)
{
  r2[0U] = (uint64_t)0xa40611e3449c0f01U;
  r2[1U] = (uint64_t)0xd00e1ba768859347U;
  r2[2U] = (uint64_t)0xceec73d217f5be65U;
  r2[3U] = (uint64_t)0x399411b7c309a3dU;
}

static inline void modq(uint64_t *a, uint64_t *res)
{
  uint64_t q[4U] = { 0U };
  make_q(q);
  uint64_t mu = (uint64_t)0xd2b51da312547e1bU;
  uint64_t r2[4U] = { 0U };
  make_r2_modq(r2);
  uint64_t a_mod[4U] = { 0U };
  uint64_t a1[8U] = { 0U };
  memcpy(a1, a, (uint32_t)8U * sizeof (uint64_t));
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t qj = mu * a1[i0];
    uint64_t *res_j0 = a1 + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = q[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j0 + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i0);
      uint64_t a_i0 = q[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j0 + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c, res_i1);
      uint64_t a_i1 = q[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j0 + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c, res_i2);
      uint64_t a_i2 = q[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j0 + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = q[i];
      uint64_t *res_i = res_j0 + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c, res_i);
    }
    uint64_t r = c;
    uint64_t c1 = r;
    uint64_t *resb = a1 + (uint32_t)4U + i0;
    uint64_t res_j = a1[(uint32_t)4U + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c1, res_j, resb);
  }
  memcpy(a_mod, a1 + (uint32_t)4U, (uint32_t)4U * sizeof (uint64_t));
  uint64_t c00 = c0;
  uint64_t tmp0[4U] = { 0U };
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64((uint32_t)4U, a_mod, q, tmp0);
  uint64_t m = (uint64_t)0U - c00;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = a_mod;
    uint64_t x = (m & tmp0[i]) | (~m & a_mod[i]);
    os[i] = x;
  }
  uint64_t c[8U] = { 0U };
  uint64_t tmp[16U] = { 0U };
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64((uint32_t)4U, a_mod, r2, tmp, c);
  Hacl_Bignum_Montgomery_bn_mont_reduction_u64((uint32_t)4U, q, mu, c, res);
}

static inline void mul_add_modq(uint64_t *a, uint64_t *b, uint64_t *c, uint64_t *res)
{
  uint64_t tmp[8U] = { 0U };
  uint32_t resLen = (uint32_t)8U;
  memset(tmp, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t bj = b[i0];
    uint64_t *res_j = tmp + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = a[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i0);
      uint64_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c1, res_i1);
      uint64_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c1, res_i2);
      uint64_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c1, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = a[i];
      uint64_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i);
    }
    uint64_t r = c1;
    tmp[(uint32_t)4U + i0] = r;
  }
  uint64_t *a0 = tmp;
  uint64_t *res0 = tmp;
  uint64_t c10 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a0[(uint32_t)4U * i];
    uint64_t t20 = c[(uint32_t)4U * i];
    uint64_t *res_i0 = res0 + (uint32_t)4U * i;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t20, res_i0);
    uint64_t t10 = a0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = c[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res0 + (uint32_t)4U * i + (uint32_t)1U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t10, t21, res_i1);
    uint64_t t11 = a0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = c[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res0 + (uint32_t)4U * i + (uint32_t)2U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t11, t22, res_i2);
    uint64_t t12 = a0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = c[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res0 + (uint32_t)4U * i + (uint32_t)3U;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a0[i];
    uint64_t t2 = c[i];
    uint64_t *res_i = res0 + i;
    c10 = Lib_IntTypes_Intrinsics_add_carry_u64(c10, t1, t2, res_i);
  }
  uint64_t c0 = c10;
  uint64_t c11;
  if ((uint32_t)4U < (uint32_t)8U)
  {
    uint32_t rLen = (uint32_t)4U;
    uint64_t *a1 = tmp + (uint32_t)4U;
    uint64_t *res1 = tmp + (uint32_t)4U;
    uint64_t c1 = c0;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, (uint64_t)0U, res_i);
    }
    uint64_t c12 = c1;
    c11 = c12;
  }
  else
  {
    c11 = c0;
  }
  modq(tmp, res);
}

static inline void sha512_pre_msg(uint8_t *h, uint8_t *prefix, uint32_t len, uint8_t *input)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)32U);
  uint8_t pre_msg[len + (uint32_t)32U];
  memset(pre_msg, 0U, (len + (uint32_t)32U) * sizeof (uint8_t));
  memcpy(pre_msg, prefix, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pre_msg + (uint32_t)32U, input, len * sizeof (uint8_t));
  Hacl_Hash_SHA2_hash_512(pre_msg, len + (uint32_t)32U, h);
}

static inline void
sha512_pre_pre2_msg(
  uint8_t *h,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint32_t len,
  uint8_t *input
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)64U);
  uint8_t pre_msg[len + (uint32_t)64U];
  memset(pre_msg, 0U, (len + (uint32_t)64U) * sizeof (uint8_t));
  memcpy(pre_msg, prefix, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pre_msg + (uint32_t)32U, prefix2, (uint32_t)32U * sizeof (uint8_t));
  memcpy(pre_msg + (uint32_t)64U, input, len * sizeof (uint8_t));
  Hacl_Hash_SHA2_hash_512(pre_msg, len + (uint32_t)64U, h);
}

static inline void
sha512_modq_pre(uint64_t *out, uint8_t *prefix, uint32_t len, uint8_t *input)
{
  uint64_t tmp[8U] = { 0U };
  uint8_t hash[64U] = { 0U };
  sha512_pre_msg(hash, prefix, len, input);
  Hacl_Bignum_Convert_bn_from_bytes_le_uint64((uint32_t)64U, hash, tmp);
  modq(tmp, out);
}

static inline void
sha512_modq_pre_pre2(
  uint64_t *out,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint32_t len,
  uint8_t *input
)
{
  uint64_t tmp[8U] = { 0U };
  uint8_t hash[64U] = { 0U };
  sha512_pre_pre2_msg(hash, prefix, prefix2, len, input);
  Hacl_Bignum_Convert_bn_from_bytes_le_uint64((uint32_t)64U, hash, tmp);
  modq(tmp, out);
}

static inline void point_mul_g_compress(uint8_t *out, uint8_t *s)
{
  uint64_t tmp[20U] = { 0U };
  point_mul_g(tmp, s);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, tmp);
}

static inline void sign_expanded(uint8_t *signature, uint8_t *ks, uint32_t msg, uint8_t *len)
{
  uint8_t tmp_bytes[192U] = { 0U };
  uint64_t tmp_ints[16U] = { 0U };
  uint8_t *rs_ = tmp_bytes + (uint32_t)64U;
  uint8_t *s_ = tmp_bytes + (uint32_t)96U;
  uint8_t *tmp_public = tmp_bytes;
  uint8_t *tmp_xsecret = tmp_bytes + (uint32_t)128U;
  memcpy(tmp_public, ks, (uint32_t)32U * sizeof (uint8_t));
  memcpy(tmp_xsecret, ks + (uint32_t)32U, (uint32_t)64U * sizeof (uint8_t));
  uint64_t *r0 = tmp_ints;
  uint8_t *prefix = tmp_bytes + (uint32_t)160U;
  sha512_modq_pre(r0, prefix, msg, len);
  uint8_t rb[32U] = { 0U };
  uint64_t *r = tmp_ints;
  uint8_t *rs_1 = tmp_bytes + (uint32_t)64U;
  Hacl_Bignum_Convert_bn_to_bytes_le_uint64((uint32_t)32U, r, rb);
  point_mul_g_compress(rs_1, rb);
  uint64_t *h0 = tmp_ints + (uint32_t)12U;
  uint8_t *a__ = tmp_bytes;
  uint8_t *rs_10 = tmp_bytes + (uint32_t)64U;
  sha512_modq_pre_pre2(h0, rs_10, a__, msg, len);
  uint64_t *r1 = tmp_ints;
  uint64_t *aq = tmp_ints + (uint32_t)4U;
  uint64_t *s = tmp_ints + (uint32_t)8U;
  uint64_t *h = tmp_ints + (uint32_t)12U;
  uint8_t *s_1 = tmp_bytes + (uint32_t)96U;
  uint8_t *a = tmp_bytes + (uint32_t)128U;
  Hacl_Bignum_Convert_bn_from_bytes_le_uint64((uint32_t)32U, a, aq);
  mul_add_modq(h, aq, r1, s);
  Hacl_Bignum_Convert_bn_to_bytes_le_uint64((uint32_t)32U, s, s_1);
  memcpy(signature, rs_, (uint32_t)32U * sizeof (uint8_t));
  memcpy(signature + (uint32_t)32U, s_, (uint32_t)32U * sizeof (uint8_t));
}

static inline void pow2_252m2(uint64_t *out, uint64_t *z)
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

static inline bool is_0(uint64_t *x)
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

static inline void mul_modp_sqrt_m1(uint64_t *x)
{
  uint64_t sqrt_m1[5U] = { 0U };
  sqrt_m1[0U] = (uint64_t)0x00061b274a0ea0b0U;
  sqrt_m1[1U] = (uint64_t)0x0000d5a5fc8f189dU;
  sqrt_m1[2U] = (uint64_t)0x0007ef5e9cbd0c60U;
  sqrt_m1[3U] = (uint64_t)0x00078595a6804c9eU;
  sqrt_m1[4U] = (uint64_t)0x0002b8324804fc1dU;
  fmul0(x, x, sqrt_m1);
}

static inline bool recover_x(uint64_t *x, uint64_t *y, uint64_t sign)
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
    fdifference(one, y2);
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
      fdifference(t10, t00);
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
      fdifference(t1, t01);
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
          fdifference(x32, t0);
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

static inline bool gte_q(uint64_t *s)
{
  uint64_t q[4U] = { 0U };
  make_q(q);
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(s[i], q[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(s[i], q[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t b = acc;
  return b == (uint64_t)0U;
}

static inline bool eq(uint64_t *a, uint64_t *b)
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

bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q)
{
  uint64_t tmp[20U] = { 0U };
  uint64_t *pxqz = tmp;
  uint64_t *qxpz = tmp + (uint32_t)5U;
  fmul0(pxqz, p, q + (uint32_t)10U);
  reduce(pxqz);
  fmul0(qxpz, q, p + (uint32_t)10U);
  reduce(qxpz);
  bool b = eq(pxqz, qxpz);
  if (b)
  {
    uint64_t *pyqz = tmp + (uint32_t)10U;
    uint64_t *qypz = tmp + (uint32_t)15U;
    fmul0(pyqz, p + (uint32_t)5U, q + (uint32_t)10U);
    reduce(pyqz);
    fmul0(qypz, q + (uint32_t)5U, p + (uint32_t)10U);
    reduce(qypz);
    return eq(pyqz, qypz);
  }
  return false;
}

void Hacl_Impl_Ed25519_PointNegate_point_negate(uint64_t *p, uint64_t *out)
{
  uint64_t zero[5U] = { 0U };
  zero[0U] = (uint64_t)0U;
  zero[1U] = (uint64_t)0U;
  zero[2U] = (uint64_t)0U;
  zero[3U] = (uint64_t)0U;
  zero[4U] = (uint64_t)0U;
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)5U;
  uint64_t *z = p + (uint32_t)10U;
  uint64_t *t = p + (uint32_t)15U;
  uint64_t *x1 = out;
  uint64_t *y1 = out + (uint32_t)5U;
  uint64_t *z1 = out + (uint32_t)10U;
  uint64_t *t1 = out + (uint32_t)15U;
  memcpy(x1, x, (uint32_t)5U * sizeof (uint64_t));
  fdifference(x1, zero);
  Hacl_Bignum25519_reduce_513(x1);
  memcpy(y1, y, (uint32_t)5U * sizeof (uint64_t));
  memcpy(z1, z, (uint32_t)5U * sizeof (uint64_t));
  memcpy(t1, t, (uint32_t)5U * sizeof (uint64_t));
  fdifference(t1, zero);
  Hacl_Bignum25519_reduce_513(t1);
}

void Hacl_Ed25519_sign(uint8_t *signature, uint8_t *priv, uint32_t len, uint8_t *msg)
{
  uint8_t ks[96U] = { 0U };
  secret_expand(ks + (uint32_t)32U, priv);
  secret_to_public(ks, priv);
  sign_expanded(signature, ks, len, msg);
}

bool Hacl_Ed25519_verify(uint8_t *pub, uint32_t len, uint8_t *msg, uint8_t *signature)
{
  uint64_t tmp[44U] = { 0U };
  uint8_t tmp_[32U] = { 0U };
  uint64_t *a_ = tmp;
  uint64_t *r_ = tmp + (uint32_t)20U;
  bool b = Hacl_Impl_Ed25519_PointDecompress_point_decompress(a_, pub);
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
      Hacl_Bignum_Convert_bn_from_bytes_le_uint64((uint32_t)32U, signature + (uint32_t)32U, s1);
      bool b__ = gte_q(s1);
      if (b__)
      {
        res = false;
      }
      else
      {
        uint64_t r_2[4U] = { 0U };
        sha512_modq_pre_pre2(r_2, rs1, pub, len, msg);
        Hacl_Bignum_Convert_bn_to_bytes_le_uint64((uint32_t)32U, r_2, tmp_);
        uint8_t *uu____0 = signature + (uint32_t)32U;
        uint64_t tmp1[60U] = { 0U };
        uint64_t *hA = tmp1;
        uint64_t *rhA = tmp1 + (uint32_t)20U;
        uint64_t *sB = tmp1 + (uint32_t)40U;
        point_mul_g(sB, uu____0);
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

void Hacl_Ed25519_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  secret_to_public(pub, priv);
}

void Hacl_Ed25519_expand_keys(uint8_t *ks, uint8_t *priv)
{
  secret_expand(ks + (uint32_t)32U, priv);
  secret_to_public(ks, priv);
}

void Hacl_Ed25519_sign_expanded(uint8_t *signature, uint8_t *ks, uint32_t len, uint8_t *msg)
{
  sign_expanded(signature, ks, len, msg);
}

