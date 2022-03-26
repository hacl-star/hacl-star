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


#include "internal/Hacl_Ed25519.h"

#include "internal/Hacl_Kremlib.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Curve25519_51.h"

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

void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *result, uint8_t *scalar, uint64_t *q)
{
  uint64_t bscalar[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = bscalar;
    uint8_t *bj = scalar + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t *x0 = result;
  uint64_t *y = result + (uint32_t)5U;
  uint64_t *z = result + (uint32_t)10U;
  uint64_t *t = result + (uint32_t)15U;
  x0[0U] = (uint64_t)0U;
  x0[1U] = (uint64_t)0U;
  x0[2U] = (uint64_t)0U;
  x0[3U] = (uint64_t)0U;
  x0[4U] = (uint64_t)0U;
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
  uint64_t table[320U] = { 0U };
  memcpy(table, result, (uint32_t)20U * sizeof (uint64_t));
  uint64_t *t1 = table + (uint32_t)20U;
  memcpy(t1, q, (uint32_t)20U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)14U; i++)
  {
    uint64_t *t11 = table + (i + (uint32_t)1U) * (uint32_t)20U;
    uint64_t *t2 = table + (i + (uint32_t)2U) * (uint32_t)20U;
    Hacl_Impl_Ed25519_PointAdd_point_add(t2, t11, q);
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      point_double(result, result);
    }
    uint32_t bk = (uint32_t)256U;
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
    uint32_t i1 = (bk - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bk - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = bscalar[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | bscalar[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l = ite & mask_l;
    uint64_t a_bits_l[20U] = { 0U };
    memcpy(a_bits_l, table, (uint32_t)20U * sizeof (uint64_t));
    for (uint32_t i2 = (uint32_t)0U; i2 < (uint32_t)15U; i2++)
    {
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
      uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)20U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)20U; i++)
      {
        uint64_t *os = a_bits_l;
        uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
        os[i] = x;
      }
    }
    Hacl_Impl_Ed25519_PointAdd_point_add(result, result, a_bits_l);
  }
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

static inline void
point_mul_double_vartime(
  uint64_t *result,
  uint8_t *scalar1,
  uint64_t *q1,
  uint8_t *scalar2,
  uint64_t *q2
)
{
  uint64_t bscalar1[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = bscalar1;
    uint8_t *bj = scalar1 + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t bscalar2[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = bscalar2;
    uint8_t *bj = scalar2 + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t *x = result;
  uint64_t *y = result + (uint32_t)5U;
  uint64_t *z = result + (uint32_t)10U;
  uint64_t *t = result + (uint32_t)15U;
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
  uint64_t table1[320U] = { 0U };
  memcpy(table1, result, (uint32_t)20U * sizeof (uint64_t));
  uint64_t *t10 = table1 + (uint32_t)20U;
  memcpy(t10, q1, (uint32_t)20U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)14U; i++)
  {
    uint64_t *t11 = table1 + (i + (uint32_t)1U) * (uint32_t)20U;
    uint64_t *t2 = table1 + (i + (uint32_t)2U) * (uint32_t)20U;
    Hacl_Impl_Ed25519_PointAdd_point_add(t2, t11, q1);
  }
  uint64_t table2[320U] = { 0U };
  memcpy(table2, result, (uint32_t)20U * sizeof (uint64_t));
  uint64_t *t1 = table2 + (uint32_t)20U;
  memcpy(t1, q2, (uint32_t)20U * sizeof (uint64_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)14U; i++)
  {
    uint64_t *t11 = table2 + (i + (uint32_t)1U) * (uint32_t)20U;
    uint64_t *t2 = table2 + (i + (uint32_t)2U) * (uint32_t)20U;
    Hacl_Impl_Ed25519_PointAdd_point_add(t2, t11, q2);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      point_double(result, result);
    }
    uint32_t bk = (uint32_t)256U;
    uint64_t mask_l0 = (uint64_t)16U - (uint64_t)1U;
    uint32_t i10 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j0 = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p10 = bscalar1[i10] >> j0;
    uint64_t ite0;
    if (i10 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
    {
      ite0 = p10 | bscalar1[i10 + (uint32_t)1U] << ((uint32_t)64U - j0);
    }
    else
    {
      ite0 = p10;
    }
    uint64_t bits_l = ite0 & mask_l0;
    uint64_t a_bits_l0[20U] = { 0U };
    uint32_t bits_l320 = (uint32_t)bits_l;
    uint64_t *a_bits_l1 = table1 + bits_l320 * (uint32_t)20U;
    memcpy(a_bits_l0, a_bits_l1, (uint32_t)20U * sizeof (uint64_t));
    Hacl_Impl_Ed25519_PointAdd_point_add(result, result, a_bits_l0);
    uint32_t bk0 = (uint32_t)256U;
    uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
    uint32_t i1 = (bk0 - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
    uint32_t j = (bk0 - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
    uint64_t p1 = bscalar2[i1] >> j;
    uint64_t ite;
    if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
    {
      ite = p1 | bscalar2[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
    }
    else
    {
      ite = p1;
    }
    uint64_t bits_l0 = ite & mask_l;
    uint64_t a_bits_l[20U] = { 0U };
    uint32_t bits_l32 = (uint32_t)bits_l0;
    uint64_t *a_bits_l10 = table2 + bits_l32 * (uint32_t)20U;
    memcpy(a_bits_l, a_bits_l10, (uint32_t)20U * sizeof (uint64_t));
    Hacl_Impl_Ed25519_PointAdd_point_add(result, result, a_bits_l);
  }
}

static inline void
point_mul_g_double_vartime(uint64_t *result, uint8_t *scalar1, uint8_t *scalar2, uint64_t *q2)
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
  point_mul_double_vartime(result, scalar1, g, scalar2, q2);
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

static inline void barrett_reduction(uint64_t *z, uint64_t *t)
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
  FStar_UInt128_uint128 xy000 = FStar_UInt128_mul_wide(q0, mu0);
  FStar_UInt128_uint128 xy010 = FStar_UInt128_mul_wide(q0, mu1);
  FStar_UInt128_uint128 xy020 = FStar_UInt128_mul_wide(q0, mu2);
  FStar_UInt128_uint128 xy030 = FStar_UInt128_mul_wide(q0, mu3);
  FStar_UInt128_uint128 xy040 = FStar_UInt128_mul_wide(q0, mu4);
  FStar_UInt128_uint128 xy100 = FStar_UInt128_mul_wide(q1, mu0);
  FStar_UInt128_uint128 xy110 = FStar_UInt128_mul_wide(q1, mu1);
  FStar_UInt128_uint128 xy120 = FStar_UInt128_mul_wide(q1, mu2);
  FStar_UInt128_uint128 xy130 = FStar_UInt128_mul_wide(q1, mu3);
  FStar_UInt128_uint128 xy14 = FStar_UInt128_mul_wide(q1, mu4);
  FStar_UInt128_uint128 xy200 = FStar_UInt128_mul_wide(q2, mu0);
  FStar_UInt128_uint128 xy210 = FStar_UInt128_mul_wide(q2, mu1);
  FStar_UInt128_uint128 xy220 = FStar_UInt128_mul_wide(q2, mu2);
  FStar_UInt128_uint128 xy23 = FStar_UInt128_mul_wide(q2, mu3);
  FStar_UInt128_uint128 xy24 = FStar_UInt128_mul_wide(q2, mu4);
  FStar_UInt128_uint128 xy300 = FStar_UInt128_mul_wide(q3, mu0);
  FStar_UInt128_uint128 xy310 = FStar_UInt128_mul_wide(q3, mu1);
  FStar_UInt128_uint128 xy32 = FStar_UInt128_mul_wide(q3, mu2);
  FStar_UInt128_uint128 xy33 = FStar_UInt128_mul_wide(q3, mu3);
  FStar_UInt128_uint128 xy34 = FStar_UInt128_mul_wide(q3, mu4);
  FStar_UInt128_uint128 xy400 = FStar_UInt128_mul_wide(q4, mu0);
  FStar_UInt128_uint128 xy41 = FStar_UInt128_mul_wide(q4, mu1);
  FStar_UInt128_uint128 xy42 = FStar_UInt128_mul_wide(q4, mu2);
  FStar_UInt128_uint128 xy43 = FStar_UInt128_mul_wide(q4, mu3);
  FStar_UInt128_uint128 xy44 = FStar_UInt128_mul_wide(q4, mu4);
  FStar_UInt128_uint128 z01 = xy000;
  FStar_UInt128_uint128 z11 = FStar_UInt128_add_mod(xy010, xy100);
  FStar_UInt128_uint128 z21 = FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy020, xy110), xy200);
  FStar_UInt128_uint128
  z31 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy030, xy120), xy210),
      xy300);
  FStar_UInt128_uint128
  z41 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy040,
            xy130),
          xy220),
        xy310),
      xy400);
  FStar_UInt128_uint128
  z5 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy14, xy23), xy32),
      xy41);
  FStar_UInt128_uint128 z6 = FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy24, xy33), xy42);
  FStar_UInt128_uint128 z7 = FStar_UInt128_add_mod(xy34, xy43);
  FStar_UInt128_uint128 z8 = xy44;
  FStar_UInt128_uint128 carry0 = FStar_UInt128_shift_right(z01, (uint32_t)56U);
  FStar_UInt128_uint128 c00 = carry0;
  FStar_UInt128_uint128
  carry1 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z11, c00), (uint32_t)56U);
  uint64_t
  t100 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z11, c00))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c10 = carry1;
  FStar_UInt128_uint128
  carry2 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z21, c10), (uint32_t)56U);
  uint64_t
  t101 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z21, c10))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c20 = carry2;
  FStar_UInt128_uint128
  carry3 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z31, c20), (uint32_t)56U);
  uint64_t
  t102 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z31, c20))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c30 = carry3;
  FStar_UInt128_uint128
  carry4 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z41, c30), (uint32_t)56U);
  uint64_t
  t103 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z41, c30))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c40 = carry4;
  uint64_t t410 = t103;
  FStar_UInt128_uint128
  carry5 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z5, c40), (uint32_t)56U);
  uint64_t
  t104 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z5, c40))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c5 = carry5;
  uint64_t t51 = t104;
  FStar_UInt128_uint128
  carry6 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z6, c5), (uint32_t)56U);
  uint64_t
  t105 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z6, c5))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c6 = carry6;
  uint64_t t61 = t105;
  FStar_UInt128_uint128
  carry7 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z7, c6), (uint32_t)56U);
  uint64_t
  t106 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z7, c6))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c7 = carry7;
  uint64_t t71 = t106;
  FStar_UInt128_uint128
  carry8 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z8, c7), (uint32_t)56U);
  uint64_t
  t107 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z8, c7))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c8 = carry8;
  uint64_t t81 = t107;
  uint64_t t91 = FStar_UInt128_uint128_to_uint64(c8);
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
  FStar_UInt128_uint128 xy00 = FStar_UInt128_mul_wide(qdiv0, m0);
  FStar_UInt128_uint128 xy01 = FStar_UInt128_mul_wide(qdiv0, m1);
  FStar_UInt128_uint128 xy02 = FStar_UInt128_mul_wide(qdiv0, m2);
  FStar_UInt128_uint128 xy03 = FStar_UInt128_mul_wide(qdiv0, m3);
  FStar_UInt128_uint128 xy04 = FStar_UInt128_mul_wide(qdiv0, m4);
  FStar_UInt128_uint128 xy10 = FStar_UInt128_mul_wide(qdiv1, m0);
  FStar_UInt128_uint128 xy11 = FStar_UInt128_mul_wide(qdiv1, m1);
  FStar_UInt128_uint128 xy12 = FStar_UInt128_mul_wide(qdiv1, m2);
  FStar_UInt128_uint128 xy13 = FStar_UInt128_mul_wide(qdiv1, m3);
  FStar_UInt128_uint128 xy20 = FStar_UInt128_mul_wide(qdiv2, m0);
  FStar_UInt128_uint128 xy21 = FStar_UInt128_mul_wide(qdiv2, m1);
  FStar_UInt128_uint128 xy22 = FStar_UInt128_mul_wide(qdiv2, m2);
  FStar_UInt128_uint128 xy30 = FStar_UInt128_mul_wide(qdiv3, m0);
  FStar_UInt128_uint128 xy31 = FStar_UInt128_mul_wide(qdiv3, m1);
  FStar_UInt128_uint128 xy40 = FStar_UInt128_mul_wide(qdiv4, m0);
  FStar_UInt128_uint128 carry9 = FStar_UInt128_shift_right(xy00, (uint32_t)56U);
  uint64_t t108 = FStar_UInt128_uint128_to_uint64(xy00) & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c0 = carry9;
  uint64_t t010 = t108;
  FStar_UInt128_uint128
  carry10 =
    FStar_UInt128_shift_right(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy01, xy10), c0),
      (uint32_t)56U);
  uint64_t
  t109 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy01, xy10), c0))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c11 = carry10;
  uint64_t t110 = t109;
  FStar_UInt128_uint128
  carry11 =
    FStar_UInt128_shift_right(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy02,
            xy11),
          xy20),
        c11),
      (uint32_t)56U);
  uint64_t
  t1010 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy02,
            xy11),
          xy20),
        c11))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c21 = carry11;
  uint64_t t210 = t1010;
  FStar_UInt128_uint128
  carry =
    FStar_UInt128_shift_right(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy03,
              xy12),
            xy21),
          xy30),
        c21),
      (uint32_t)56U);
  uint64_t
  t1011 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy03,
              xy12),
            xy21),
          xy30),
        c21))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c31 = carry;
  uint64_t t310 = t1011;
  uint64_t
  t411 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy04,
                xy13),
              xy22),
            xy31),
          xy40),
        c31))
    & (uint64_t)0xffffffffffU;
  uint64_t qmul0 = t010;
  uint64_t qmul1 = t110;
  uint64_t qmul2 = t210;
  uint64_t qmul3 = t310;
  uint64_t qmul4 = t411;
  uint64_t b5 = (r0 - qmul0) >> (uint32_t)63U;
  uint64_t t1012 = (b5 << (uint32_t)56U) + r0 - qmul0;
  uint64_t c1 = b5;
  uint64_t t011 = t1012;
  uint64_t b6 = (r1 - (qmul1 + c1)) >> (uint32_t)63U;
  uint64_t t1013 = (b6 << (uint32_t)56U) + r1 - (qmul1 + c1);
  uint64_t c2 = b6;
  uint64_t t111 = t1013;
  uint64_t b7 = (r2 - (qmul2 + c2)) >> (uint32_t)63U;
  uint64_t t1014 = (b7 << (uint32_t)56U) + r2 - (qmul2 + c2);
  uint64_t c3 = b7;
  uint64_t t211 = t1014;
  uint64_t b8 = (r3 - (qmul3 + c3)) >> (uint32_t)63U;
  uint64_t t1015 = (b8 << (uint32_t)56U) + r3 - (qmul3 + c3);
  uint64_t c4 = b8;
  uint64_t t311 = t1015;
  uint64_t b9 = (r4 - (qmul4 + c4)) >> (uint32_t)63U;
  uint64_t t1016 = (b9 << (uint32_t)40U) + r4 - (qmul4 + c4);
  uint64_t t412 = t1016;
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
  uint64_t t1017 = (b10 << (uint32_t)56U) + s0 - y0;
  uint64_t b0 = b10;
  uint64_t t01 = t1017;
  uint64_t b11 = (s1 - (y1 + b0)) >> (uint32_t)63U;
  uint64_t t1018 = (b11 << (uint32_t)56U) + s1 - (y1 + b0);
  uint64_t b1 = b11;
  uint64_t t11 = t1018;
  uint64_t b12 = (s2 - (y2 + b1)) >> (uint32_t)63U;
  uint64_t t1019 = (b12 << (uint32_t)56U) + s2 - (y2 + b1);
  uint64_t b2 = b12;
  uint64_t t21 = t1019;
  uint64_t b13 = (s3 - (y3 + b2)) >> (uint32_t)63U;
  uint64_t t1020 = (b13 << (uint32_t)56U) + s3 - (y3 + b2);
  uint64_t b3 = b13;
  uint64_t t31 = t1020;
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

static inline void mul_modq(uint64_t *out, uint64_t *x, uint64_t *y)
{
  uint64_t tmp[10U] = { 0U };
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
  FStar_UInt128_uint128 xy00 = FStar_UInt128_mul_wide(x0, y0);
  FStar_UInt128_uint128 xy01 = FStar_UInt128_mul_wide(x0, y1);
  FStar_UInt128_uint128 xy02 = FStar_UInt128_mul_wide(x0, y2);
  FStar_UInt128_uint128 xy03 = FStar_UInt128_mul_wide(x0, y3);
  FStar_UInt128_uint128 xy04 = FStar_UInt128_mul_wide(x0, y4);
  FStar_UInt128_uint128 xy10 = FStar_UInt128_mul_wide(x1, y0);
  FStar_UInt128_uint128 xy11 = FStar_UInt128_mul_wide(x1, y1);
  FStar_UInt128_uint128 xy12 = FStar_UInt128_mul_wide(x1, y2);
  FStar_UInt128_uint128 xy13 = FStar_UInt128_mul_wide(x1, y3);
  FStar_UInt128_uint128 xy14 = FStar_UInt128_mul_wide(x1, y4);
  FStar_UInt128_uint128 xy20 = FStar_UInt128_mul_wide(x2, y0);
  FStar_UInt128_uint128 xy21 = FStar_UInt128_mul_wide(x2, y1);
  FStar_UInt128_uint128 xy22 = FStar_UInt128_mul_wide(x2, y2);
  FStar_UInt128_uint128 xy23 = FStar_UInt128_mul_wide(x2, y3);
  FStar_UInt128_uint128 xy24 = FStar_UInt128_mul_wide(x2, y4);
  FStar_UInt128_uint128 xy30 = FStar_UInt128_mul_wide(x3, y0);
  FStar_UInt128_uint128 xy31 = FStar_UInt128_mul_wide(x3, y1);
  FStar_UInt128_uint128 xy32 = FStar_UInt128_mul_wide(x3, y2);
  FStar_UInt128_uint128 xy33 = FStar_UInt128_mul_wide(x3, y3);
  FStar_UInt128_uint128 xy34 = FStar_UInt128_mul_wide(x3, y4);
  FStar_UInt128_uint128 xy40 = FStar_UInt128_mul_wide(x4, y0);
  FStar_UInt128_uint128 xy41 = FStar_UInt128_mul_wide(x4, y1);
  FStar_UInt128_uint128 xy42 = FStar_UInt128_mul_wide(x4, y2);
  FStar_UInt128_uint128 xy43 = FStar_UInt128_mul_wide(x4, y3);
  FStar_UInt128_uint128 xy44 = FStar_UInt128_mul_wide(x4, y4);
  FStar_UInt128_uint128 z00 = xy00;
  FStar_UInt128_uint128 z10 = FStar_UInt128_add_mod(xy01, xy10);
  FStar_UInt128_uint128 z20 = FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy02, xy11), xy20);
  FStar_UInt128_uint128
  z30 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy03, xy12), xy21),
      xy30);
  FStar_UInt128_uint128
  z40 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy04,
            xy13),
          xy22),
        xy31),
      xy40);
  FStar_UInt128_uint128
  z50 =
    FStar_UInt128_add_mod(FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy14, xy23), xy32),
      xy41);
  FStar_UInt128_uint128 z60 = FStar_UInt128_add_mod(FStar_UInt128_add_mod(xy24, xy33), xy42);
  FStar_UInt128_uint128 z70 = FStar_UInt128_add_mod(xy34, xy43);
  FStar_UInt128_uint128 z80 = xy44;
  FStar_UInt128_uint128 carry0 = FStar_UInt128_shift_right(z00, (uint32_t)56U);
  uint64_t t10 = FStar_UInt128_uint128_to_uint64(z00) & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c0 = carry0;
  uint64_t t0 = t10;
  FStar_UInt128_uint128
  carry1 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z10, c0), (uint32_t)56U);
  uint64_t
  t11 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z10, c0))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c1 = carry1;
  uint64_t t1 = t11;
  FStar_UInt128_uint128
  carry2 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z20, c1), (uint32_t)56U);
  uint64_t
  t12 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z20, c1))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c2 = carry2;
  uint64_t t2 = t12;
  FStar_UInt128_uint128
  carry3 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z30, c2), (uint32_t)56U);
  uint64_t
  t13 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z30, c2))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c3 = carry3;
  uint64_t t3 = t13;
  FStar_UInt128_uint128
  carry4 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z40, c3), (uint32_t)56U);
  uint64_t
  t14 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z40, c3))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c4 = carry4;
  uint64_t t4 = t14;
  FStar_UInt128_uint128
  carry5 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z50, c4), (uint32_t)56U);
  uint64_t
  t15 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z50, c4))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c5 = carry5;
  uint64_t t5 = t15;
  FStar_UInt128_uint128
  carry6 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z60, c5), (uint32_t)56U);
  uint64_t
  t16 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z60, c5))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c6 = carry6;
  uint64_t t6 = t16;
  FStar_UInt128_uint128
  carry7 = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z70, c6), (uint32_t)56U);
  uint64_t
  t17 =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z70, c6))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c7 = carry7;
  uint64_t t7 = t17;
  FStar_UInt128_uint128
  carry = FStar_UInt128_shift_right(FStar_UInt128_add_mod(z80, c7), (uint32_t)56U);
  uint64_t
  t =
    FStar_UInt128_uint128_to_uint64(FStar_UInt128_add_mod(z80, c7))
    & (uint64_t)0xffffffffffffffU;
  FStar_UInt128_uint128 c8 = carry;
  uint64_t t8 = t;
  uint64_t t9 = FStar_UInt128_uint128_to_uint64(c8);
  uint64_t z0 = t0;
  uint64_t z1 = t1;
  uint64_t z2 = t2;
  uint64_t z3 = t3;
  uint64_t z4 = t4;
  uint64_t z5 = t5;
  uint64_t z6 = t6;
  uint64_t z7 = t7;
  uint64_t z8 = t8;
  uint64_t z9 = t9;
  tmp[0U] = z0;
  tmp[1U] = z1;
  tmp[2U] = z2;
  tmp[3U] = z3;
  tmp[4U] = z4;
  tmp[5U] = z5;
  tmp[6U] = z6;
  tmp[7U] = z7;
  tmp[8U] = z8;
  tmp[9U] = z9;
  barrett_reduction(out, tmp);
}

static inline void add_modq(uint64_t *out, uint64_t *x, uint64_t *y)
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

static inline void load_64_bytes(uint64_t *out, uint8_t *b)
{
  uint8_t *b80 = b;
  uint64_t u = load64_le(b80);
  uint64_t z = u;
  uint64_t b0 = z & (uint64_t)0xffffffffffffffU;
  uint8_t *b81 = b + (uint32_t)7U;
  uint64_t u0 = load64_le(b81);
  uint64_t z0 = u0;
  uint64_t b1 = z0 & (uint64_t)0xffffffffffffffU;
  uint8_t *b82 = b + (uint32_t)14U;
  uint64_t u1 = load64_le(b82);
  uint64_t z1 = u1;
  uint64_t b2 = z1 & (uint64_t)0xffffffffffffffU;
  uint8_t *b83 = b + (uint32_t)21U;
  uint64_t u2 = load64_le(b83);
  uint64_t z2 = u2;
  uint64_t b3 = z2 & (uint64_t)0xffffffffffffffU;
  uint8_t *b84 = b + (uint32_t)28U;
  uint64_t u3 = load64_le(b84);
  uint64_t z3 = u3;
  uint64_t b4 = z3 & (uint64_t)0xffffffffffffffU;
  uint8_t *b85 = b + (uint32_t)35U;
  uint64_t u4 = load64_le(b85);
  uint64_t z4 = u4;
  uint64_t b5 = z4 & (uint64_t)0xffffffffffffffU;
  uint8_t *b86 = b + (uint32_t)42U;
  uint64_t u5 = load64_le(b86);
  uint64_t z5 = u5;
  uint64_t b6 = z5 & (uint64_t)0xffffffffffffffU;
  uint8_t *b87 = b + (uint32_t)49U;
  uint64_t u6 = load64_le(b87);
  uint64_t z6 = u6;
  uint64_t b7 = z6 & (uint64_t)0xffffffffffffffU;
  uint8_t *b8 = b + (uint32_t)56U;
  uint64_t u7 = load64_le(b8);
  uint64_t z7 = u7;
  uint64_t b88 = z7 & (uint64_t)0xffffffffffffffU;
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
  out[8U] = b88;
  out[9U] = b9;
}

static inline void load_32_bytes(uint64_t *out, uint8_t *b)
{
  uint8_t *b80 = b;
  uint64_t u0 = load64_le(b80);
  uint64_t z = u0;
  uint64_t b0 = z & (uint64_t)0xffffffffffffffU;
  uint8_t *b81 = b + (uint32_t)7U;
  uint64_t u1 = load64_le(b81);
  uint64_t z0 = u1;
  uint64_t b1 = z0 & (uint64_t)0xffffffffffffffU;
  uint8_t *b82 = b + (uint32_t)14U;
  uint64_t u2 = load64_le(b82);
  uint64_t z1 = u2;
  uint64_t b2 = z1 & (uint64_t)0xffffffffffffffU;
  uint8_t *b8 = b + (uint32_t)21U;
  uint64_t u3 = load64_le(b8);
  uint64_t z2 = u3;
  uint64_t b3 = z2 & (uint64_t)0xffffffffffffffU;
  uint32_t u = load32_le(b + (uint32_t)28U);
  uint32_t b4 = u;
  uint64_t b41 = (uint64_t)b4;
  out[0U] = b0;
  out[1U] = b1;
  out[2U] = b2;
  out[3U] = b3;
  out[4U] = b41;
}

static inline void store_56(uint8_t *out, uint64_t *b)
{
  uint64_t b0 = b[0U];
  uint64_t b1 = b[1U];
  uint64_t b2 = b[2U];
  uint64_t b3 = b[3U];
  uint64_t b4 = b[4U];
  uint32_t b4_ = (uint32_t)b4;
  uint8_t *b8 = out;
  store64_le(b8, b0);
  uint8_t *b80 = out + (uint32_t)7U;
  store64_le(b80, b1);
  uint8_t *b81 = out + (uint32_t)14U;
  store64_le(b81, b2);
  uint8_t *b82 = out + (uint32_t)21U;
  store64_le(b82, b3);
  store32_le(out + (uint32_t)28U, b4_);
}

static inline void sha512_pre_msg(uint8_t *hash, uint8_t *prefix, uint32_t len, uint8_t *input)
{
  uint8_t buf[128U] = { 0U };
  uint64_t block_state[8U] = { 0U };
  Hacl_Streaming_SHA2_state_sha2_384
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  Hacl_Streaming_SHA2_state_sha2_384 p = s;
  Hacl_Hash_Core_SHA2_init_512(block_state);
  Hacl_Streaming_SHA2_state_sha2_384 *st = &p;
  Hacl_Streaming_SHA2_update_512(st, prefix, (uint32_t)32U);
  Hacl_Streaming_SHA2_update_512(st, input, len);
  Hacl_Streaming_SHA2_finish_512(st, hash);
}

static inline void
sha512_pre_pre2_msg(
  uint8_t *hash,
  uint8_t *prefix,
  uint8_t *prefix2,
  uint32_t len,
  uint8_t *input
)
{
  uint8_t buf[128U] = { 0U };
  uint64_t block_state[8U] = { 0U };
  Hacl_Streaming_SHA2_state_sha2_384
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  Hacl_Streaming_SHA2_state_sha2_384 p = s;
  Hacl_Hash_Core_SHA2_init_512(block_state);
  Hacl_Streaming_SHA2_state_sha2_384 *st = &p;
  Hacl_Streaming_SHA2_update_512(st, prefix, (uint32_t)32U);
  Hacl_Streaming_SHA2_update_512(st, prefix2, (uint32_t)32U);
  Hacl_Streaming_SHA2_update_512(st, input, len);
  Hacl_Streaming_SHA2_finish_512(st, hash);
}

static inline void
sha512_modq_pre(uint64_t *out, uint8_t *prefix, uint32_t len, uint8_t *input)
{
  uint64_t tmp[10U] = { 0U };
  uint8_t hash[64U] = { 0U };
  sha512_pre_msg(hash, prefix, len, input);
  load_64_bytes(tmp, hash);
  barrett_reduction(out, tmp);
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
  uint64_t tmp[10U] = { 0U };
  uint8_t hash[64U] = { 0U };
  sha512_pre_pre2_msg(hash, prefix, prefix2, len, input);
  load_64_bytes(tmp, hash);
  barrett_reduction(out, tmp);
}

static inline void point_mul_g_compress(uint8_t *out, uint8_t *s)
{
  uint64_t tmp[20U] = { 0U };
  point_mul_g(tmp, s);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, tmp);
}

static inline void sign_expanded(uint8_t *signature, uint8_t *ks, uint32_t msg, uint8_t *len)
{
  uint8_t tmp_bytes[160U] = { 0U };
  uint64_t tmp_ints[25U] = { 0U };
  uint8_t *rs_ = tmp_bytes + (uint32_t)32U;
  uint8_t *s_ = tmp_bytes + (uint32_t)64U;
  uint8_t *tmp_public = tmp_bytes;
  uint8_t *tmp_xsecret = tmp_bytes + (uint32_t)96U;
  memcpy(tmp_public, ks, (uint32_t)32U * sizeof (uint8_t));
  memcpy(tmp_xsecret, ks + (uint32_t)32U, (uint32_t)64U * sizeof (uint8_t));
  uint64_t *r0 = tmp_ints;
  uint8_t *prefix = tmp_bytes + (uint32_t)128U;
  sha512_modq_pre(r0, prefix, msg, len);
  uint8_t *rs_1 = tmp_bytes + (uint32_t)32U;
  uint64_t *r = tmp_ints;
  uint8_t rb[32U] = { 0U };
  store_56(rb, r);
  point_mul_g_compress(rs_1, rb);
  uint64_t *h0 = tmp_ints + (uint32_t)20U;
  uint8_t *a__ = tmp_bytes;
  uint8_t *rs_10 = tmp_bytes + (uint32_t)32U;
  sha512_modq_pre_pre2(h0, rs_10, a__, msg, len);
  uint64_t *r1 = tmp_ints;
  uint64_t *aq = tmp_ints + (uint32_t)5U;
  uint64_t *ha = tmp_ints + (uint32_t)10U;
  uint64_t *s = tmp_ints + (uint32_t)15U;
  uint64_t *h = tmp_ints + (uint32_t)20U;
  uint8_t *s_1 = tmp_bytes + (uint32_t)64U;
  uint8_t *a = tmp_bytes + (uint32_t)96U;
  load_32_bytes(aq, a);
  mul_modq(ha, h, aq);
  add_modq(s, r1, ha);
  store_56(s_1, s);
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
  uint64_t tmp[45U] = { 0U };
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
      uint64_t *s = tmp + (uint32_t)40U;
      load_32_bytes(s, signature + (uint32_t)32U);
      bool b__ = gte_q(s);
      if (b__)
      {
        res = false;
      }
      else
      {
        uint64_t r_2[5U] = { 0U };
        sha512_modq_pre_pre2(r_2, rs1, pub, len, msg);
        store_56(tmp_, r_2);
        uint8_t *uu____0 = signature + (uint32_t)32U;
        uint64_t tmp1[40U] = { 0U };
        uint64_t *a_neg = tmp1;
        uint64_t *exp_d = tmp1 + (uint32_t)20U;
        Hacl_Impl_Ed25519_PointNegate_point_negate(a_1, a_neg);
        point_mul_g_double_vartime(exp_d, uu____0, tmp_, a_neg);
        uint64_t *exp_d0 = tmp1 + (uint32_t)20U;
        bool b1 = Hacl_Impl_Ed25519_PointEqual_point_equal(exp_d0, r_1);
        res = b1;
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

