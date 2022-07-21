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

#include "internal/Hacl_Streaming.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Curve25519_51.h"

static inline void fsum(u64 *a, u64 *b)
{
  Hacl_Impl_Curve25519_Field51_fadd(a, a, b);
}

static inline void fdifference(u64 *a, u64 *b)
{
  Hacl_Impl_Curve25519_Field51_fsub(a, b, a);
}

void Hacl_Bignum25519_reduce_513(u64 *a)
{
  u64 f0 = a[0U];
  u64 f1 = a[1U];
  u64 f2 = a[2U];
  u64 f3 = a[3U];
  u64 f4 = a[4U];
  u64 l_ = f0 + (u64)0U;
  u64 tmp0 = l_ & (u64)0x7ffffffffffffU;
  u64 c0 = l_ >> (u32)51U;
  u64 l_0 = f1 + c0;
  u64 tmp1 = l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = l_0 >> (u32)51U;
  u64 l_1 = f2 + c1;
  u64 tmp2 = l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = l_1 >> (u32)51U;
  u64 l_2 = f3 + c2;
  u64 tmp3 = l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = l_2 >> (u32)51U;
  u64 l_3 = f4 + c3;
  u64 tmp4 = l_3 & (u64)0x7ffffffffffffU;
  u64 c4 = l_3 >> (u32)51U;
  u64 l_4 = tmp0 + c4 * (u64)19U;
  u64 tmp0_ = l_4 & (u64)0x7ffffffffffffU;
  u64 c5 = l_4 >> (u32)51U;
  a[0U] = tmp0_;
  a[1U] = tmp1 + c5;
  a[2U] = tmp2;
  a[3U] = tmp3;
  a[4U] = tmp4;
}

static inline void fmul(u64 *output, u64 *input, u64 *input2)
{
  uint128_t tmp[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Impl_Curve25519_Field51_fmul(output, input, input2, tmp);
}

static inline void times_2(u64 *out, u64 *a)
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

static inline void times_d(u64 *out, u64 *a)
{
  u64 d[5U] = { 0U };
  d[0U] = (u64)0x00034dca135978a3U;
  d[1U] = (u64)0x0001a8283b156ebdU;
  d[2U] = (u64)0x0005e7a26001c029U;
  d[3U] = (u64)0x000739c663a03cbbU;
  d[4U] = (u64)0x00052036cee2b6ffU;
  fmul(out, d, a);
}

static inline void times_2d(u64 *out, u64 *a)
{
  u64 d2[5U] = { 0U };
  d2[0U] = (u64)0x00069b9426b2f159U;
  d2[1U] = (u64)0x00035050762add7aU;
  d2[2U] = (u64)0x0003cf44c0038052U;
  d2[3U] = (u64)0x0006738cc7407977U;
  d2[4U] = (u64)0x0002406d9dc56dffU;
  fmul(out, d2, a);
}

static inline void fsquare(u64 *out, u64 *a)
{
  uint128_t tmp[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp);
}

static inline void fsquare_times(u64 *output, u64 *input, u32 count)
{
  uint128_t tmp[5U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)5U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Curve25519_51_fsquare_times(output, input, tmp, count);
}

static inline void fsquare_times_inplace(u64 *output, u32 count)
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

static inline void reduce(u64 *out)
{
  u64 o0 = out[0U];
  u64 o1 = out[1U];
  u64 o2 = out[2U];
  u64 o3 = out[3U];
  u64 o4 = out[4U];
  u64 l_ = o0 + (u64)0U;
  u64 tmp0 = l_ & (u64)0x7ffffffffffffU;
  u64 c0 = l_ >> (u32)51U;
  u64 l_0 = o1 + c0;
  u64 tmp1 = l_0 & (u64)0x7ffffffffffffU;
  u64 c1 = l_0 >> (u32)51U;
  u64 l_1 = o2 + c1;
  u64 tmp2 = l_1 & (u64)0x7ffffffffffffU;
  u64 c2 = l_1 >> (u32)51U;
  u64 l_2 = o3 + c2;
  u64 tmp3 = l_2 & (u64)0x7ffffffffffffU;
  u64 c3 = l_2 >> (u32)51U;
  u64 l_3 = o4 + c3;
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
  out[0U] = f01;
  out[1U] = f11;
  out[2U] = f21;
  out[3U] = f31;
  out[4U] = f41;
}

void Hacl_Bignum25519_load_51(u64 *output, u8 *input)
{
  u64 u64s[4U] = { 0U };
  u64 u64s3;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = u64s;
      u8 *bj = input + i * (u32)8U;
      u64 u = load64_le(bj);
      u64 r = u;
      u64 x = r;
      os[i] = x;
    }
  }
  u64s3 = u64s[3U];
  u64s[3U] = u64s3 & (u64)0x7fffffffffffffffU;
  output[0U] = u64s[0U] & (u64)0x7ffffffffffffU;
  output[1U] = u64s[0U] >> (u32)51U | (u64s[1U] & (u64)0x3fffffffffU) << (u32)13U;
  output[2U] = u64s[1U] >> (u32)38U | (u64s[2U] & (u64)0x1ffffffU) << (u32)26U;
  output[3U] = u64s[2U] >> (u32)25U | (u64s[3U] & (u64)0xfffU) << (u32)39U;
  output[4U] = u64s[3U] >> (u32)12U;
}

void Hacl_Bignum25519_store_51(u8 *output, u64 *input)
{
  u64 u64s[4U] = { 0U };
  Hacl_Impl_Curve25519_Field51_store_felem(u64s, input);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
      store64_le(output + i * (u32)8U, u64s[i]);
  }
}

void Hacl_Impl_Ed25519_PointDouble_point_double(u64 *out, u64 *p)
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
  fdifference(tmp61, tmp51);
  fdifference(tmp21, tmp11);
  Hacl_Bignum25519_reduce_513(tmp21);
  Hacl_Bignum25519_reduce_513(tmp41);
  fsum(tmp41, tmp21);
  fmul(x3, tmp4, tmp6);
  fmul(y3, tmp2, tmp3);
  fmul(t3, tmp6, tmp3);
  fmul(z3, tmp4, tmp2);
}

static inline void pow2_252m2(u64 *out, u64 *z)
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

static inline bool is_0(u64 *x)
{
  u64 x0 = x[0U];
  u64 x1 = x[1U];
  u64 x2 = x[2U];
  u64 x3 = x[3U];
  u64 x4 = x[4U];
  return x0 == (u64)0U && x1 == (u64)0U && x2 == (u64)0U && x3 == (u64)0U && x4 == (u64)0U;
}

static inline void mul_modp_sqrt_m1(u64 *x)
{
  u64 sqrt_m1[5U] = { 0U };
  sqrt_m1[0U] = (u64)0x00061b274a0ea0b0U;
  sqrt_m1[1U] = (u64)0x0000d5a5fc8f189dU;
  sqrt_m1[2U] = (u64)0x0007ef5e9cbd0c60U;
  sqrt_m1[3U] = (u64)0x00078595a6804c9eU;
  sqrt_m1[4U] = (u64)0x0002b8324804fc1dU;
  fmul(x, x, sqrt_m1);
}

static inline bool recover_x(u64 *x, u64 *y, u64 sign)
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
    fdifference(one, y2);
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
        fdifference(t10, t00);
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
            fdifference(t1, t01);
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
                    fdifference(x32, t0);
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

static inline void barrett_reduction(u64 *z, u64 *t)
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

static inline void mul_modq(u64 *out, u64 *x, u64 *y)
{
  u64 tmp[10U] = { 0U };
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
  uint128_t xy00 = (uint128_t)x0 * y0;
  uint128_t xy01 = (uint128_t)x0 * y1;
  uint128_t xy02 = (uint128_t)x0 * y2;
  uint128_t xy03 = (uint128_t)x0 * y3;
  uint128_t xy04 = (uint128_t)x0 * y4;
  uint128_t xy10 = (uint128_t)x1 * y0;
  uint128_t xy11 = (uint128_t)x1 * y1;
  uint128_t xy12 = (uint128_t)x1 * y2;
  uint128_t xy13 = (uint128_t)x1 * y3;
  uint128_t xy14 = (uint128_t)x1 * y4;
  uint128_t xy20 = (uint128_t)x2 * y0;
  uint128_t xy21 = (uint128_t)x2 * y1;
  uint128_t xy22 = (uint128_t)x2 * y2;
  uint128_t xy23 = (uint128_t)x2 * y3;
  uint128_t xy24 = (uint128_t)x2 * y4;
  uint128_t xy30 = (uint128_t)x3 * y0;
  uint128_t xy31 = (uint128_t)x3 * y1;
  uint128_t xy32 = (uint128_t)x3 * y2;
  uint128_t xy33 = (uint128_t)x3 * y3;
  uint128_t xy34 = (uint128_t)x3 * y4;
  uint128_t xy40 = (uint128_t)x4 * y0;
  uint128_t xy41 = (uint128_t)x4 * y1;
  uint128_t xy42 = (uint128_t)x4 * y2;
  uint128_t xy43 = (uint128_t)x4 * y3;
  uint128_t xy44 = (uint128_t)x4 * y4;
  uint128_t z00 = xy00;
  uint128_t z10 = xy01 + xy10;
  uint128_t z20 = xy02 + xy11 + xy20;
  uint128_t z30 = xy03 + xy12 + xy21 + xy30;
  uint128_t z40 = xy04 + xy13 + xy22 + xy31 + xy40;
  uint128_t z50 = xy14 + xy23 + xy32 + xy41;
  uint128_t z60 = xy24 + xy33 + xy42;
  uint128_t z70 = xy34 + xy43;
  uint128_t z80 = xy44;
  uint128_t carry0 = z00 >> (u32)56U;
  u64 t10 = (uint64_t)z00 & (u64)0xffffffffffffffU;
  uint128_t c0 = carry0;
  u64 t0 = t10;
  uint128_t carry1 = (z10 + c0) >> (u32)56U;
  u64 t11 = (uint64_t)(z10 + c0) & (u64)0xffffffffffffffU;
  uint128_t c1 = carry1;
  u64 t1 = t11;
  uint128_t carry2 = (z20 + c1) >> (u32)56U;
  u64 t12 = (uint64_t)(z20 + c1) & (u64)0xffffffffffffffU;
  uint128_t c2 = carry2;
  u64 t2 = t12;
  uint128_t carry3 = (z30 + c2) >> (u32)56U;
  u64 t13 = (uint64_t)(z30 + c2) & (u64)0xffffffffffffffU;
  uint128_t c3 = carry3;
  u64 t3 = t13;
  uint128_t carry4 = (z40 + c3) >> (u32)56U;
  u64 t14 = (uint64_t)(z40 + c3) & (u64)0xffffffffffffffU;
  uint128_t c4 = carry4;
  u64 t4 = t14;
  uint128_t carry5 = (z50 + c4) >> (u32)56U;
  u64 t15 = (uint64_t)(z50 + c4) & (u64)0xffffffffffffffU;
  uint128_t c5 = carry5;
  u64 t5 = t15;
  uint128_t carry6 = (z60 + c5) >> (u32)56U;
  u64 t16 = (uint64_t)(z60 + c5) & (u64)0xffffffffffffffU;
  uint128_t c6 = carry6;
  u64 t6 = t16;
  uint128_t carry7 = (z70 + c6) >> (u32)56U;
  u64 t17 = (uint64_t)(z70 + c6) & (u64)0xffffffffffffffU;
  uint128_t c7 = carry7;
  u64 t7 = t17;
  uint128_t carry = (z80 + c7) >> (u32)56U;
  u64 t = (uint64_t)(z80 + c7) & (u64)0xffffffffffffffU;
  uint128_t c8 = carry;
  u64 t8 = t;
  u64 t9 = (uint64_t)c8;
  u64 z0 = t0;
  u64 z1 = t1;
  u64 z2 = t2;
  u64 z3 = t3;
  u64 z4 = t4;
  u64 z5 = t5;
  u64 z6 = t6;
  u64 z7 = t7;
  u64 z8 = t8;
  u64 z9 = t9;
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

static inline void add_modq(u64 *out, u64 *x, u64 *y)
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

static inline bool gte_q(u64 *s)
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

static inline bool eq(u64 *a, u64 *b)
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

bool Hacl_Impl_Ed25519_PointEqual_point_equal(u64 *p, u64 *q)
{
  u64 tmp[20U] = { 0U };
  u64 *pxqz = tmp;
  u64 *qxpz = tmp + (u32)5U;
  bool b;
  bool res;
  fmul(pxqz, p, q + (u32)10U);
  reduce(pxqz);
  fmul(qxpz, q, p + (u32)10U);
  reduce(qxpz);
  b = eq(pxqz, qxpz);
  if (b)
  {
    u64 *pyqz = tmp + (u32)10U;
    u64 *qypz = tmp + (u32)15U;
    fmul(pyqz, p + (u32)5U, q + (u32)10U);
    reduce(pyqz);
    fmul(qypz, q + (u32)5U, p + (u32)10U);
    reduce(qypz);
    res = eq(pyqz, qypz);
  }
  else
    res = false;
  return res;
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
  fdifference(tmp10, y1);
  fdifference(tmp20, y2);
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
  fdifference(tmp11, tmp41);
  fdifference(tmp60, tmp50);
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

void Hacl_Impl_Ed25519_PointNegate_point_negate(u64 *p, u64 *out)
{
  u64 zero[5U] = { 0U };
  u64 *x;
  u64 *y;
  u64 *z;
  u64 *t;
  u64 *x1;
  u64 *y1;
  u64 *z1;
  u64 *t1;
  zero[0U] = (u64)0U;
  zero[1U] = (u64)0U;
  zero[2U] = (u64)0U;
  zero[3U] = (u64)0U;
  zero[4U] = (u64)0U;
  x = p;
  y = p + (u32)5U;
  z = p + (u32)10U;
  t = p + (u32)15U;
  x1 = out;
  y1 = out + (u32)5U;
  z1 = out + (u32)10U;
  t1 = out + (u32)15U;
  memcpy(x1, x, (u32)5U * sizeof (u64));
  fdifference(x1, zero);
  Hacl_Bignum25519_reduce_513(x1);
  memcpy(y1, y, (u32)5U * sizeof (u64));
  memcpy(z1, z, (u32)5U * sizeof (u64));
  memcpy(t1, t, (u32)5U * sizeof (u64));
  fdifference(t1, zero);
  Hacl_Bignum25519_reduce_513(t1);
}

void Hacl_Impl_Ed25519_Ladder_point_mul(u64 *result, u8 *scalar, u64 *q)
{
  u64 bscalar[4U] = { 0U };
  u64 *x0;
  u64 *y;
  u64 *z;
  u64 *t;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = bscalar;
      u8 *bj = scalar + i * (u32)8U;
      u64 u = load64_le(bj);
      u64 r = u;
      u64 x = r;
      os[i] = x;
    }
  }
  x0 = result;
  y = result + (u32)5U;
  z = result + (u32)10U;
  t = result + (u32)15U;
  x0[0U] = (u64)0U;
  x0[1U] = (u64)0U;
  x0[2U] = (u64)0U;
  x0[3U] = (u64)0U;
  x0[4U] = (u64)0U;
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
  {
    u64 table[320U] = { 0U };
    u64 *t1;
    memcpy(table, result, (u32)20U * sizeof (u64));
    t1 = table + (u32)20U;
    memcpy(t1, q, (u32)20U * sizeof (u64));
    {
      u32 i;
      for (i = (u32)0U; i < (u32)15U; i++)
      {
        u64 *t11 = table + i * (u32)20U;
        u64 *t2 = table + i * (u32)20U + (u32)20U;
        Hacl_Impl_Ed25519_PointAdd_point_add(t2, q, t11);
      }
    }
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < (u32)64U; i0++)
      {
        {
          u32 i;
          for (i = (u32)0U; i < (u32)4U; i++)
            Hacl_Impl_Ed25519_PointDouble_point_double(result, result);
        }
        {
          u32 bk = (u32)256U;
          u64 mask_l = (u64)16U - (u64)1U;
          u32 i1 = (bk - (u32)4U * i0 - (u32)4U) / (u32)64U;
          u32 j = (bk - (u32)4U * i0 - (u32)4U) % (u32)64U;
          u64 p1 = bscalar[i1] >> j;
          u64 ite;
          if (i1 + (u32)1U < (u32)4U && (u32)0U < j)
            ite = p1 | bscalar[i1 + (u32)1U] << ((u32)64U - j);
          else
            ite = p1;
          {
            u64 bits_l = ite & mask_l;
            u64 a_bits_l[20U] = { 0U };
            memcpy(a_bits_l, table, (u32)20U * sizeof (u64));
            {
              u32 i2;
              for (i2 = (u32)0U; i2 < (u32)15U; i2++)
              {
                u64 c = FStar_UInt64_eq_mask(bits_l, (u64)(i2 + (u32)1U));
                u64 *res_j = table + (i2 + (u32)1U) * (u32)20U;
                {
                  u32 i;
                  for (i = (u32)0U; i < (u32)20U; i++)
                  {
                    u64 *os = a_bits_l;
                    u64 x = (c & res_j[i]) | (~c & a_bits_l[i]);
                    os[i] = x;
                  }
                }
              }
            }
            Hacl_Impl_Ed25519_PointAdd_point_add(result, result, a_bits_l);
          }
        }
      }
    }
  }
}

static inline void point_mul_g(u64 *result, u8 *scalar)
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

static inline void
point_mul_double_vartime(u64 *result, u8 *scalar1, u64 *q1, u8 *scalar2, u64 *q2)
{
  u64 bscalar1[4U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = bscalar1;
      u8 *bj = scalar1 + i * (u32)8U;
      u64 u = load64_le(bj);
      u64 r = u;
      u64 x = r;
      os[i] = x;
    }
  }
  {
    u64 bscalar2[4U] = { 0U };
    u64 *x;
    u64 *y;
    u64 *z;
    u64 *t;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)4U; i++)
      {
        u64 *os = bscalar2;
        u8 *bj = scalar2 + i * (u32)8U;
        u64 u = load64_le(bj);
        u64 r = u;
        u64 x0 = r;
        os[i] = x0;
      }
    }
    x = result;
    y = result + (u32)5U;
    z = result + (u32)10U;
    t = result + (u32)15U;
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
    {
      u64 table1[320U] = { 0U };
      u64 *t10;
      memcpy(table1, result, (u32)20U * sizeof (u64));
      t10 = table1 + (u32)20U;
      memcpy(t10, q1, (u32)20U * sizeof (u64));
      {
        u32 i;
        for (i = (u32)0U; i < (u32)15U; i++)
        {
          u64 *t11 = table1 + i * (u32)20U;
          u64 *t2 = table1 + i * (u32)20U + (u32)20U;
          Hacl_Impl_Ed25519_PointAdd_point_add(t2, q1, t11);
        }
      }
      {
        u64 table2[320U] = { 0U };
        u64 *t1;
        memcpy(table2, result, (u32)20U * sizeof (u64));
        t1 = table2 + (u32)20U;
        memcpy(t1, q2, (u32)20U * sizeof (u64));
        {
          u32 i;
          for (i = (u32)0U; i < (u32)15U; i++)
          {
            u64 *t11 = table2 + i * (u32)20U;
            u64 *t2 = table2 + i * (u32)20U + (u32)20U;
            Hacl_Impl_Ed25519_PointAdd_point_add(t2, q2, t11);
          }
        }
        {
          u32 i;
          for (i = (u32)0U; i < (u32)64U; i++)
          {
            {
              u32 i0;
              for (i0 = (u32)0U; i0 < (u32)4U; i0++)
                Hacl_Impl_Ed25519_PointDouble_point_double(result, result);
            }
            {
              u32 bk = (u32)256U;
              u64 mask_l0 = (u64)16U - (u64)1U;
              u32 i10 = (bk - (u32)4U * i - (u32)4U) / (u32)64U;
              u32 j0 = (bk - (u32)4U * i - (u32)4U) % (u32)64U;
              u64 p10 = bscalar1[i10] >> j0;
              u64 ite0;
              if (i10 + (u32)1U < (u32)4U && (u32)0U < j0)
                ite0 = p10 | bscalar1[i10 + (u32)1U] << ((u32)64U - j0);
              else
                ite0 = p10;
              {
                u64 bits_l = ite0 & mask_l0;
                u64 a_bits_l0[20U] = { 0U };
                u32 bits_l320 = (u32)bits_l;
                u64 *a_bits_l1 = table1 + bits_l320 * (u32)20U;
                memcpy(a_bits_l0, a_bits_l1, (u32)20U * sizeof (u64));
                Hacl_Impl_Ed25519_PointAdd_point_add(result, result, a_bits_l0);
                {
                  u32 bk0 = (u32)256U;
                  u64 mask_l = (u64)16U - (u64)1U;
                  u32 i1 = (bk0 - (u32)4U * i - (u32)4U) / (u32)64U;
                  u32 j = (bk0 - (u32)4U * i - (u32)4U) % (u32)64U;
                  u64 p1 = bscalar2[i1] >> j;
                  u64 ite;
                  if (i1 + (u32)1U < (u32)4U && (u32)0U < j)
                    ite = p1 | bscalar2[i1 + (u32)1U] << ((u32)64U - j);
                  else
                    ite = p1;
                  {
                    u64 bits_l0 = ite & mask_l;
                    u64 a_bits_l[20U] = { 0U };
                    u32 bits_l32 = (u32)bits_l0;
                    u64 *a_bits_l10 = table2 + bits_l32 * (u32)20U;
                    memcpy(a_bits_l, a_bits_l10, (u32)20U * sizeof (u64));
                    Hacl_Impl_Ed25519_PointAdd_point_add(result, result, a_bits_l);
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

static inline void point_mul_g_double_vartime(u64 *result, u8 *scalar1, u8 *scalar2, u64 *q2)
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
  point_mul_double_vartime(result, scalar1, g, scalar2, q2);
}

static inline void
point_negate_mul_double_g_vartime(u64 *result, u8 *scalar1, u8 *scalar2, u64 *q2)
{
  u64 q2_neg[20U] = { 0U };
  Hacl_Impl_Ed25519_PointNegate_point_negate(q2, q2_neg);
  point_mul_g_double_vartime(result, scalar1, scalar2, q2_neg);
}

static inline void store_56(u8 *out, u64 *b)
{
  u64 b0 = b[0U];
  u64 b1 = b[1U];
  u64 b2 = b[2U];
  u64 b3 = b[3U];
  u64 b4 = b[4U];
  u32 b4_ = (u32)b4;
  u8 *b80 = out;
  u8 *b81;
  u8 *b82;
  u8 *b8;
  store64_le(b80, b0);
  b81 = out + (u32)7U;
  store64_le(b81, b1);
  b82 = out + (u32)14U;
  store64_le(b82, b2);
  b8 = out + (u32)21U;
  store64_le(b8, b3);
  store32_le(out + (u32)28U, b4_);
}

static inline void load_64_bytes(u64 *out, u8 *b)
{
  u8 *b80 = b;
  u64 u = load64_le(b80);
  u64 z = u;
  u64 b0 = z & (u64)0xffffffffffffffU;
  u8 *b81 = b + (u32)7U;
  u64 u0 = load64_le(b81);
  u64 z0 = u0;
  u64 b1 = z0 & (u64)0xffffffffffffffU;
  u8 *b82 = b + (u32)14U;
  u64 u1 = load64_le(b82);
  u64 z1 = u1;
  u64 b2 = z1 & (u64)0xffffffffffffffU;
  u8 *b83 = b + (u32)21U;
  u64 u2 = load64_le(b83);
  u64 z2 = u2;
  u64 b3 = z2 & (u64)0xffffffffffffffU;
  u8 *b84 = b + (u32)28U;
  u64 u3 = load64_le(b84);
  u64 z3 = u3;
  u64 b4 = z3 & (u64)0xffffffffffffffU;
  u8 *b85 = b + (u32)35U;
  u64 u4 = load64_le(b85);
  u64 z4 = u4;
  u64 b5 = z4 & (u64)0xffffffffffffffU;
  u8 *b86 = b + (u32)42U;
  u64 u5 = load64_le(b86);
  u64 z5 = u5;
  u64 b6 = z5 & (u64)0xffffffffffffffU;
  u8 *b87 = b + (u32)49U;
  u64 u6 = load64_le(b87);
  u64 z6 = u6;
  u64 b7 = z6 & (u64)0xffffffffffffffU;
  u8 *b8 = b + (u32)56U;
  u64 u7 = load64_le(b8);
  u64 z7 = u7;
  u64 b88 = z7 & (u64)0xffffffffffffffU;
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
  out[8U] = b88;
  out[9U] = b9;
}

static inline void load_32_bytes(u64 *out, u8 *b)
{
  u8 *b80 = b;
  u64 u0 = load64_le(b80);
  u64 z = u0;
  u64 b0 = z & (u64)0xffffffffffffffU;
  u8 *b81 = b + (u32)7U;
  u64 u1 = load64_le(b81);
  u64 z0 = u1;
  u64 b1 = z0 & (u64)0xffffffffffffffU;
  u8 *b82 = b + (u32)14U;
  u64 u2 = load64_le(b82);
  u64 z1 = u2;
  u64 b2 = z1 & (u64)0xffffffffffffffU;
  u8 *b8 = b + (u32)21U;
  u64 u3 = load64_le(b8);
  u64 z2 = u3;
  u64 b3 = z2 & (u64)0xffffffffffffffU;
  u32 u = load32_le(b + (u32)28U);
  u32 b4 = u;
  u64 b41 = (u64)b4;
  out[0U] = b0;
  out[1U] = b1;
  out[2U] = b2;
  out[3U] = b3;
  out[4U] = b41;
}

static inline void sha512_pre_msg(u8 *hash, u8 *prefix, u32 len, u8 *input)
{
  u8 buf[128U] = { 0U };
  u64 block_state[8U] = { 0U };
  Hacl_Streaming_SHA2_state_sha2_384
  s = { .block_state = block_state, .buf = buf, .total_len = (u64)0U };
  Hacl_Streaming_SHA2_state_sha2_384 p = s;
  Hacl_Streaming_SHA2_state_sha2_384 *st;
  Hacl_Hash_Core_SHA2_init_512(block_state);
  st = &p;
  Hacl_Streaming_SHA2_update_512(st, prefix, (u32)32U);
  Hacl_Streaming_SHA2_update_512(st, input, len);
  Hacl_Streaming_SHA2_finish_512(st, hash);
}

static inline void sha512_pre_pre2_msg(u8 *hash, u8 *prefix, u8 *prefix2, u32 len, u8 *input)
{
  u8 buf[128U] = { 0U };
  u64 block_state[8U] = { 0U };
  Hacl_Streaming_SHA2_state_sha2_384
  s = { .block_state = block_state, .buf = buf, .total_len = (u64)0U };
  Hacl_Streaming_SHA2_state_sha2_384 p = s;
  Hacl_Streaming_SHA2_state_sha2_384 *st;
  Hacl_Hash_Core_SHA2_init_512(block_state);
  st = &p;
  Hacl_Streaming_SHA2_update_512(st, prefix, (u32)32U);
  Hacl_Streaming_SHA2_update_512(st, prefix2, (u32)32U);
  Hacl_Streaming_SHA2_update_512(st, input, len);
  Hacl_Streaming_SHA2_finish_512(st, hash);
}

static inline void sha512_modq_pre(u64 *out, u8 *prefix, u32 len, u8 *input)
{
  u64 tmp[10U] = { 0U };
  u8 hash[64U] = { 0U };
  sha512_pre_msg(hash, prefix, len, input);
  load_64_bytes(tmp, hash);
  barrett_reduction(out, tmp);
}

static inline void sha512_modq_pre_pre2(u64 *out, u8 *prefix, u8 *prefix2, u32 len, u8 *input)
{
  u64 tmp[10U] = { 0U };
  u8 hash[64U] = { 0U };
  sha512_pre_pre2_msg(hash, prefix, prefix2, len, input);
  load_64_bytes(tmp, hash);
  barrett_reduction(out, tmp);
}

static inline void point_mul_g_compress(u8 *out, u8 *s)
{
  u64 tmp[20U] = { 0U };
  point_mul_g(tmp, s);
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, tmp);
}

static inline void secret_expand(u8 *expanded, u8 *secret)
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

/********************************************************************************
  Verified C library for EdDSA signing and verification on the edwards25519 curve.
********************************************************************************/


/*
Compute the public key from the private key.

  The outparam `public_key`  points to 32 bytes of valid memory, i.e., uint8_t[32].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].
*/
void Hacl_Ed25519_secret_to_public(u8 *public_key, u8 *private_key)
{
  u8 expanded_secret[64U] = { 0U };
  u8 *a;
  secret_expand(expanded_secret, private_key);
  a = expanded_secret;
  point_mul_g_compress(public_key, a);
}

/*
Compute the expanded keys for an Ed25519 signature.

  The outparam `expanded_keys` points to 96 bytes of valid memory, i.e., uint8_t[96].
  The argument `private_key`   points to 32 bytes of valid memory, i.e., uint8_t[32].

  If one needs to sign several messages under the same private key, it is more efficient
  to call `expand_keys` only once and `sign_expanded` multiple times, for each message.
*/
void Hacl_Ed25519_expand_keys(u8 *expanded_keys, u8 *private_key)
{
  u8 *public_key = expanded_keys;
  u8 *s_prefix = expanded_keys + (u32)32U;
  u8 *s = expanded_keys + (u32)32U;
  secret_expand(s_prefix, private_key);
  point_mul_g_compress(public_key, s);
}

/*
Create an Ed25519 signature with the (precomputed) expanded keys.

  The outparam `signature`     points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `expanded_keys` points to 96 bytes of valid memory, i.e., uint8_t[96].
  The argument `msg`    points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].

  The argument `expanded_keys` is obtained through `expand_keys`.

  If one needs to sign several messages under the same private key, it is more efficient
  to call `expand_keys` only once and `sign_expanded` multiple times, for each message.
*/
void Hacl_Ed25519_sign_expanded(u8 *signature, u8 *expanded_keys, u32 msg_len, u8 *msg)
{
  u8 *rs = signature;
  u8 *ss = signature + (u32)32U;
  u64 rq[5U] = { 0U };
  u64 hq[5U] = { 0U };
  u8 rb[32U] = { 0U };
  u8 *public_key = expanded_keys;
  u8 *s = expanded_keys + (u32)32U;
  u8 *prefix = expanded_keys + (u32)64U;
  sha512_modq_pre(rq, prefix, msg_len, msg);
  store_56(rb, rq);
  point_mul_g_compress(rs, rb);
  sha512_modq_pre_pre2(hq, rs, public_key, msg_len, msg);
  {
    u64 aq[5U] = { 0U };
    load_32_bytes(aq, s);
    mul_modq(aq, hq, aq);
    add_modq(aq, rq, aq);
    store_56(ss, aq);
  }
}

/*
Create an Ed25519 signature.

  The outparam `signature`   points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The argument `msg`  points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].

  The function first calls `expand_keys` and then invokes `sign_expanded`.

  If one needs to sign several messages under the same private key, it is more efficient
  to call `expand_keys` only once and `sign_expanded` multiple times, for each message.
*/
void Hacl_Ed25519_sign(u8 *signature, u8 *private_key, u32 msg_len, u8 *msg)
{
  u8 expanded_keys[96U] = { 0U };
  Hacl_Ed25519_expand_keys(expanded_keys, private_key);
  Hacl_Ed25519_sign_expanded(signature, expanded_keys, msg_len, msg);
}

/*
Verify an Ed25519 signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `public_key` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `signature`  points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_Ed25519_verify(u8 *public_key, u32 msg_len, u8 *msg, u8 *signature)
{
  u64 a_[20U] = { 0U };
  bool b = Hacl_Impl_Ed25519_PointDecompress_point_decompress(a_, public_key);
  if (b)
  {
    u64 r_[20U] = { 0U };
    u8 *rs = signature;
    bool b_ = Hacl_Impl_Ed25519_PointDecompress_point_decompress(r_, rs);
    if (b_)
    {
      u8 hb[32U] = { 0U };
      u8 *rs1 = signature;
      u8 *sb = signature + (u32)32U;
      u64 tmp[5U] = { 0U };
      load_32_bytes(tmp, sb);
      {
        bool b1 = gte_q(tmp);
        bool b10 = b1;
        if (b10)
          return false;
        {
          u64 tmp0[5U] = { 0U };
          sha512_modq_pre_pre2(tmp0, rs1, public_key, msg_len, msg);
          store_56(hb, tmp0);
          {
            u64 exp_d[20U] = { 0U };
            point_negate_mul_double_g_vartime(exp_d, sb, hb, a_);
            {
              bool b2 = Hacl_Impl_Ed25519_PointEqual_point_equal(exp_d, r_);
              return b2;
            }
          }
        }
      }
    }
    return false;
  }
  return false;
}

