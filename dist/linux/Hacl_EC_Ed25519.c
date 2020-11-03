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


#include "Hacl_EC_Ed25519.h"

void Hacl_EC_Ed25519_mk_felem_zero(u64 *b)
{
  b[0U] = (u64)0U;
  b[1U] = (u64)0U;
  b[2U] = (u64)0U;
  b[3U] = (u64)0U;
  b[4U] = (u64)0U;
}

void Hacl_EC_Ed25519_mk_felem_one(u64 *b)
{
  b[0U] = (u64)1U;
  b[1U] = (u64)0U;
  b[2U] = (u64)0U;
  b[3U] = (u64)0U;
  b[4U] = (u64)0U;
}

void Hacl_EC_Ed25519_felem_add(u64 *a, u64 *b, u64 *out)
{
  Hacl_Impl_Curve25519_Field51_fadd(out, a, b);
  Hacl_Bignum25519_reduce_513(out);
}

void Hacl_EC_Ed25519_felem_sub(u64 *a, u64 *b, u64 *out)
{
  Hacl_Impl_Curve25519_Field51_fsub(out, a, b);
  Hacl_Bignum25519_reduce_513(out);
}

void Hacl_EC_Ed25519_felem_mul(u64 *a, u64 *b, u64 *out)
{
  uint128_t tmp[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Impl_Curve25519_Field51_fmul(out, a, b, tmp);
}

void Hacl_EC_Ed25519_felem_inv(u64 *a, u64 *out)
{
  Hacl_Bignum25519_inverse(out, a);
  Hacl_Bignum25519_reduce_513(out);
}

void Hacl_EC_Ed25519_felem_load(u8 *b, u64 *out)
{
  Hacl_Bignum25519_load_51(out, b);
}

void Hacl_EC_Ed25519_felem_store(u64 *a, u8 *out)
{
  Hacl_Bignum25519_store_51(out, a);
}

void Hacl_EC_Ed25519_mk_point_at_inf(u64 *p)
{
  u64 *x = p;
  u64 *y = p + (u32)5U;
  u64 *z = p + (u32)10U;
  u64 *t = p + (u32)15U;
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
}

void Hacl_EC_Ed25519_mk_base_point(u64 *p)
{
  u64 *gx = p;
  u64 *gy = p + (u32)5U;
  u64 *gz = p + (u32)10U;
  u64 *gt = p + (u32)15U;
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
}

void Hacl_EC_Ed25519_point_negate(u64 *p, u64 *out)
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
  Hacl_Bignum25519_fdifference(x1, zero);
  Hacl_Bignum25519_reduce_513(x1);
  memcpy(y1, y, (u32)5U * sizeof (u64));
  memcpy(z1, z, (u32)5U * sizeof (u64));
  memcpy(t1, t, (u32)5U * sizeof (u64));
  Hacl_Bignum25519_fdifference(t1, zero);
  Hacl_Bignum25519_reduce_513(t1);
}

void Hacl_EC_Ed25519_point_add(u64 *p, u64 *q, u64 *out)
{
  Hacl_Impl_Ed25519_PointAdd_point_add(out, p, q);
}

void Hacl_EC_Ed25519_point_mul(u8 *scalar, u64 *p, u64 *out)
{
  Hacl_Impl_Ed25519_Ladder_point_mul(out, scalar, p);
}

bool Hacl_EC_Ed25519_point_eq(u64 *p, u64 *q)
{
  return Hacl_Impl_Ed25519_PointEqual_point_equal(p, q);
}

void Hacl_EC_Ed25519_point_compress(u64 *p, u8 *out)
{
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, p);
}

bool Hacl_EC_Ed25519_point_decompress(u8 *s, u64 *out)
{
  return Hacl_Impl_Ed25519_PointDecompress_point_decompress(out, s);
}

