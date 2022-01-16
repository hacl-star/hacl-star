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

#include "internal/Hacl_Ed25519.h"

void Hacl_EC_Ed25519_mk_felem_zero(uint64_t *b)
{
  b[0U] = (uint64_t)0U;
  b[1U] = (uint64_t)0U;
  b[2U] = (uint64_t)0U;
  b[3U] = (uint64_t)0U;
  b[4U] = (uint64_t)0U;
}

void Hacl_EC_Ed25519_mk_felem_one(uint64_t *b)
{
  b[0U] = (uint64_t)1U;
  b[1U] = (uint64_t)0U;
  b[2U] = (uint64_t)0U;
  b[3U] = (uint64_t)0U;
  b[4U] = (uint64_t)0U;
}

void Hacl_EC_Ed25519_felem_add(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_Impl_Curve25519_Field51_fadd(out, a, b);
  Hacl_Bignum25519_reduce_513(out);
}

void Hacl_EC_Ed25519_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out)
{
  Hacl_Impl_Curve25519_Field51_fsub(out, a, b);
  Hacl_Bignum25519_reduce_513(out);
}

void Hacl_EC_Ed25519_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out)
{
  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);
  Hacl_Impl_Curve25519_Field51_fmul(out, a, b, tmp);
}

void Hacl_EC_Ed25519_felem_inv(uint64_t *a, uint64_t *out)
{
  Hacl_Bignum25519_inverse(out, a);
  Hacl_Bignum25519_reduce_513(out);
}

void Hacl_EC_Ed25519_felem_load(uint8_t *b, uint64_t *out)
{
  Hacl_Bignum25519_load_51(out, b);
}

void Hacl_EC_Ed25519_felem_store(uint64_t *a, uint8_t *out)
{
  Hacl_Bignum25519_store_51(out, a);
}

void Hacl_EC_Ed25519_mk_point_at_inf(uint64_t *p)
{
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)5U;
  uint64_t *z = p + (uint32_t)10U;
  uint64_t *t = p + (uint32_t)15U;
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
}

void Hacl_EC_Ed25519_mk_base_point(uint64_t *p)
{
  uint64_t *gx = p;
  uint64_t *gy = p + (uint32_t)5U;
  uint64_t *gz = p + (uint32_t)10U;
  uint64_t *gt = p + (uint32_t)15U;
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
}

void Hacl_EC_Ed25519_point_negate(uint64_t *p, uint64_t *out)
{
  Hacl_Impl_Ed25519_PointNegate_point_negate(p, out);
}

void Hacl_EC_Ed25519_point_add(uint64_t *p, uint64_t *q, uint64_t *out)
{
  Hacl_Impl_Ed25519_PointAdd_point_add(out, p, q);
}

void Hacl_EC_Ed25519_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out)
{
  Hacl_Impl_Ed25519_Ladder_point_mul(out, scalar, p);
}

bool Hacl_EC_Ed25519_point_eq(uint64_t *p, uint64_t *q)
{
  return Hacl_Impl_Ed25519_PointEqual_point_equal(p, q);
}

void Hacl_EC_Ed25519_point_compress(uint64_t *p, uint8_t *out)
{
  Hacl_Impl_Ed25519_PointCompress_point_compress(out, p);
}

bool Hacl_EC_Ed25519_point_decompress(uint8_t *s, uint64_t *out)
{
  return Hacl_Impl_Ed25519_PointDecompress_point_decompress(out, s);
}

