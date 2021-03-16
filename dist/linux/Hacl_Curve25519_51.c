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


#include "Hacl_Curve25519_51.h"

static const u8 g25519[32U] = { (u8)9U };

static void point_add_and_double(u64 *q, u64 *p01_tmp1, uint128_t *tmp2)
{
  u64 *nq = p01_tmp1;
  u64 *nq_p1 = p01_tmp1 + (u32)10U;
  u64 *tmp1 = p01_tmp1 + (u32)20U;
  u64 *x1 = q;
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)5U;
  u64 *z3 = nq_p1 + (u32)5U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)5U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)10U;
  u64 *x3;
  u64 *z31;
  u64 *d0;
  u64 *c0;
  u64 *a1;
  u64 *b1;
  u64 *d;
  u64 *c;
  u64 *ab1;
  u64 *dc1;
  Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
  x3 = nq_p1;
  z31 = nq_p1 + (u32)5U;
  d0 = dc;
  c0 = dc + (u32)5U;
  Hacl_Impl_Curve25519_Field51_fadd(c0, x3, z31);
  Hacl_Impl_Curve25519_Field51_fsub(d0, x3, z31);
  Hacl_Impl_Curve25519_Field51_fmul2(dc, dc, ab, tmp2);
  Hacl_Impl_Curve25519_Field51_fadd(x3, d0, c0);
  Hacl_Impl_Curve25519_Field51_fsub(z31, d0, c0);
  a1 = tmp1;
  b1 = tmp1 + (u32)5U;
  d = tmp1 + (u32)10U;
  c = tmp1 + (u32)15U;
  ab1 = tmp1;
  dc1 = tmp1 + (u32)10U;
  Hacl_Impl_Curve25519_Field51_fsqr2(dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field51_fsqr2(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  a1[4U] = c[4U];
  Hacl_Impl_Curve25519_Field51_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field51_fmul1(b1, c, (u64)121665U);
  Hacl_Impl_Curve25519_Field51_fadd(b1, b1, d);
  Hacl_Impl_Curve25519_Field51_fmul2(nq, dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field51_fmul(z3, z3, x1, tmp2);
}

static void point_double(u64 *nq, u64 *tmp1, uint128_t *tmp2)
{
  u64 *x2 = nq;
  u64 *z2 = nq + (u32)5U;
  u64 *a = tmp1;
  u64 *b = tmp1 + (u32)5U;
  u64 *d = tmp1 + (u32)10U;
  u64 *c = tmp1 + (u32)15U;
  u64 *ab = tmp1;
  u64 *dc = tmp1 + (u32)10U;
  Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
  Hacl_Impl_Curve25519_Field51_fsqr2(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  a[4U] = c[4U];
  Hacl_Impl_Curve25519_Field51_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field51_fmul1(b, c, (u64)121665U);
  Hacl_Impl_Curve25519_Field51_fadd(b, b, d);
  Hacl_Impl_Curve25519_Field51_fmul2(nq, dc, ab, tmp2);
}

static void montgomery_ladder(u64 *out, u8 *key, u64 *init)
{
  uint128_t tmp2[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp2[_i] = (uint128_t)(u64)0U;
  }
  {
    u64 p01_tmp1_swap[41U] = { 0U };
    u64 *p0 = p01_tmp1_swap;
    u64 *p01 = p01_tmp1_swap;
    u64 *p03 = p01;
    u64 *p11 = p01 + (u32)10U;
    u64 *x0;
    u64 *z0;
    u64 *p01_tmp1;
    u64 *p01_tmp11;
    u64 *nq10;
    u64 *nq_p11;
    u64 *swap;
    u64 sw0;
    u64 *nq1;
    u64 *tmp1;
    memcpy(p11, init, (u32)10U * sizeof (u64));
    x0 = p03;
    z0 = p03 + (u32)5U;
    x0[0U] = (u64)1U;
    x0[1U] = (u64)0U;
    x0[2U] = (u64)0U;
    x0[3U] = (u64)0U;
    x0[4U] = (u64)0U;
    z0[0U] = (u64)0U;
    z0[1U] = (u64)0U;
    z0[2U] = (u64)0U;
    z0[3U] = (u64)0U;
    z0[4U] = (u64)0U;
    p01_tmp1 = p01_tmp1_swap;
    p01_tmp11 = p01_tmp1_swap;
    nq10 = p01_tmp1_swap;
    nq_p11 = p01_tmp1_swap + (u32)10U;
    swap = p01_tmp1_swap + (u32)40U;
    Hacl_Impl_Curve25519_Field51_cswap2((u64)1U, nq10, nq_p11);
    point_add_and_double(init, p01_tmp11, tmp2);
    swap[0U] = (u64)1U;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)251U; i++)
      {
        u64 *p01_tmp12 = p01_tmp1_swap;
        u64 *swap1 = p01_tmp1_swap + (u32)40U;
        u64 *nq2 = p01_tmp12;
        u64 *nq_p12 = p01_tmp12 + (u32)10U;
        u64 bit = (u64)(key[((u32)253U - i) / (u32)8U] >> ((u32)253U - i) % (u32)8U & (u8)1U);
        u64 sw = swap1[0U] ^ bit;
        Hacl_Impl_Curve25519_Field51_cswap2(sw, nq2, nq_p12);
        point_add_and_double(init, p01_tmp12, tmp2);
        swap1[0U] = bit;
      }
    }
    sw0 = swap[0U];
    Hacl_Impl_Curve25519_Field51_cswap2(sw0, nq10, nq_p11);
    nq1 = p01_tmp1;
    tmp1 = p01_tmp1 + (u32)20U;
    point_double(nq1, tmp1, tmp2);
    point_double(nq1, tmp1, tmp2);
    point_double(nq1, tmp1, tmp2);
    memcpy(out, p0, (u32)10U * sizeof (u64));
  }
}

void Hacl_Curve25519_51_fsquare_times(u64 *o, u64 *inp, uint128_t *tmp, u32 n)
{
  u32 i;
  Hacl_Impl_Curve25519_Field51_fsqr(o, inp, tmp);
  for (i = (u32)0U; i < n - (u32)1U; i++)
    Hacl_Impl_Curve25519_Field51_fsqr(o, o, tmp);
}

void Hacl_Curve25519_51_finv(u64 *o, u64 *i, uint128_t *tmp)
{
  u64 t1[20U] = { 0U };
  u64 *a1 = t1;
  u64 *b10 = t1 + (u32)5U;
  u64 *t010 = t1 + (u32)15U;
  uint128_t *tmp10 = tmp;
  u64 *b11;
  u64 *c10;
  u64 *t011;
  uint128_t *tmp11;
  u64 *b1;
  u64 *c1;
  u64 *t01;
  uint128_t *tmp1;
  u64 *a;
  u64 *t0;
  Hacl_Curve25519_51_fsquare_times(a1, i, tmp10, (u32)1U);
  Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, (u32)2U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t010, i, tmp);
  Hacl_Impl_Curve25519_Field51_fmul(a1, b10, a1, tmp);
  Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, (u32)1U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t010, b10, tmp);
  Hacl_Curve25519_51_fsquare_times(t010, b10, tmp10, (u32)5U);
  Hacl_Impl_Curve25519_Field51_fmul(b10, t010, b10, tmp);
  b11 = t1 + (u32)5U;
  c10 = t1 + (u32)10U;
  t011 = t1 + (u32)15U;
  tmp11 = tmp;
  Hacl_Curve25519_51_fsquare_times(t011, b11, tmp11, (u32)10U);
  Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b11, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, c10, tmp11, (u32)20U);
  Hacl_Impl_Curve25519_Field51_fmul(t011, t011, c10, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, t011, tmp11, (u32)10U);
  Hacl_Impl_Curve25519_Field51_fmul(b11, t011, b11, tmp);
  Hacl_Curve25519_51_fsquare_times(t011, b11, tmp11, (u32)50U);
  Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b11, tmp);
  b1 = t1 + (u32)5U;
  c1 = t1 + (u32)10U;
  t01 = t1 + (u32)15U;
  tmp1 = tmp;
  Hacl_Curve25519_51_fsquare_times(t01, c1, tmp1, (u32)100U);
  Hacl_Impl_Curve25519_Field51_fmul(t01, t01, c1, tmp);
  Hacl_Curve25519_51_fsquare_times(t01, t01, tmp1, (u32)50U);
  Hacl_Impl_Curve25519_Field51_fmul(t01, t01, b1, tmp);
  Hacl_Curve25519_51_fsquare_times(t01, t01, tmp1, (u32)5U);
  a = t1;
  t0 = t1 + (u32)15U;
  Hacl_Impl_Curve25519_Field51_fmul(o, t0, a, tmp);
}

static void encode_point(u8 *o, u64 *i)
{
  u64 *x = i;
  u64 *z = i + (u32)5U;
  u64 tmp[5U] = { 0U };
  u64 u64s[4U] = { 0U };
  uint128_t tmp_w[10U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)10U; ++_i)
      tmp_w[_i] = (uint128_t)(u64)0U;
  }
  Hacl_Curve25519_51_finv(tmp, z, tmp_w);
  Hacl_Impl_Curve25519_Field51_fmul(tmp, tmp, x, tmp_w);
  Hacl_Impl_Curve25519_Field51_store_felem(u64s, tmp);
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
      store64_le(o + i0 * (u32)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_51_scalarmult(u8 *out, u8 *priv, u8 *pub)
{
  u64 init[10U] = { 0U };
  u64 tmp[4U] = { 0U };
  u64 tmp3;
  u64 *x;
  u64 *z;
  u64 f0l;
  u64 f0h;
  u64 f1l;
  u64 f1h;
  u64 f2l;
  u64 f2h;
  u64 f3l;
  u64 f3h;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u64 *os = tmp;
      u8 *bj = pub + i * (u32)8U;
      u64 u = load64_le(bj);
      u64 r = u;
      u64 x0 = r;
      os[i] = x0;
    }
  }
  tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (u64)0x7fffffffffffffffU;
  x = init;
  z = init + (u32)5U;
  z[0U] = (u64)1U;
  z[1U] = (u64)0U;
  z[2U] = (u64)0U;
  z[3U] = (u64)0U;
  z[4U] = (u64)0U;
  f0l = tmp[0U] & (u64)0x7ffffffffffffU;
  f0h = tmp[0U] >> (u32)51U;
  f1l = (tmp[1U] & (u64)0x3fffffffffU) << (u32)13U;
  f1h = tmp[1U] >> (u32)38U;
  f2l = (tmp[2U] & (u64)0x1ffffffU) << (u32)26U;
  f2h = tmp[2U] >> (u32)25U;
  f3l = (tmp[3U] & (u64)0xfffU) << (u32)39U;
  f3h = tmp[3U] >> (u32)12U;
  x[0U] = f0l;
  x[1U] = f0h | f1l;
  x[2U] = f1h | f2l;
  x[3U] = f2h | f3l;
  x[4U] = f3h;
  montgomery_ladder(init, priv, init);
  encode_point(out, init);
}

void Hacl_Curve25519_51_secret_to_public(u8 *pub, u8 *priv)
{
  u8 basepoint[32U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)32U; i++)
    {
      u8 *os = basepoint;
      u8 x = g25519[i];
      os[i] = x;
    }
  }
  Hacl_Curve25519_51_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_51_ecdh(u8 *out, u8 *priv, u8 *pub)
{
  u8 zeros[32U] = { 0U };
  Hacl_Curve25519_51_scalarmult(out, priv, pub);
  {
    u8 res = (u8)255U;
    u8 z;
    bool r;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)32U; i++)
      {
        u8 uu____0 = FStar_UInt8_eq_mask(out[i], zeros[i]);
        res = uu____0 & res;
      }
    }
    z = res;
    r = z == (u8)255U;
    return !r;
  }
}

