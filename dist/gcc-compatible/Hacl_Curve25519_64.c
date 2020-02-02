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


#include "Hacl_Curve25519_64.h"

static inline uint64_t add_scalar0(uint64_t *out1, uint64_t *f1, uint64_t f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  return add_scalar(out1, f1, f2);
  #else
  uint64_t scrut = add_scalar_e(out1, f1, f2);
  return scrut;
  #endif
}

static inline void fadd0(uint64_t *out1, uint64_t *f1, uint64_t *f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fadd(out1, f1, f2);
  #else
  uint64_t uu____0 = fadd_e(out1, f1, f2);
  #endif
}

static inline void fsub0(uint64_t *out1, uint64_t *f1, uint64_t *f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsub(out1, f1, f2);
  #else
  uint64_t uu____0 = fsub_e(out1, f1, f2);
  #endif
}

static inline void fmul0(uint64_t *out1, uint64_t *f1, uint64_t *f2, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul(out1, f1, f2, tmp);
  #else
  uint64_t uu____0 = fmul_e(tmp, f1, out1, f2);
  #endif
}

static inline void fmul20(uint64_t *out1, uint64_t *f1, uint64_t *f2, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul2(out1, f1, f2, tmp);
  #else
  uint64_t uu____0 = fmul2_e(tmp, f1, out1, f2);
  #endif
}

static inline void fmul_scalar0(uint64_t *out1, uint64_t *f1, uint64_t f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul_scalar(out1, f1, f2);
  #else
  uint64_t uu____0 = fmul_scalar_e(out1, f1, f2);
  #endif
}

static inline void fsqr0(uint64_t *out1, uint64_t *f1, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsqr(out1, f1, tmp);
  #else
  uint64_t uu____0 = fsqr_e(tmp, f1, out1);
  #endif
}

static inline void fsqr20(uint64_t *out1, uint64_t *f, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsqr2(out1, f, tmp);
  #else
  uint64_t uu____0 = fsqr2_e(tmp, f, out1);
  #endif
}

static inline void cswap20(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  cswap2(bit, p1, p2);
  #else
  uint64_t uu____0 = cswap2_e(bit, p1, p2);
  #endif
}

static uint8_t g25519[32U] = { (uint8_t)9U };

static void point_add_and_double(uint64_t *q, uint64_t *p01_tmp1, uint64_t *tmp2)
{
  uint64_t *nq = p01_tmp1;
  uint64_t *nq_p1 = p01_tmp1 + (uint32_t)8U;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  uint64_t *x1 = q;
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *z3 = nq_p1 + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  fadd0(a, x2, z2);
  fsub0(b, x2, z2);
  uint64_t *x3 = nq_p1;
  uint64_t *z31 = nq_p1 + (uint32_t)4U;
  uint64_t *d0 = dc;
  uint64_t *c0 = dc + (uint32_t)4U;
  fadd0(c0, x3, z31);
  fsub0(d0, x3, z31);
  fmul20(dc, dc, ab, tmp2);
  fadd0(x3, d0, c0);
  fsub0(z31, d0, c0);
  uint64_t *a1 = tmp1;
  uint64_t *b1 = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab1 = tmp1;
  uint64_t *dc1 = tmp1 + (uint32_t)8U;
  fsqr20(dc1, ab1, tmp2);
  fsqr20(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  fsub0(c, d, c);
  fmul_scalar0(b1, c, (uint64_t)121665U);
  fadd0(b1, b1, d);
  fmul20(nq, dc1, ab1, tmp2);
  fmul0(z3, z3, x1, tmp2);
}

static void point_double(uint64_t *nq, uint64_t *tmp1, uint64_t *tmp2)
{
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  fadd0(a, x2, z2);
  fsub0(b, x2, z2);
  fsqr20(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  fsub0(c, d, c);
  fmul_scalar0(b, c, (uint64_t)121665U);
  fadd0(b, b, d);
  fmul20(nq, dc, ab, tmp2);
}

static void montgomery_ladder(uint64_t *out, uint8_t *key, uint64_t *init1)
{
  uint64_t tmp2[16U] = { 0U };
  uint64_t p01_tmp1_swap[33U] = { 0U };
  uint64_t *p0 = p01_tmp1_swap;
  uint64_t *p01 = p01_tmp1_swap;
  uint64_t *p03 = p01;
  uint64_t *p11 = p01 + (uint32_t)8U;
  memcpy(p11, init1, (uint32_t)8U * sizeof (init1[0U]));
  uint64_t *x0 = p03;
  uint64_t *z0 = p03 + (uint32_t)4U;
  x0[0U] = (uint64_t)1U;
  x0[1U] = (uint64_t)0U;
  x0[2U] = (uint64_t)0U;
  x0[3U] = (uint64_t)0U;
  z0[0U] = (uint64_t)0U;
  z0[1U] = (uint64_t)0U;
  z0[2U] = (uint64_t)0U;
  z0[3U] = (uint64_t)0U;
  uint64_t *p01_tmp1 = p01_tmp1_swap;
  uint64_t *p01_tmp11 = p01_tmp1_swap;
  uint64_t *nq1 = p01_tmp1_swap;
  uint64_t *nq_p11 = p01_tmp1_swap + (uint32_t)8U;
  uint64_t *swap1 = p01_tmp1_swap + (uint32_t)32U;
  cswap20((uint64_t)1U, nq1, nq_p11);
  point_add_and_double(init1, p01_tmp11, tmp2);
  swap1[0U] = (uint64_t)1U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)251U; i++)
  {
    uint64_t *p01_tmp12 = p01_tmp1_swap;
    uint64_t *swap2 = p01_tmp1_swap + (uint32_t)32U;
    uint64_t *nq2 = p01_tmp12;
    uint64_t *nq_p12 = p01_tmp12 + (uint32_t)8U;
    uint64_t
    bit =
      (uint64_t)(key[((uint32_t)253U - i)
      / (uint32_t)8U]
      >> ((uint32_t)253U - i) % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t sw = swap2[0U] ^ bit;
    cswap20(sw, nq2, nq_p12);
    point_add_and_double(init1, p01_tmp12, tmp2);
    swap2[0U] = bit;
  }
  uint64_t sw = swap1[0U];
  cswap20(sw, nq1, nq_p11);
  uint64_t *nq10 = p01_tmp1;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  point_double(nq10, tmp1, tmp2);
  point_double(nq10, tmp1, tmp2);
  point_double(nq10, tmp1, tmp2);
  memcpy(out, p0, (uint32_t)8U * sizeof (p0[0U]));
}

static void fsquare_times(uint64_t *o, uint64_t *inp, uint64_t *tmp, uint32_t n1)
{
  fsqr0(o, inp, tmp);
  for (uint32_t i = (uint32_t)0U; i < n1 - (uint32_t)1U; i++)
  {
    fsqr0(o, o, tmp);
  }
}

static void finv(uint64_t *o, uint64_t *i, uint64_t *tmp)
{
  uint64_t t1[16U] = { 0U };
  uint64_t *a = t1;
  uint64_t *b = t1 + (uint32_t)4U;
  uint64_t *c = t1 + (uint32_t)8U;
  uint64_t *t00 = t1 + (uint32_t)12U;
  uint64_t *tmp1 = tmp;
  fsquare_times(a, i, tmp1, (uint32_t)1U);
  fsquare_times(t00, a, tmp1, (uint32_t)2U);
  fmul0(b, t00, i, tmp);
  fmul0(a, b, a, tmp);
  fsquare_times(t00, a, tmp1, (uint32_t)1U);
  fmul0(b, t00, b, tmp);
  fsquare_times(t00, b, tmp1, (uint32_t)5U);
  fmul0(b, t00, b, tmp);
  fsquare_times(t00, b, tmp1, (uint32_t)10U);
  fmul0(c, t00, b, tmp);
  fsquare_times(t00, c, tmp1, (uint32_t)20U);
  fmul0(t00, t00, c, tmp);
  fsquare_times(t00, t00, tmp1, (uint32_t)10U);
  fmul0(b, t00, b, tmp);
  fsquare_times(t00, b, tmp1, (uint32_t)50U);
  fmul0(c, t00, b, tmp);
  fsquare_times(t00, c, tmp1, (uint32_t)100U);
  fmul0(t00, t00, c, tmp);
  fsquare_times(t00, t00, tmp1, (uint32_t)50U);
  fmul0(t00, t00, b, tmp);
  fsquare_times(t00, t00, tmp1, (uint32_t)5U);
  uint64_t *a0 = t1;
  uint64_t *t0 = t1 + (uint32_t)12U;
  fmul0(o, t0, a0, tmp);
}

static void store_felem(uint64_t *b, uint64_t *f)
{
  uint64_t f30 = f[3U];
  uint64_t top_bit0 = f30 >> (uint32_t)63U;
  f[3U] = f30 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry = add_scalar0(f, f, (uint64_t)19U * top_bit0);
  uint64_t f31 = f[3U];
  uint64_t top_bit = f31 >> (uint32_t)63U;
  f[3U] = f31 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry0 = add_scalar0(f, f, (uint64_t)19U * top_bit);
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t m0 = FStar_UInt64_gte_mask(f0, (uint64_t)0xffffffffffffffedU);
  uint64_t m1 = FStar_UInt64_eq_mask(f1, (uint64_t)0xffffffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(f2, (uint64_t)0xffffffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(f3, (uint64_t)0x7fffffffffffffffU);
  uint64_t mask = ((m0 & m1) & m2) & m3;
  uint64_t f0_ = f0 - (mask & (uint64_t)0xffffffffffffffedU);
  uint64_t f1_ = f1 - (mask & (uint64_t)0xffffffffffffffffU);
  uint64_t f2_ = f2 - (mask & (uint64_t)0xffffffffffffffffU);
  uint64_t f3_ = f3 - (mask & (uint64_t)0x7fffffffffffffffU);
  uint64_t o0 = f0_;
  uint64_t o1 = f1_;
  uint64_t o2 = f2_;
  uint64_t o3 = f3_;
  b[0U] = o0;
  b[1U] = o1;
  b[2U] = o2;
  b[3U] = o3;
}

static void encode_point(uint8_t *o, uint64_t *i)
{
  uint64_t *x = i;
  uint64_t *z = i + (uint32_t)4U;
  uint64_t tmp[4U] = { 0U };
  uint64_t u64s[4U] = { 0U };
  uint64_t tmp_w[16U] = { 0U };
  finv(tmp, z, tmp_w);
  fmul0(tmp, tmp, x, tmp_w);
  store_felem(u64s, tmp);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    store64_le(o + i0 * (uint32_t)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_64_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint64_t init1[8U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = tmp;
    uint8_t *bj = pub + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (uint64_t)0x7fffffffffffffffU;
  uint64_t *x = init1;
  uint64_t *z = init1 + (uint32_t)4U;
  z[0U] = (uint64_t)1U;
  z[1U] = (uint64_t)0U;
  z[2U] = (uint64_t)0U;
  z[3U] = (uint64_t)0U;
  x[0U] = tmp[0U];
  x[1U] = tmp[1U];
  x[2U] = tmp[2U];
  x[3U] = tmp[3U];
  montgomery_ladder(init1, priv, init1);
  encode_point(out, init1);
}

void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  uint8_t basepoint[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t *os = basepoint;
    uint8_t x = g25519[i];
    os[i] = x;
  }
  Hacl_Curve25519_64_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_64_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint8_t zeros1[32U] = { 0U };
  Hacl_Curve25519_64_scalarmult(out, priv, pub);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(out[i], zeros1[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  return !r;
}

