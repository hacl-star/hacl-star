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

inline static uint64_t
Hacl_Impl_Curve25519_Field64_Vale_add1(uint64_t *out1, uint64_t *f1, uint64_t f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  return add1_inline(out1, f1, f2);
  #else
  uint64_t scrut = add1(out1, f1, f2);
  return scrut;
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fadd(uint64_t *out1, uint64_t *f1, uint64_t *f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fadd_inline(out1, f1, f2);
  #else
  uint64_t uu____0 = fadd_(out1, f1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fsub(uint64_t *out1, uint64_t *f1, uint64_t *f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsub_inline(out1, f1, f2);
  #else
  uint64_t uu____0 = fsub_(out1, f1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fmul(
  uint64_t *out1,
  uint64_t *f1,
  uint64_t *f2,
  uint64_t *tmp
)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul_inline(tmp, f1, out1, f2);
  #else
  uint64_t uu____0 = fmul_(tmp, f1, out1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fmul2(
  uint64_t *out1,
  uint64_t *f1,
  uint64_t *f2,
  uint64_t *tmp
)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul2_inline(tmp, f1, out1, f2);
  #else
  uint64_t uu____0 = fmul2(tmp, f1, out1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fmul1(uint64_t *out1, uint64_t *f1, uint64_t f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul1_inline(out1, f1, f2);
  #else
  uint64_t uu____0 = fmul1(out1, f1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fsqr(uint64_t *out1, uint64_t *f1, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsqr_inline(tmp, f1, out1);
  #else
  uint64_t uu____0 = fsqr(tmp, f1, out1);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fsqr2(uint64_t *out1, uint64_t *f, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsqr2_inline(tmp, f, out1);
  #else
  uint64_t uu____0 = fsqr2(tmp, f, out1);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_cswap2(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  cswap2_inline(bit, p1, p2);
  #else
  uint64_t uu____0 = cswap2(bit, p1, p2);
  #endif
}

static uint8_t
Hacl_Curve25519_64_g25519[32U] =
  {
    (uint8_t)9U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U
  };

static void
Hacl_Curve25519_64_point_add_and_double(uint64_t *q, uint64_t *p01_tmp1, uint64_t *tmp2)
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
  Hacl_Impl_Curve25519_Field64_Vale_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(b, x2, z2);
  uint64_t *x3 = nq_p1;
  uint64_t *z31 = nq_p1 + (uint32_t)4U;
  uint64_t *d0 = dc;
  uint64_t *c0 = dc + (uint32_t)4U;
  Hacl_Impl_Curve25519_Field64_Vale_fadd(c0, x3, z31);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(d0, x3, z31);
  Hacl_Impl_Curve25519_Field64_Vale_fmul2(dc, dc, ab, tmp2);
  Hacl_Impl_Curve25519_Field64_Vale_fadd(x3, d0, c0);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(z31, d0, c0);
  uint64_t *a1 = tmp1;
  uint64_t *b1 = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab1 = tmp1;
  uint64_t *dc1 = tmp1 + (uint32_t)8U;
  Hacl_Impl_Curve25519_Field64_Vale_fsqr2(dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field64_Vale_fsqr2(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  Hacl_Impl_Curve25519_Field64_Vale_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field64_Vale_fmul1(b1, c, (uint64_t)121665U);
  Hacl_Impl_Curve25519_Field64_Vale_fadd(b1, b1, d);
  Hacl_Impl_Curve25519_Field64_Vale_fmul2(nq, dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(z3, z3, x1, tmp2);
}

static void Hacl_Curve25519_64_point_double(uint64_t *nq, uint64_t *tmp1, uint64_t *tmp2)
{
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  Hacl_Impl_Curve25519_Field64_Vale_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(b, x2, z2);
  Hacl_Impl_Curve25519_Field64_Vale_fsqr2(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  Hacl_Impl_Curve25519_Field64_Vale_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field64_Vale_fmul1(b, c, (uint64_t)121665U);
  Hacl_Impl_Curve25519_Field64_Vale_fadd(b, b, d);
  Hacl_Impl_Curve25519_Field64_Vale_fmul2(nq, dc, ab, tmp2);
}

static void Hacl_Curve25519_64_montgomery_ladder(uint64_t *out, uint8_t *key, uint64_t *init1)
{
  uint64_t tmp2[16U] = { 0U };
  uint64_t p01_tmp1_swap[33U] = { 0U };
  uint64_t *p0 = p01_tmp1_swap;
  uint64_t *p01 = p01_tmp1_swap;
  uint64_t *p03 = p01;
  uint64_t *p11 = p01 + (uint32_t)8U;
  memcpy(p11, init1, (uint32_t)8U * sizeof init1[0U]);
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
  Hacl_Impl_Curve25519_Field64_Vale_cswap2((uint64_t)1U, nq1, nq_p11);
  Hacl_Curve25519_64_point_add_and_double(init1, p01_tmp11, tmp2);
  swap1[0U] = (uint64_t)1U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)251U; i = i + (uint32_t)1U)
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
    Hacl_Impl_Curve25519_Field64_Vale_cswap2(sw, nq2, nq_p12);
    Hacl_Curve25519_64_point_add_and_double(init1, p01_tmp12, tmp2);
    swap2[0U] = bit;
  }
  uint64_t sw = swap1[0U];
  Hacl_Impl_Curve25519_Field64_Vale_cswap2(sw, nq1, nq_p11);
  uint64_t *nq10 = p01_tmp1;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  Hacl_Curve25519_64_point_double(nq10, tmp1, tmp2);
  Hacl_Curve25519_64_point_double(nq10, tmp1, tmp2);
  Hacl_Curve25519_64_point_double(nq10, tmp1, tmp2);
  memcpy(out, p0, (uint32_t)8U * sizeof p0[0U]);
}

static void
Hacl_Curve25519_64_fsquare_times(uint64_t *o, uint64_t *inp, uint64_t *tmp, uint32_t n1)
{
  Hacl_Impl_Curve25519_Field64_Vale_fsqr(o, inp, tmp);
  for (uint32_t i = (uint32_t)0U; i < n1 - (uint32_t)1U; i = i + (uint32_t)1U)
  {
    Hacl_Impl_Curve25519_Field64_Vale_fsqr(o, o, tmp);
  }
}

static void Hacl_Curve25519_64_finv(uint64_t *o, uint64_t *i, uint64_t *tmp)
{
  uint64_t t1[16U] = { 0U };
  uint64_t *a = t1;
  uint64_t *b = t1 + (uint32_t)4U;
  uint64_t *c = t1 + (uint32_t)8U;
  uint64_t *t00 = t1 + (uint32_t)12U;
  uint64_t *tmp1 = tmp;
  Hacl_Curve25519_64_fsquare_times(a, i, tmp1, (uint32_t)1U);
  Hacl_Curve25519_64_fsquare_times(t00, a, tmp1, (uint32_t)2U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, i, tmp);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(a, b, a, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, a, tmp1, (uint32_t)1U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, b, tmp1, (uint32_t)5U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, b, tmp1, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(c, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, c, tmp1, (uint32_t)20U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(t00, t00, c, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, t00, tmp1, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, b, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(c, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, c, tmp1, (uint32_t)100U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(t00, t00, c, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, t00, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(t00, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, t00, tmp1, (uint32_t)5U);
  uint64_t *a0 = t1;
  uint64_t *t0 = t1 + (uint32_t)12U;
  Hacl_Impl_Curve25519_Field64_Vale_fmul(o, t0, a0, tmp);
}

static void Hacl_Curve25519_64_store_felem(uint64_t *b, uint64_t *f)
{
  uint64_t f30 = f[3U];
  uint64_t top_bit0 = f30 >> (uint32_t)63U;
  f[3U] = f30 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry = Hacl_Impl_Curve25519_Field64_Vale_add1(f, f, (uint64_t)19U * top_bit0);
  uint64_t f31 = f[3U];
  uint64_t top_bit = f31 >> (uint32_t)63U;
  f[3U] = f31 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry0 = Hacl_Impl_Curve25519_Field64_Vale_add1(f, f, (uint64_t)19U * top_bit);
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

static void Hacl_Curve25519_64_encode_point(uint8_t *o, uint64_t *i)
{
  uint64_t *x = i;
  uint64_t *z = i + (uint32_t)4U;
  uint64_t tmp[4U] = { 0U };
  uint64_t u64s[4U] = { 0U };
  uint64_t tmp_w[16U] = { 0U };
  Hacl_Curve25519_64_finv(tmp, z, tmp_w);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(tmp, tmp, x, tmp_w);
  Hacl_Curve25519_64_store_felem(u64s, tmp);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0 = i0 + (uint32_t)1U)
  {
    store64_le(o + i0 * (uint32_t)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_64_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint64_t init1[8U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
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
  Hacl_Curve25519_64_montgomery_ladder(init1, priv, init1);
  Hacl_Curve25519_64_encode_point(out, init1);
}

void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  uint8_t basepoint[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
  {
    uint8_t *os = basepoint;
    uint8_t x = Hacl_Curve25519_64_g25519[i];
    os[i] = x;
  }
  Hacl_Curve25519_64_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_64_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint8_t zeros1[32U] = { 0U };
  Hacl_Curve25519_64_scalarmult(out, priv, pub);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(out[i], zeros1[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  return !r;
}

