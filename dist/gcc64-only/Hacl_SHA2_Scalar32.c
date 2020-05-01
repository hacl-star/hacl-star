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


#include "Hacl_SHA2_Scalar32.h"

static inline void sha256_update1(uint8_t *b, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (hash[0U]));
  uint8_t *b10 = b;
  uint32_t u = load32_be(b10);
  ws[0U] = u;
  uint32_t u0 = load32_be(b10 + (uint32_t)4U);
  ws[1U] = u0;
  uint32_t u1 = load32_be(b10 + (uint32_t)8U);
  ws[2U] = u1;
  uint32_t u2 = load32_be(b10 + (uint32_t)12U);
  ws[3U] = u2;
  uint32_t u3 = load32_be(b10 + (uint32_t)16U);
  ws[4U] = u3;
  uint32_t u4 = load32_be(b10 + (uint32_t)20U);
  ws[5U] = u4;
  uint32_t u5 = load32_be(b10 + (uint32_t)24U);
  ws[6U] = u5;
  uint32_t u6 = load32_be(b10 + (uint32_t)28U);
  ws[7U] = u6;
  uint32_t u7 = load32_be(b10 + (uint32_t)32U);
  ws[8U] = u7;
  uint32_t u8 = load32_be(b10 + (uint32_t)36U);
  ws[9U] = u8;
  uint32_t u9 = load32_be(b10 + (uint32_t)40U);
  ws[10U] = u9;
  uint32_t u10 = load32_be(b10 + (uint32_t)44U);
  ws[11U] = u10;
  uint32_t u11 = load32_be(b10 + (uint32_t)48U);
  ws[12U] = u11;
  uint32_t u12 = load32_be(b10 + (uint32_t)52U);
  ws[13U] = u12;
  uint32_t u13 = load32_be(b10 + (uint32_t)56U);
  ws[14U] = u13;
  uint32_t u14 = load32_be(b10 + (uint32_t)60U);
  ws[15U] = u14;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
      uint32_t ws_t = ws[i];
      uint32_t a0 = hash[0U];
      uint32_t b0 = hash[1U];
      uint32_t c0 = hash[2U];
      uint32_t d0 = hash[3U];
      uint32_t e0 = hash[4U];
      uint32_t f0 = hash[5U];
      uint32_t g0 = hash[6U];
      uint32_t h02 = hash[7U];
      uint32_t k_e_t = k_t;
      uint32_t
      t1 =
        h02
        +
          ((e0 << ((uint32_t)32U - (uint32_t)6U) | e0 >> (uint32_t)6U)
          ^
            ((e0 << ((uint32_t)32U - (uint32_t)11U) | e0 >> (uint32_t)11U)
            ^ (e0 << ((uint32_t)32U - (uint32_t)25U) | e0 >> (uint32_t)25U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint32_t
      t2 =
        ((a0 << ((uint32_t)32U - (uint32_t)2U) | a0 >> (uint32_t)2U)
        ^
          ((a0 << ((uint32_t)32U - (uint32_t)13U) | a0 >> (uint32_t)13U)
          ^ (a0 << ((uint32_t)32U - (uint32_t)22U) | a0 >> (uint32_t)22U)))
        + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
      uint32_t a1 = t1 + t2;
      uint32_t b1 = a0;
      uint32_t c1 = b0;
      uint32_t d1 = c0;
      uint32_t e1 = d0 + t1;
      uint32_t f1 = e0;
      uint32_t g1 = f0;
      uint32_t h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)4U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t t16 = ws[i];
        uint32_t t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        uint32_t t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        uint32_t t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        uint32_t
        s1 =
          (t2 << ((uint32_t)32U - (uint32_t)17U) | t2 >> (uint32_t)17U)
          ^ ((t2 << ((uint32_t)32U - (uint32_t)19U) | t2 >> (uint32_t)19U) ^ t2 >> (uint32_t)10U);
        uint32_t
        s0 =
          (t15 << ((uint32_t)32U - (uint32_t)7U) | t15 >> (uint32_t)7U)
          ^ ((t15 << ((uint32_t)32U - (uint32_t)18U) | t15 >> (uint32_t)18U) ^ t15 >> (uint32_t)3U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

void Hacl_SHA2_Scalar32_sha256(uint8_t *h, uint32_t len, uint8_t *b)
{
  uint8_t *b1 = b;
  uint8_t *h1 = h;
  uint32_t st[8U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = st;
    uint32_t x = Hacl_Impl_SHA2_Generic_h256[i];
    os[i] = x;
  }
  uint32_t rem = len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)len;
  uint32_t blocks0 = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b0 = b1;
    uint8_t *mb = b0 + i * (uint32_t)64U;
    sha256_update1(mb, st);
  }
  uint32_t rem1 = len % (uint32_t)64U;
  uint8_t *b0 = b1;
  uint8_t *lb = b0 + len - rem1;
  uint32_t blocks;
  if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)64U;
  uint8_t last[128U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = len_ << (uint32_t)3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b00 = lb;
  memcpy(last, b00, rem * sizeof (b00[0U]));
  last[rem] = (uint8_t)0x80U;
  memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (totlen_buf[0U]));
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut = { .fst = last00, .snd = last10 };
  uint8_t *l0 = scrut.fst;
  uint8_t *l1 = scrut.snd;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  K____uint8_t___uint8_t_ scrut0 = { .fst = lb0, .snd = lb1 };
  uint8_t *last0 = scrut0.fst;
  uint8_t *last1 = scrut0.snd;
  sha256_update1(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha256_update1(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)1U * (uint32_t)8U * (uint32_t)4U);
  uint8_t hbuf[(uint32_t)1U * (uint32_t)8U * (uint32_t)4U];
  memset(hbuf, 0U, (uint32_t)1U * (uint32_t)8U * (uint32_t)4U * sizeof (hbuf[0U]));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store32_be(hbuf + i * (uint32_t)4U, st[i]);
  }
  memcpy(h1, hbuf, (uint32_t)32U * sizeof (hbuf[0U]));
}

static inline void sha512_update1(uint8_t *b, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (hash[0U]));
  uint8_t *b10 = b;
  uint64_t u = load64_be(b10);
  ws[0U] = u;
  uint64_t u0 = load64_be(b10 + (uint32_t)8U);
  ws[1U] = u0;
  uint64_t u1 = load64_be(b10 + (uint32_t)16U);
  ws[2U] = u1;
  uint64_t u2 = load64_be(b10 + (uint32_t)24U);
  ws[3U] = u2;
  uint64_t u3 = load64_be(b10 + (uint32_t)32U);
  ws[4U] = u3;
  uint64_t u4 = load64_be(b10 + (uint32_t)40U);
  ws[5U] = u4;
  uint64_t u5 = load64_be(b10 + (uint32_t)48U);
  ws[6U] = u5;
  uint64_t u6 = load64_be(b10 + (uint32_t)56U);
  ws[7U] = u6;
  uint64_t u7 = load64_be(b10 + (uint32_t)64U);
  ws[8U] = u7;
  uint64_t u8 = load64_be(b10 + (uint32_t)72U);
  ws[9U] = u8;
  uint64_t u9 = load64_be(b10 + (uint32_t)80U);
  ws[10U] = u9;
  uint64_t u10 = load64_be(b10 + (uint32_t)88U);
  ws[11U] = u10;
  uint64_t u11 = load64_be(b10 + (uint32_t)96U);
  ws[12U] = u11;
  uint64_t u12 = load64_be(b10 + (uint32_t)104U);
  ws[13U] = u12;
  uint64_t u13 = load64_be(b10 + (uint32_t)112U);
  ws[14U] = u13;
  uint64_t u14 = load64_be(b10 + (uint32_t)120U);
  ws[15U] = u14;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[(uint32_t)16U * i0 + i];
      uint64_t ws_t = ws[i];
      uint64_t a0 = hash[0U];
      uint64_t b0 = hash[1U];
      uint64_t c0 = hash[2U];
      uint64_t d0 = hash[3U];
      uint64_t e0 = hash[4U];
      uint64_t f0 = hash[5U];
      uint64_t g0 = hash[6U];
      uint64_t h02 = hash[7U];
      uint64_t k_e_t = k_t;
      uint64_t
      t1 =
        h02
        +
          ((e0 << ((uint32_t)64U - (uint32_t)14U) | e0 >> (uint32_t)14U)
          ^
            ((e0 << ((uint32_t)64U - (uint32_t)18U) | e0 >> (uint32_t)18U)
            ^ (e0 << ((uint32_t)64U - (uint32_t)41U) | e0 >> (uint32_t)41U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint64_t
      t2 =
        ((a0 << ((uint32_t)64U - (uint32_t)28U) | a0 >> (uint32_t)28U)
        ^
          ((a0 << ((uint32_t)64U - (uint32_t)34U) | a0 >> (uint32_t)34U)
          ^ (a0 << ((uint32_t)64U - (uint32_t)39U) | a0 >> (uint32_t)39U)))
        + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
      uint64_t a1 = t1 + t2;
      uint64_t b1 = a0;
      uint64_t c1 = b0;
      uint64_t d1 = c0;
      uint64_t e1 = d0 + t1;
      uint64_t f1 = e0;
      uint64_t g1 = f0;
      uint64_t h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)5U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t t16 = ws[i];
        uint64_t t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        uint64_t t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        uint64_t t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        uint64_t
        s1 =
          (t2 << ((uint32_t)64U - (uint32_t)19U) | t2 >> (uint32_t)19U)
          ^ ((t2 << ((uint32_t)64U - (uint32_t)61U) | t2 >> (uint32_t)61U) ^ t2 >> (uint32_t)6U);
        uint64_t
        s0 =
          (t15 << ((uint32_t)64U - (uint32_t)1U) | t15 >> (uint32_t)1U)
          ^ ((t15 << ((uint32_t)64U - (uint32_t)8U) | t15 >> (uint32_t)8U) ^ t15 >> (uint32_t)7U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

void Hacl_SHA2_Scalar32_sha512(uint8_t *h, uint32_t len, uint8_t *b)
{
  uint8_t *b1 = b;
  uint8_t *h1 = h;
  uint64_t st[8U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = st;
    uint64_t x = Hacl_Impl_SHA2_Generic_h512[i];
    os[i] = x;
  }
  uint32_t rem = len % (uint32_t)128U;
  uint128_t len_ = (uint128_t)(uint64_t)len;
  uint32_t blocks0 = len / (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b0 = b1;
    uint8_t *mb = b0 + i * (uint32_t)128U;
    sha512_update1(mb, st);
  }
  uint32_t rem1 = len % (uint32_t)128U;
  uint8_t *b0 = b1;
  uint8_t *lb = b0 + len - rem1;
  uint32_t blocks;
  if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)128U;
  uint8_t last[256U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  uint128_t total_len_bits = len_ << (uint32_t)3U;
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b00 = lb;
  memcpy(last, b00, rem * sizeof (b00[0U]));
  last[rem] = (uint8_t)0x80U;
  memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut = { .fst = last00, .snd = last10 };
  uint8_t *l0 = scrut.fst;
  uint8_t *l1 = scrut.snd;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  K____uint8_t___uint8_t_ scrut0 = { .fst = lb0, .snd = lb1 };
  uint8_t *last0 = scrut0.fst;
  uint8_t *last1 = scrut0.snd;
  sha512_update1(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha512_update1(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)1U * (uint32_t)8U * (uint32_t)8U);
  uint8_t hbuf[(uint32_t)1U * (uint32_t)8U * (uint32_t)8U];
  memset(hbuf, 0U, (uint32_t)1U * (uint32_t)8U * (uint32_t)8U * sizeof (hbuf[0U]));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store64_be(hbuf + i * (uint32_t)8U, st[i]);
  }
  memcpy(h1, hbuf, (uint32_t)64U * sizeof (hbuf[0U]));
}

