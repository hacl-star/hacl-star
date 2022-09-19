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

#include "internal/Hacl_SHA2_Types.h"

static inline void sha224_update1(uint8_t *block, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  uint8_t *b;
  uint32_t u0;
  uint32_t u1;
  uint32_t u2;
  uint32_t u3;
  uint32_t u4;
  uint32_t u5;
  uint32_t u6;
  uint32_t u7;
  uint32_t u8;
  uint32_t u9;
  uint32_t u10;
  uint32_t u11;
  uint32_t u12;
  uint32_t u13;
  uint32_t u14;
  uint32_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint32_t));
  b = block;
  u0 = load32_be(b);
  ws[0U] = u0;
  u1 = load32_be(b + (uint32_t)4U);
  ws[1U] = u1;
  u2 = load32_be(b + (uint32_t)8U);
  ws[2U] = u2;
  u3 = load32_be(b + (uint32_t)12U);
  ws[3U] = u3;
  u4 = load32_be(b + (uint32_t)16U);
  ws[4U] = u4;
  u5 = load32_be(b + (uint32_t)20U);
  ws[5U] = u5;
  u6 = load32_be(b + (uint32_t)24U);
  ws[6U] = u6;
  u7 = load32_be(b + (uint32_t)28U);
  ws[7U] = u7;
  u8 = load32_be(b + (uint32_t)32U);
  ws[8U] = u8;
  u9 = load32_be(b + (uint32_t)36U);
  ws[9U] = u9;
  u10 = load32_be(b + (uint32_t)40U);
  ws[10U] = u10;
  u11 = load32_be(b + (uint32_t)44U);
  ws[11U] = u11;
  u12 = load32_be(b + (uint32_t)48U);
  ws[12U] = u12;
  u13 = load32_be(b + (uint32_t)52U);
  ws[13U] = u13;
  u14 = load32_be(b + (uint32_t)56U);
  ws[14U] = u14;
  u = load32_be(b + (uint32_t)60U);
  ws[15U] = u;
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)4U - (uint32_t)1U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

void Hacl_SHA2_Scalar32_sha224(uint8_t *dst, uint32_t input_len, uint8_t *input)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint32_t st[8U] = { 0U };
  uint32_t rem;
  uint64_t len_;
  uint32_t blocks0;
  uint32_t rem1;
  uint8_t *b00;
  uint8_t *lb;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = st;
    uint32_t x = Hacl_Impl_SHA2_Generic_h224[i];
    os[i] = x;);
  rem = input_len % (uint32_t)64U;
  len_ = (uint64_t)input_len;
  blocks0 = input_len / (uint32_t)64U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < blocks0; i++)
    {
      uint8_t *b0 = ib;
      uint8_t *mb = b0 + i * (uint32_t)64U;
      sha224_update1(mb, st);
    }
  }
  rem1 = input_len % (uint32_t)64U;
  b00 = ib;
  lb = b00 + input_len - rem1;
  {
    uint32_t blocks;
    if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
    {
      blocks = (uint32_t)1U;
    }
    else
    {
      blocks = (uint32_t)2U;
    }
    {
      uint32_t fin = blocks * (uint32_t)64U;
      uint8_t last[128U] = { 0U };
      uint8_t totlen_buf[8U] = { 0U };
      uint64_t total_len_bits = len_ << (uint32_t)3U;
      uint8_t *b0;
      uint8_t *last00;
      uint8_t *last10;
      store64_be(totlen_buf, total_len_bits);
      b0 = lb;
      memcpy(last, b0, rem * sizeof (uint8_t));
      last[rem] = (uint8_t)0x80U;
      memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
      last00 = last;
      last10 = last + (uint32_t)64U;
      {
        Hacl_Impl_SHA2_Types_uint8_2p lit0;
        Hacl_Impl_SHA2_Types_uint8_2p scrut0;
        uint8_t *l0;
        uint8_t *l1;
        uint8_t *lb0;
        uint8_t *lb1;
        lit0.fst = last00;
        lit0.snd = last10;
        scrut0 = lit0;
        l0 = scrut0.fst;
        l1 = scrut0.snd;
        lb0 = l0;
        lb1 = l1;
        {
          Hacl_Impl_SHA2_Types_uint8_2p lit;
          Hacl_Impl_SHA2_Types_uint8_2p scrut;
          uint8_t *last0;
          uint8_t *last1;
          lit.fst = lb0;
          lit.snd = lb1;
          scrut = lit;
          last0 = scrut.fst;
          last1 = scrut.snd;
          sha224_update1(last0, st);
          if (blocks > (uint32_t)1U)
          {
            sha224_update1(last1, st);
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)1U * (uint32_t)8U * (uint32_t)4U);
          {
            uint8_t hbuf[(uint32_t)1U * (uint32_t)8U * (uint32_t)4U];
            memset(hbuf, 0U, (uint32_t)1U * (uint32_t)8U * (uint32_t)4U * sizeof (uint8_t));
            KRML_MAYBE_FOR8(i,
              (uint32_t)0U,
              (uint32_t)8U,
              (uint32_t)1U,
              store32_be(hbuf + i * (uint32_t)4U, st[i]););
            memcpy(rb, hbuf, (uint32_t)28U * sizeof (uint8_t));
          }
        }
      }
    }
  }
}

static inline void sha256_update1(uint8_t *block, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  uint8_t *b;
  uint32_t u0;
  uint32_t u1;
  uint32_t u2;
  uint32_t u3;
  uint32_t u4;
  uint32_t u5;
  uint32_t u6;
  uint32_t u7;
  uint32_t u8;
  uint32_t u9;
  uint32_t u10;
  uint32_t u11;
  uint32_t u12;
  uint32_t u13;
  uint32_t u14;
  uint32_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint32_t));
  b = block;
  u0 = load32_be(b);
  ws[0U] = u0;
  u1 = load32_be(b + (uint32_t)4U);
  ws[1U] = u1;
  u2 = load32_be(b + (uint32_t)8U);
  ws[2U] = u2;
  u3 = load32_be(b + (uint32_t)12U);
  ws[3U] = u3;
  u4 = load32_be(b + (uint32_t)16U);
  ws[4U] = u4;
  u5 = load32_be(b + (uint32_t)20U);
  ws[5U] = u5;
  u6 = load32_be(b + (uint32_t)24U);
  ws[6U] = u6;
  u7 = load32_be(b + (uint32_t)28U);
  ws[7U] = u7;
  u8 = load32_be(b + (uint32_t)32U);
  ws[8U] = u8;
  u9 = load32_be(b + (uint32_t)36U);
  ws[9U] = u9;
  u10 = load32_be(b + (uint32_t)40U);
  ws[10U] = u10;
  u11 = load32_be(b + (uint32_t)44U);
  ws[11U] = u11;
  u12 = load32_be(b + (uint32_t)48U);
  ws[12U] = u12;
  u13 = load32_be(b + (uint32_t)52U);
  ws[13U] = u13;
  u14 = load32_be(b + (uint32_t)56U);
  ws[14U] = u14;
  u = load32_be(b + (uint32_t)60U);
  ws[15U] = u;
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)4U - (uint32_t)1U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

void Hacl_SHA2_Scalar32_sha256(uint8_t *dst, uint32_t input_len, uint8_t *input)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint32_t st[8U] = { 0U };
  uint32_t rem;
  uint64_t len_;
  uint32_t blocks0;
  uint32_t rem1;
  uint8_t *b00;
  uint8_t *lb;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint32_t *os = st;
    uint32_t x = Hacl_Impl_SHA2_Generic_h256[i];
    os[i] = x;);
  rem = input_len % (uint32_t)64U;
  len_ = (uint64_t)input_len;
  blocks0 = input_len / (uint32_t)64U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < blocks0; i++)
    {
      uint8_t *b0 = ib;
      uint8_t *mb = b0 + i * (uint32_t)64U;
      sha256_update1(mb, st);
    }
  }
  rem1 = input_len % (uint32_t)64U;
  b00 = ib;
  lb = b00 + input_len - rem1;
  {
    uint32_t blocks;
    if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
    {
      blocks = (uint32_t)1U;
    }
    else
    {
      blocks = (uint32_t)2U;
    }
    {
      uint32_t fin = blocks * (uint32_t)64U;
      uint8_t last[128U] = { 0U };
      uint8_t totlen_buf[8U] = { 0U };
      uint64_t total_len_bits = len_ << (uint32_t)3U;
      uint8_t *b0;
      uint8_t *last00;
      uint8_t *last10;
      store64_be(totlen_buf, total_len_bits);
      b0 = lb;
      memcpy(last, b0, rem * sizeof (uint8_t));
      last[rem] = (uint8_t)0x80U;
      memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
      last00 = last;
      last10 = last + (uint32_t)64U;
      {
        Hacl_Impl_SHA2_Types_uint8_2p lit0;
        Hacl_Impl_SHA2_Types_uint8_2p scrut0;
        uint8_t *l0;
        uint8_t *l1;
        uint8_t *lb0;
        uint8_t *lb1;
        lit0.fst = last00;
        lit0.snd = last10;
        scrut0 = lit0;
        l0 = scrut0.fst;
        l1 = scrut0.snd;
        lb0 = l0;
        lb1 = l1;
        {
          Hacl_Impl_SHA2_Types_uint8_2p lit;
          Hacl_Impl_SHA2_Types_uint8_2p scrut;
          uint8_t *last0;
          uint8_t *last1;
          lit.fst = lb0;
          lit.snd = lb1;
          scrut = lit;
          last0 = scrut.fst;
          last1 = scrut.snd;
          sha256_update1(last0, st);
          if (blocks > (uint32_t)1U)
          {
            sha256_update1(last1, st);
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)1U * (uint32_t)8U * (uint32_t)4U);
          {
            uint8_t hbuf[(uint32_t)1U * (uint32_t)8U * (uint32_t)4U];
            memset(hbuf, 0U, (uint32_t)1U * (uint32_t)8U * (uint32_t)4U * sizeof (uint8_t));
            KRML_MAYBE_FOR8(i,
              (uint32_t)0U,
              (uint32_t)8U,
              (uint32_t)1U,
              store32_be(hbuf + i * (uint32_t)4U, st[i]););
            memcpy(rb, hbuf, (uint32_t)32U * sizeof (uint8_t));
          }
        }
      }
    }
  }
}

static inline void sha384_update1(uint8_t *block, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  uint8_t *b;
  uint64_t u0;
  uint64_t u1;
  uint64_t u2;
  uint64_t u3;
  uint64_t u4;
  uint64_t u5;
  uint64_t u6;
  uint64_t u7;
  uint64_t u8;
  uint64_t u9;
  uint64_t u10;
  uint64_t u11;
  uint64_t u12;
  uint64_t u13;
  uint64_t u14;
  uint64_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint64_t));
  b = block;
  u0 = load64_be(b);
  ws[0U] = u0;
  u1 = load64_be(b + (uint32_t)8U);
  ws[1U] = u1;
  u2 = load64_be(b + (uint32_t)16U);
  ws[2U] = u2;
  u3 = load64_be(b + (uint32_t)24U);
  ws[3U] = u3;
  u4 = load64_be(b + (uint32_t)32U);
  ws[4U] = u4;
  u5 = load64_be(b + (uint32_t)40U);
  ws[5U] = u5;
  u6 = load64_be(b + (uint32_t)48U);
  ws[6U] = u6;
  u7 = load64_be(b + (uint32_t)56U);
  ws[7U] = u7;
  u8 = load64_be(b + (uint32_t)64U);
  ws[8U] = u8;
  u9 = load64_be(b + (uint32_t)72U);
  ws[9U] = u9;
  u10 = load64_be(b + (uint32_t)80U);
  ws[10U] = u10;
  u11 = load64_be(b + (uint32_t)88U);
  ws[11U] = u11;
  u12 = load64_be(b + (uint32_t)96U);
  ws[12U] = u12;
  u13 = load64_be(b + (uint32_t)104U);
  ws[13U] = u13;
  u14 = load64_be(b + (uint32_t)112U);
  ws[14U] = u14;
  u = load64_be(b + (uint32_t)120U);
  ws[15U] = u;
  KRML_MAYBE_FOR5(i0,
    (uint32_t)0U,
    (uint32_t)5U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)5U - (uint32_t)1U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

void Hacl_SHA2_Scalar32_sha384(uint8_t *dst, uint32_t input_len, uint8_t *input)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint64_t st[8U] = { 0U };
  uint32_t rem;
  FStar_UInt128_uint128 len_;
  uint32_t blocks0;
  uint32_t rem1;
  uint8_t *b00;
  uint8_t *lb;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t *os = st;
    uint64_t x = Hacl_Impl_SHA2_Generic_h384[i];
    os[i] = x;);
  rem = input_len % (uint32_t)128U;
  len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  blocks0 = input_len / (uint32_t)128U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < blocks0; i++)
    {
      uint8_t *b0 = ib;
      uint8_t *mb = b0 + i * (uint32_t)128U;
      sha384_update1(mb, st);
    }
  }
  rem1 = input_len % (uint32_t)128U;
  b00 = ib;
  lb = b00 + input_len - rem1;
  {
    uint32_t blocks;
    if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
    {
      blocks = (uint32_t)1U;
    }
    else
    {
      blocks = (uint32_t)2U;
    }
    {
      uint32_t fin = blocks * (uint32_t)128U;
      uint8_t last[256U] = { 0U };
      uint8_t totlen_buf[16U] = { 0U };
      FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(len_, (uint32_t)3U);
      uint8_t *b0;
      uint8_t *last00;
      uint8_t *last10;
      store128_be(totlen_buf, total_len_bits);
      b0 = lb;
      memcpy(last, b0, rem * sizeof (uint8_t));
      last[rem] = (uint8_t)0x80U;
      memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
      last00 = last;
      last10 = last + (uint32_t)128U;
      {
        Hacl_Impl_SHA2_Types_uint8_2p lit0;
        Hacl_Impl_SHA2_Types_uint8_2p scrut0;
        uint8_t *l0;
        uint8_t *l1;
        uint8_t *lb0;
        uint8_t *lb1;
        lit0.fst = last00;
        lit0.snd = last10;
        scrut0 = lit0;
        l0 = scrut0.fst;
        l1 = scrut0.snd;
        lb0 = l0;
        lb1 = l1;
        {
          Hacl_Impl_SHA2_Types_uint8_2p lit;
          Hacl_Impl_SHA2_Types_uint8_2p scrut;
          uint8_t *last0;
          uint8_t *last1;
          lit.fst = lb0;
          lit.snd = lb1;
          scrut = lit;
          last0 = scrut.fst;
          last1 = scrut.snd;
          sha384_update1(last0, st);
          if (blocks > (uint32_t)1U)
          {
            sha384_update1(last1, st);
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)1U * (uint32_t)8U * (uint32_t)8U);
          {
            uint8_t hbuf[(uint32_t)1U * (uint32_t)8U * (uint32_t)8U];
            memset(hbuf, 0U, (uint32_t)1U * (uint32_t)8U * (uint32_t)8U * sizeof (uint8_t));
            KRML_MAYBE_FOR8(i,
              (uint32_t)0U,
              (uint32_t)8U,
              (uint32_t)1U,
              store64_be(hbuf + i * (uint32_t)8U, st[i]););
            memcpy(rb, hbuf, (uint32_t)48U * sizeof (uint8_t));
          }
        }
      }
    }
  }
}

static inline void sha512_update1(uint8_t *block, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  uint8_t *b;
  uint64_t u0;
  uint64_t u1;
  uint64_t u2;
  uint64_t u3;
  uint64_t u4;
  uint64_t u5;
  uint64_t u6;
  uint64_t u7;
  uint64_t u8;
  uint64_t u9;
  uint64_t u10;
  uint64_t u11;
  uint64_t u12;
  uint64_t u13;
  uint64_t u14;
  uint64_t u;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint64_t));
  b = block;
  u0 = load64_be(b);
  ws[0U] = u0;
  u1 = load64_be(b + (uint32_t)8U);
  ws[1U] = u1;
  u2 = load64_be(b + (uint32_t)16U);
  ws[2U] = u2;
  u3 = load64_be(b + (uint32_t)24U);
  ws[3U] = u3;
  u4 = load64_be(b + (uint32_t)32U);
  ws[4U] = u4;
  u5 = load64_be(b + (uint32_t)40U);
  ws[5U] = u5;
  u6 = load64_be(b + (uint32_t)48U);
  ws[6U] = u6;
  u7 = load64_be(b + (uint32_t)56U);
  ws[7U] = u7;
  u8 = load64_be(b + (uint32_t)64U);
  ws[8U] = u8;
  u9 = load64_be(b + (uint32_t)72U);
  ws[9U] = u9;
  u10 = load64_be(b + (uint32_t)80U);
  ws[10U] = u10;
  u11 = load64_be(b + (uint32_t)88U);
  ws[11U] = u11;
  u12 = load64_be(b + (uint32_t)96U);
  ws[12U] = u12;
  u13 = load64_be(b + (uint32_t)104U);
  ws[13U] = u13;
  u14 = load64_be(b + (uint32_t)112U);
  ws[14U] = u14;
  u = load64_be(b + (uint32_t)120U);
  ws[15U] = u;
  KRML_MAYBE_FOR5(i0,
    (uint32_t)0U,
    (uint32_t)5U,
    (uint32_t)1U,
    KRML_MAYBE_FOR16(i,
      (uint32_t)0U,
      (uint32_t)16U,
      (uint32_t)1U,
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
      hash[7U] = h12;);
    if (i0 < (uint32_t)5U - (uint32_t)1U)
    {
      KRML_MAYBE_FOR16(i,
        (uint32_t)0U,
        (uint32_t)16U,
        (uint32_t)1U,
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
        ws[i] = s1 + t7 + s0 + t16;);
    });
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;);
}

void Hacl_SHA2_Scalar32_sha512(uint8_t *dst, uint32_t input_len, uint8_t *input)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint64_t st[8U] = { 0U };
  uint32_t rem;
  FStar_UInt128_uint128 len_;
  uint32_t blocks0;
  uint32_t rem1;
  uint8_t *b00;
  uint8_t *lb;
  KRML_MAYBE_FOR8(i,
    (uint32_t)0U,
    (uint32_t)8U,
    (uint32_t)1U,
    uint64_t *os = st;
    uint64_t x = Hacl_Impl_SHA2_Generic_h512[i];
    os[i] = x;);
  rem = input_len % (uint32_t)128U;
  len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  blocks0 = input_len / (uint32_t)128U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < blocks0; i++)
    {
      uint8_t *b0 = ib;
      uint8_t *mb = b0 + i * (uint32_t)128U;
      sha512_update1(mb, st);
    }
  }
  rem1 = input_len % (uint32_t)128U;
  b00 = ib;
  lb = b00 + input_len - rem1;
  {
    uint32_t blocks;
    if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
    {
      blocks = (uint32_t)1U;
    }
    else
    {
      blocks = (uint32_t)2U;
    }
    {
      uint32_t fin = blocks * (uint32_t)128U;
      uint8_t last[256U] = { 0U };
      uint8_t totlen_buf[16U] = { 0U };
      FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(len_, (uint32_t)3U);
      uint8_t *b0;
      uint8_t *last00;
      uint8_t *last10;
      store128_be(totlen_buf, total_len_bits);
      b0 = lb;
      memcpy(last, b0, rem * sizeof (uint8_t));
      last[rem] = (uint8_t)0x80U;
      memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
      last00 = last;
      last10 = last + (uint32_t)128U;
      {
        Hacl_Impl_SHA2_Types_uint8_2p lit0;
        Hacl_Impl_SHA2_Types_uint8_2p scrut0;
        uint8_t *l0;
        uint8_t *l1;
        uint8_t *lb0;
        uint8_t *lb1;
        lit0.fst = last00;
        lit0.snd = last10;
        scrut0 = lit0;
        l0 = scrut0.fst;
        l1 = scrut0.snd;
        lb0 = l0;
        lb1 = l1;
        {
          Hacl_Impl_SHA2_Types_uint8_2p lit;
          Hacl_Impl_SHA2_Types_uint8_2p scrut;
          uint8_t *last0;
          uint8_t *last1;
          lit.fst = lb0;
          lit.snd = lb1;
          scrut = lit;
          last0 = scrut.fst;
          last1 = scrut.snd;
          sha512_update1(last0, st);
          if (blocks > (uint32_t)1U)
          {
            sha512_update1(last1, st);
          }
          KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)1U * (uint32_t)8U * (uint32_t)8U);
          {
            uint8_t hbuf[(uint32_t)1U * (uint32_t)8U * (uint32_t)8U];
            memset(hbuf, 0U, (uint32_t)1U * (uint32_t)8U * (uint32_t)8U * sizeof (uint8_t));
            KRML_MAYBE_FOR8(i,
              (uint32_t)0U,
              (uint32_t)8U,
              (uint32_t)1U,
              store64_be(hbuf + i * (uint32_t)8U, st[i]););
            memcpy(rb, hbuf, (uint32_t)64U * sizeof (uint8_t));
          }
        }
      }
    }
  }
}

