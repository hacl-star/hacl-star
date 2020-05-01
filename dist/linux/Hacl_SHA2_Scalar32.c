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

static inline void sha256_update1(u8 *b, u32 *hash)
{
  u32 hash_old[8U] = { 0U };
  u32 ws[16U] = { 0U };
  u8 *b10;
  u32 u0;
  u32 u1;
  u32 u2;
  u32 u3;
  u32 u4;
  u32 u5;
  u32 u6;
  u32 u7;
  u32 u8;
  u32 u9;
  u32 u10;
  u32 u11;
  u32 u12;
  u32 u13;
  u32 u14;
  u32 u;
  memcpy(hash_old, hash, (u32)8U * sizeof (hash[0U]));
  b10 = b;
  u0 = load32_be(b10);
  ws[0U] = u0;
  u1 = load32_be(b10 + (u32)4U);
  ws[1U] = u1;
  u2 = load32_be(b10 + (u32)8U);
  ws[2U] = u2;
  u3 = load32_be(b10 + (u32)12U);
  ws[3U] = u3;
  u4 = load32_be(b10 + (u32)16U);
  ws[4U] = u4;
  u5 = load32_be(b10 + (u32)20U);
  ws[5U] = u5;
  u6 = load32_be(b10 + (u32)24U);
  ws[6U] = u6;
  u7 = load32_be(b10 + (u32)28U);
  ws[7U] = u7;
  u8 = load32_be(b10 + (u32)32U);
  ws[8U] = u8;
  u9 = load32_be(b10 + (u32)36U);
  ws[9U] = u9;
  u10 = load32_be(b10 + (u32)40U);
  ws[10U] = u10;
  u11 = load32_be(b10 + (u32)44U);
  ws[11U] = u11;
  u12 = load32_be(b10 + (u32)48U);
  ws[12U] = u12;
  u13 = load32_be(b10 + (u32)52U);
  ws[13U] = u13;
  u14 = load32_be(b10 + (u32)56U);
  ws[14U] = u14;
  u = load32_be(b10 + (u32)60U);
  ws[15U] = u;
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
    {
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u32 k_t = Hacl_Impl_SHA2_Generic_k224_256[(u32)16U * i0 + i];
          u32 ws_t = ws[i];
          u32 a0 = hash[0U];
          u32 b0 = hash[1U];
          u32 c0 = hash[2U];
          u32 d0 = hash[3U];
          u32 e0 = hash[4U];
          u32 f0 = hash[5U];
          u32 g0 = hash[6U];
          u32 h02 = hash[7U];
          u32 k_e_t = k_t;
          u32
          t1 =
            h02
            +
              ((e0 << ((u32)32U - (u32)6U) | e0 >> (u32)6U)
              ^
                ((e0 << ((u32)32U - (u32)11U) | e0 >> (u32)11U)
                ^ (e0 << ((u32)32U - (u32)25U) | e0 >> (u32)25U)))
            + ((e0 & f0) ^ (~e0 & g0))
            + k_e_t
            + ws_t;
          u32
          t2 =
            ((a0 << ((u32)32U - (u32)2U) | a0 >> (u32)2U)
            ^
              ((a0 << ((u32)32U - (u32)13U) | a0 >> (u32)13U)
              ^ (a0 << ((u32)32U - (u32)22U) | a0 >> (u32)22U)))
            + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
          u32 a1 = t1 + t2;
          u32 b1 = a0;
          u32 c1 = b0;
          u32 d1 = c0;
          u32 e1 = d0 + t1;
          u32 f1 = e0;
          u32 g1 = f0;
          u32 h12 = g0;
          hash[0U] = a1;
          hash[1U] = b1;
          hash[2U] = c1;
          hash[3U] = d1;
          hash[4U] = e1;
          hash[5U] = f1;
          hash[6U] = g1;
          hash[7U] = h12;
        }
      }
      if (i0 < (u32)4U - (u32)1U)
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u32 t16 = ws[i];
          u32 t15 = ws[(i + (u32)1U) % (u32)16U];
          u32 t7 = ws[(i + (u32)9U) % (u32)16U];
          u32 t2 = ws[(i + (u32)14U) % (u32)16U];
          u32
          s1 =
            (t2 << ((u32)32U - (u32)17U) | t2 >> (u32)17U)
            ^ ((t2 << ((u32)32U - (u32)19U) | t2 >> (u32)19U) ^ t2 >> (u32)10U);
          u32
          s0 =
            (t15 << ((u32)32U - (u32)7U) | t15 >> (u32)7U)
            ^ ((t15 << ((u32)32U - (u32)18U) | t15 >> (u32)18U) ^ t15 >> (u32)3U);
          ws[i] = s1 + t7 + s0 + t16;
        }
      }
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = hash;
      u32 x = hash[i] + hash_old[i];
      os[i] = x;
    }
  }
}

void Hacl_SHA2_Scalar32_sha256(u8 *h, u32 len, u8 *b)
{
  u8 *b1 = b;
  u8 *h1 = h;
  u32 st[8U] = { 0U };
  u32 rem;
  u64 len_;
  u32 blocks0;
  u32 rem1;
  u8 *b00;
  u8 *lb;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = st;
      u32 x = Hacl_Impl_SHA2_Generic_h256[i];
      os[i] = x;
    }
  }
  rem = len % (u32)64U;
  len_ = (u64)len;
  blocks0 = len / (u32)64U;
  {
    u32 i;
    for (i = (u32)0U; i < blocks0; i++)
    {
      u8 *b0 = b1;
      u8 *mb = b0 + i * (u32)64U;
      sha256_update1(mb, st);
    }
  }
  rem1 = len % (u32)64U;
  b00 = b1;
  lb = b00 + len - rem1;
  {
    u32 blocks;
    if (rem + (u32)8U + (u32)1U <= (u32)64U)
      blocks = (u32)1U;
    else
      blocks = (u32)2U;
    {
      u32 fin = blocks * (u32)64U;
      u8 last[128U] = { 0U };
      u8 totlen_buf[8U] = { 0U };
      u64 total_len_bits = len_ << (u32)3U;
      u8 *b0;
      u8 *last00;
      u8 *last10;
      K____u8___u8_ scrut0;
      u8 *l0;
      u8 *l1;
      u8 *lb0;
      u8 *lb1;
      K____u8___u8_ scrut;
      u8 *last0;
      u8 *last1;
      store64_be(totlen_buf, total_len_bits);
      b0 = lb;
      memcpy(last, b0, rem * sizeof (b0[0U]));
      last[rem] = (u8)0x80U;
      memcpy(last + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
      last00 = last;
      last10 = last + (u32)64U;
      scrut0 = ((K____u8___u8_){ .fst = last00, .snd = last10 });
      l0 = scrut0.fst;
      l1 = scrut0.snd;
      lb0 = l0;
      lb1 = l1;
      scrut = ((K____u8___u8_){ .fst = lb0, .snd = lb1 });
      last0 = scrut.fst;
      last1 = scrut.snd;
      sha256_update1(last0, st);
      if (blocks > (u32)1U)
        sha256_update1(last1, st);
      KRML_CHECK_SIZE(sizeof (u8), (u32)1U * (u32)8U * (u32)4U);
      {
        u8 hbuf[(u32)1U * (u32)8U * (u32)4U];
        memset(hbuf, 0U, (u32)1U * (u32)8U * (u32)4U * sizeof (hbuf[0U]));
        {
          u32 i;
          for (i = (u32)0U; i < (u32)8U; i++)
            store32_be(hbuf + i * (u32)4U, st[i]);
        }
        memcpy(h1, hbuf, (u32)32U * sizeof (hbuf[0U]));
      }
    }
  }
}

static inline void sha512_update1(u8 *b, u64 *hash)
{
  u64 hash_old[8U] = { 0U };
  u64 ws[16U] = { 0U };
  u8 *b10;
  u64 u0;
  u64 u1;
  u64 u2;
  u64 u3;
  u64 u4;
  u64 u5;
  u64 u6;
  u64 u7;
  u64 u8;
  u64 u9;
  u64 u10;
  u64 u11;
  u64 u12;
  u64 u13;
  u64 u14;
  u64 u;
  memcpy(hash_old, hash, (u32)8U * sizeof (hash[0U]));
  b10 = b;
  u0 = load64_be(b10);
  ws[0U] = u0;
  u1 = load64_be(b10 + (u32)8U);
  ws[1U] = u1;
  u2 = load64_be(b10 + (u32)16U);
  ws[2U] = u2;
  u3 = load64_be(b10 + (u32)24U);
  ws[3U] = u3;
  u4 = load64_be(b10 + (u32)32U);
  ws[4U] = u4;
  u5 = load64_be(b10 + (u32)40U);
  ws[5U] = u5;
  u6 = load64_be(b10 + (u32)48U);
  ws[6U] = u6;
  u7 = load64_be(b10 + (u32)56U);
  ws[7U] = u7;
  u8 = load64_be(b10 + (u32)64U);
  ws[8U] = u8;
  u9 = load64_be(b10 + (u32)72U);
  ws[9U] = u9;
  u10 = load64_be(b10 + (u32)80U);
  ws[10U] = u10;
  u11 = load64_be(b10 + (u32)88U);
  ws[11U] = u11;
  u12 = load64_be(b10 + (u32)96U);
  ws[12U] = u12;
  u13 = load64_be(b10 + (u32)104U);
  ws[13U] = u13;
  u14 = load64_be(b10 + (u32)112U);
  ws[14U] = u14;
  u = load64_be(b10 + (u32)120U);
  ws[15U] = u;
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)5U; i0++)
    {
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u64 k_t = Hacl_Impl_SHA2_Generic_k384_512[(u32)16U * i0 + i];
          u64 ws_t = ws[i];
          u64 a0 = hash[0U];
          u64 b0 = hash[1U];
          u64 c0 = hash[2U];
          u64 d0 = hash[3U];
          u64 e0 = hash[4U];
          u64 f0 = hash[5U];
          u64 g0 = hash[6U];
          u64 h02 = hash[7U];
          u64 k_e_t = k_t;
          u64
          t1 =
            h02
            +
              ((e0 << ((u32)64U - (u32)14U) | e0 >> (u32)14U)
              ^
                ((e0 << ((u32)64U - (u32)18U) | e0 >> (u32)18U)
                ^ (e0 << ((u32)64U - (u32)41U) | e0 >> (u32)41U)))
            + ((e0 & f0) ^ (~e0 & g0))
            + k_e_t
            + ws_t;
          u64
          t2 =
            ((a0 << ((u32)64U - (u32)28U) | a0 >> (u32)28U)
            ^
              ((a0 << ((u32)64U - (u32)34U) | a0 >> (u32)34U)
              ^ (a0 << ((u32)64U - (u32)39U) | a0 >> (u32)39U)))
            + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
          u64 a1 = t1 + t2;
          u64 b1 = a0;
          u64 c1 = b0;
          u64 d1 = c0;
          u64 e1 = d0 + t1;
          u64 f1 = e0;
          u64 g1 = f0;
          u64 h12 = g0;
          hash[0U] = a1;
          hash[1U] = b1;
          hash[2U] = c1;
          hash[3U] = d1;
          hash[4U] = e1;
          hash[5U] = f1;
          hash[6U] = g1;
          hash[7U] = h12;
        }
      }
      if (i0 < (u32)5U - (u32)1U)
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u64 t16 = ws[i];
          u64 t15 = ws[(i + (u32)1U) % (u32)16U];
          u64 t7 = ws[(i + (u32)9U) % (u32)16U];
          u64 t2 = ws[(i + (u32)14U) % (u32)16U];
          u64
          s1 =
            (t2 << ((u32)64U - (u32)19U) | t2 >> (u32)19U)
            ^ ((t2 << ((u32)64U - (u32)61U) | t2 >> (u32)61U) ^ t2 >> (u32)6U);
          u64
          s0 =
            (t15 << ((u32)64U - (u32)1U) | t15 >> (u32)1U)
            ^ ((t15 << ((u32)64U - (u32)8U) | t15 >> (u32)8U) ^ t15 >> (u32)7U);
          ws[i] = s1 + t7 + s0 + t16;
        }
      }
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u64 *os = hash;
      u64 x = hash[i] + hash_old[i];
      os[i] = x;
    }
  }
}

void Hacl_SHA2_Scalar32_sha512(u8 *h, u32 len, u8 *b)
{
  u8 *b1 = b;
  u8 *h1 = h;
  u64 st[8U] = { 0U };
  u32 rem;
  uint128_t len_;
  u32 blocks0;
  u32 rem1;
  u8 *b00;
  u8 *lb;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u64 *os = st;
      u64 x = Hacl_Impl_SHA2_Generic_h512[i];
      os[i] = x;
    }
  }
  rem = len % (u32)128U;
  len_ = (uint128_t)(u64)len;
  blocks0 = len / (u32)128U;
  {
    u32 i;
    for (i = (u32)0U; i < blocks0; i++)
    {
      u8 *b0 = b1;
      u8 *mb = b0 + i * (u32)128U;
      sha512_update1(mb, st);
    }
  }
  rem1 = len % (u32)128U;
  b00 = b1;
  lb = b00 + len - rem1;
  {
    u32 blocks;
    if (rem + (u32)16U + (u32)1U <= (u32)128U)
      blocks = (u32)1U;
    else
      blocks = (u32)2U;
    {
      u32 fin = blocks * (u32)128U;
      u8 last[256U] = { 0U };
      u8 totlen_buf[16U] = { 0U };
      uint128_t total_len_bits = len_ << (u32)3U;
      u8 *b0;
      u8 *last00;
      u8 *last10;
      K____u8___u8_ scrut0;
      u8 *l0;
      u8 *l1;
      u8 *lb0;
      u8 *lb1;
      K____u8___u8_ scrut;
      u8 *last0;
      u8 *last1;
      store128_be(totlen_buf, total_len_bits);
      b0 = lb;
      memcpy(last, b0, rem * sizeof (b0[0U]));
      last[rem] = (u8)0x80U;
      memcpy(last + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
      last00 = last;
      last10 = last + (u32)128U;
      scrut0 = ((K____u8___u8_){ .fst = last00, .snd = last10 });
      l0 = scrut0.fst;
      l1 = scrut0.snd;
      lb0 = l0;
      lb1 = l1;
      scrut = ((K____u8___u8_){ .fst = lb0, .snd = lb1 });
      last0 = scrut.fst;
      last1 = scrut.snd;
      sha512_update1(last0, st);
      if (blocks > (u32)1U)
        sha512_update1(last1, st);
      KRML_CHECK_SIZE(sizeof (u8), (u32)1U * (u32)8U * (u32)8U);
      {
        u8 hbuf[(u32)1U * (u32)8U * (u32)8U];
        memset(hbuf, 0U, (u32)1U * (u32)8U * (u32)8U * sizeof (hbuf[0U]));
        {
          u32 i;
          for (i = (u32)0U; i < (u32)8U; i++)
            store64_be(hbuf + i * (u32)8U, st[i]);
        }
        memcpy(h1, hbuf, (u32)64U * sizeof (hbuf[0U]));
      }
    }
  }
}

