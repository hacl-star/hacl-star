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


#include "Hacl_Salsa20.h"

static inline void quarter_round(u32 *st, u32 a, u32 b, u32 c, u32 d)
{
  u32 sta0 = st[b];
  u32 stb0 = st[a];
  u32 std0 = st[d];
  u32 sta10 = sta0 ^ ((stb0 + std0) << (u32)7U | (stb0 + std0) >> (u32)25U);
  u32 sta2;
  u32 stb1;
  u32 std1;
  u32 sta11;
  u32 sta3;
  u32 stb2;
  u32 std2;
  u32 sta12;
  u32 sta;
  u32 stb;
  u32 std;
  u32 sta1;
  st[b] = sta10;
  sta2 = st[c];
  stb1 = st[b];
  std1 = st[a];
  sta11 = sta2 ^ ((stb1 + std1) << (u32)9U | (stb1 + std1) >> (u32)23U);
  st[c] = sta11;
  sta3 = st[d];
  stb2 = st[c];
  std2 = st[b];
  sta12 = sta3 ^ ((stb2 + std2) << (u32)13U | (stb2 + std2) >> (u32)19U);
  st[d] = sta12;
  sta = st[a];
  stb = st[d];
  std = st[c];
  sta1 = sta ^ ((stb + std) << (u32)18U | (stb + std) >> (u32)14U);
  st[a] = sta1;
}

static inline void double_round(u32 *st)
{
  quarter_round(st, (u32)0U, (u32)4U, (u32)8U, (u32)12U);
  quarter_round(st, (u32)5U, (u32)9U, (u32)13U, (u32)1U);
  quarter_round(st, (u32)10U, (u32)14U, (u32)2U, (u32)6U);
  quarter_round(st, (u32)15U, (u32)3U, (u32)7U, (u32)11U);
  quarter_round(st, (u32)0U, (u32)1U, (u32)2U, (u32)3U);
  quarter_round(st, (u32)5U, (u32)6U, (u32)7U, (u32)4U);
  quarter_round(st, (u32)10U, (u32)11U, (u32)8U, (u32)9U);
  quarter_round(st, (u32)15U, (u32)12U, (u32)13U, (u32)14U);
}

static inline void rounds(u32 *st)
{
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
}

static inline void salsa20_core(u32 *k, u32 *ctx, u32 ctr)
{
  u32 ctr_u32;
  memcpy(k, ctx, (u32)16U * sizeof (u32));
  ctr_u32 = ctr;
  k[8U] = k[8U] + ctr_u32;
  rounds(k);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
    {
      u32 *os = k;
      u32 x = k[i] + ctx[i];
      os[i] = x;
    }
  }
  k[8U] = k[8U] + ctr_u32;
}

static inline void salsa20_key_block0(u8 *out, u8 *key, u8 *n)
{
  u32 ctx[16U] = { 0U };
  u32 k[16U] = { 0U };
  u32 k32[8U] = { 0U };
  u32 n32[2U] = { 0U };
  u32 *k0;
  u32 *k1;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = k32;
      u8 *bj = key + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)2U; i++)
    {
      u32 *os = n32;
      u8 *bj = n + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  ctx[0U] = (u32)0x61707865U;
  k0 = k32;
  k1 = k32 + (u32)4U;
  memcpy(ctx + (u32)1U, k0, (u32)4U * sizeof (u32));
  ctx[5U] = (u32)0x3320646eU;
  memcpy(ctx + (u32)6U, n32, (u32)2U * sizeof (u32));
  ctx[8U] = (u32)0U;
  ctx[9U] = (u32)0U;
  ctx[10U] = (u32)0x79622d32U;
  memcpy(ctx + (u32)11U, k1, (u32)4U * sizeof (u32));
  ctx[15U] = (u32)0x6b206574U;
  salsa20_core(k, ctx, (u32)0U);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
      store32_le(out + i * (u32)4U, k[i]);
  }
}

static inline void salsa20_encrypt(u32 len, u8 *out, u8 *text, u8 *key, u8 *n, u32 ctr)
{
  u32 ctx[16U] = { 0U };
  u32 k32[8U] = { 0U };
  u32 n32[2U] = { 0U };
  u32 *k0;
  u32 *k10;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = k32;
      u8 *bj = key + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)2U; i++)
    {
      u32 *os = n32;
      u8 *bj = n + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  ctx[0U] = (u32)0x61707865U;
  k0 = k32;
  k10 = k32 + (u32)4U;
  memcpy(ctx + (u32)1U, k0, (u32)4U * sizeof (u32));
  ctx[5U] = (u32)0x3320646eU;
  memcpy(ctx + (u32)6U, n32, (u32)2U * sizeof (u32));
  ctx[8U] = ctr;
  ctx[9U] = (u32)0U;
  ctx[10U] = (u32)0x79622d32U;
  memcpy(ctx + (u32)11U, k10, (u32)4U * sizeof (u32));
  ctx[15U] = (u32)0x6b206574U;
  {
    u32 k[16U] = { 0U };
    u32 rem = len % (u32)64U;
    u32 nb = len / (u32)64U;
    u32 rem1 = len % (u32)64U;
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < nb; i0++)
      {
        u8 *uu____0 = out + i0 * (u32)64U;
        u8 *uu____1 = text + i0 * (u32)64U;
        u32 k1[16U] = { 0U };
        salsa20_core(k1, ctx, i0);
        {
          u32 bl[16U] = { 0U };
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u8 *bj = uu____1 + i * (u32)4U;
              u32 u = load32_le(bj);
              u32 r = u;
              u32 x = r;
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u32 x = bl[i] ^ k1[i];
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
              store32_le(uu____0 + i * (u32)4U, bl[i]);
          }
        }
      }
    }
    if (rem1 > (u32)0U)
    {
      u8 *uu____2 = out + nb * (u32)64U;
      u8 *uu____3 = text + nb * (u32)64U;
      u8 plain[64U] = { 0U };
      memcpy(plain, uu____3, rem * sizeof (u8));
      {
        u32 k1[16U] = { 0U };
        salsa20_core(k1, ctx, nb);
        {
          u32 bl[16U] = { 0U };
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u8 *bj = plain + i * (u32)4U;
              u32 u = load32_le(bj);
              u32 r = u;
              u32 x = r;
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u32 x = bl[i] ^ k1[i];
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
              store32_le(plain + i * (u32)4U, bl[i]);
          }
          memcpy(uu____2, plain, rem * sizeof (u8));
        }
      }
    }
  }
}

static inline void salsa20_decrypt(u32 len, u8 *out, u8 *cipher, u8 *key, u8 *n, u32 ctr)
{
  u32 ctx[16U] = { 0U };
  u32 k32[8U] = { 0U };
  u32 n32[2U] = { 0U };
  u32 *k0;
  u32 *k10;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = k32;
      u8 *bj = key + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)2U; i++)
    {
      u32 *os = n32;
      u8 *bj = n + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  ctx[0U] = (u32)0x61707865U;
  k0 = k32;
  k10 = k32 + (u32)4U;
  memcpy(ctx + (u32)1U, k0, (u32)4U * sizeof (u32));
  ctx[5U] = (u32)0x3320646eU;
  memcpy(ctx + (u32)6U, n32, (u32)2U * sizeof (u32));
  ctx[8U] = ctr;
  ctx[9U] = (u32)0U;
  ctx[10U] = (u32)0x79622d32U;
  memcpy(ctx + (u32)11U, k10, (u32)4U * sizeof (u32));
  ctx[15U] = (u32)0x6b206574U;
  {
    u32 k[16U] = { 0U };
    u32 rem = len % (u32)64U;
    u32 nb = len / (u32)64U;
    u32 rem1 = len % (u32)64U;
    {
      u32 i0;
      for (i0 = (u32)0U; i0 < nb; i0++)
      {
        u8 *uu____0 = out + i0 * (u32)64U;
        u8 *uu____1 = cipher + i0 * (u32)64U;
        u32 k1[16U] = { 0U };
        salsa20_core(k1, ctx, i0);
        {
          u32 bl[16U] = { 0U };
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u8 *bj = uu____1 + i * (u32)4U;
              u32 u = load32_le(bj);
              u32 r = u;
              u32 x = r;
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u32 x = bl[i] ^ k1[i];
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
              store32_le(uu____0 + i * (u32)4U, bl[i]);
          }
        }
      }
    }
    if (rem1 > (u32)0U)
    {
      u8 *uu____2 = out + nb * (u32)64U;
      u8 *uu____3 = cipher + nb * (u32)64U;
      u8 plain[64U] = { 0U };
      memcpy(plain, uu____3, rem * sizeof (u8));
      {
        u32 k1[16U] = { 0U };
        salsa20_core(k1, ctx, nb);
        {
          u32 bl[16U] = { 0U };
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u8 *bj = plain + i * (u32)4U;
              u32 u = load32_le(bj);
              u32 r = u;
              u32 x = r;
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 *os = bl;
              u32 x = bl[i] ^ k1[i];
              os[i] = x;
            }
          }
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
              store32_le(plain + i * (u32)4U, bl[i]);
          }
          memcpy(uu____2, plain, rem * sizeof (u8));
        }
      }
    }
  }
}

static inline void hsalsa20(u8 *out, u8 *key, u8 *n)
{
  u32 ctx[16U] = { 0U };
  u32 k32[8U] = { 0U };
  u32 n32[4U] = { 0U };
  u32 *k0;
  u32 *k1;
  u32 r0;
  u32 r1;
  u32 r2;
  u32 r3;
  u32 r4;
  u32 r5;
  u32 r6;
  u32 r7;
  u32 res[8];
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = k32;
      u8 *bj = key + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u32 *os = n32;
      u8 *bj = n + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  k0 = k32;
  k1 = k32 + (u32)4U;
  ctx[0U] = (u32)0x61707865U;
  memcpy(ctx + (u32)1U, k0, (u32)4U * sizeof (u32));
  ctx[5U] = (u32)0x3320646eU;
  memcpy(ctx + (u32)6U, n32, (u32)4U * sizeof (u32));
  ctx[10U] = (u32)0x79622d32U;
  memcpy(ctx + (u32)11U, k1, (u32)4U * sizeof (u32));
  ctx[15U] = (u32)0x6b206574U;
  rounds(ctx);
  r0 = ctx[0U];
  r1 = ctx[5U];
  r2 = ctx[10U];
  r3 = ctx[15U];
  r4 = ctx[6U];
  r5 = ctx[7U];
  r6 = ctx[8U];
  r7 = ctx[9U];
  res[0U] = r0;
  res[1U] = r1;
  res[2U] = r2;
  res[3U] = r3;
  res[4U] = r4;
  res[5U] = r5;
  res[6U] = r6;
  res[7U] = r7;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
      store32_le(out + i * (u32)4U, res[i]);
  }
}

void Hacl_Salsa20_salsa20_encrypt(u32 len, u8 *out, u8 *text, u8 *key, u8 *n, u32 ctr)
{
  salsa20_encrypt(len, out, text, key, n, ctr);
}

void Hacl_Salsa20_salsa20_decrypt(u32 len, u8 *out, u8 *cipher, u8 *key, u8 *n, u32 ctr)
{
  salsa20_decrypt(len, out, cipher, key, n, ctr);
}

void Hacl_Salsa20_salsa20_key_block0(u8 *out, u8 *key, u8 *n)
{
  salsa20_key_block0(out, key, n);
}

void Hacl_Salsa20_hsalsa20(u8 *out, u8 *key, u8 *n)
{
  hsalsa20(out, key, n);
}

