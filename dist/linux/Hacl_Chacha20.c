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


#include "Hacl_Chacha20.h"

const
u32
Hacl_Impl_Chacha20_Vec_chacha20_constants[4U] =
  { (u32)0x61707865U, (u32)0x3320646eU, (u32)0x79622d32U, (u32)0x6b206574U };

static inline void quarter_round(u32 *st, u32 a, u32 b, u32 c, u32 d)
{
  u32 sta0 = st[a];
  u32 stb0 = st[b];
  u32 std0 = st[d];
  u32 sta10 = sta0 + stb0;
  u32 std10 = std0 ^ sta10;
  u32 std20 = std10 << (u32)16U | std10 >> (u32)16U;
  u32 sta2;
  u32 stb1;
  u32 std3;
  u32 sta11;
  u32 std11;
  u32 std21;
  u32 sta3;
  u32 stb2;
  u32 std4;
  u32 sta12;
  u32 std12;
  u32 std22;
  u32 sta;
  u32 stb;
  u32 std;
  u32 sta1;
  u32 std1;
  u32 std2;
  st[a] = sta10;
  st[d] = std20;
  sta2 = st[c];
  stb1 = st[d];
  std3 = st[b];
  sta11 = sta2 + stb1;
  std11 = std3 ^ sta11;
  std21 = std11 << (u32)12U | std11 >> (u32)20U;
  st[c] = sta11;
  st[b] = std21;
  sta3 = st[a];
  stb2 = st[b];
  std4 = st[d];
  sta12 = sta3 + stb2;
  std12 = std4 ^ sta12;
  std22 = std12 << (u32)8U | std12 >> (u32)24U;
  st[a] = sta12;
  st[d] = std22;
  sta = st[c];
  stb = st[d];
  std = st[b];
  sta1 = sta + stb;
  std1 = std ^ sta1;
  std2 = std1 << (u32)7U | std1 >> (u32)25U;
  st[c] = sta1;
  st[b] = std2;
}

static inline void double_round(u32 *st)
{
  quarter_round(st, (u32)0U, (u32)4U, (u32)8U, (u32)12U);
  quarter_round(st, (u32)1U, (u32)5U, (u32)9U, (u32)13U);
  quarter_round(st, (u32)2U, (u32)6U, (u32)10U, (u32)14U);
  quarter_round(st, (u32)3U, (u32)7U, (u32)11U, (u32)15U);
  quarter_round(st, (u32)0U, (u32)5U, (u32)10U, (u32)15U);
  quarter_round(st, (u32)1U, (u32)6U, (u32)11U, (u32)12U);
  quarter_round(st, (u32)2U, (u32)7U, (u32)8U, (u32)13U);
  quarter_round(st, (u32)3U, (u32)4U, (u32)9U, (u32)14U);
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

static inline void chacha20_core(u32 *k, u32 *ctx, u32 ctr)
{
  u32 ctr_u32;
  memcpy(k, ctx, (u32)16U * sizeof (u32));
  ctr_u32 = ctr;
  k[12U] = k[12U] + ctr_u32;
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
  k[12U] = k[12U] + ctr_u32;
}

static const
u32
chacha20_constants[4U] =
  { (u32)0x61707865U, (u32)0x3320646eU, (u32)0x79622d32U, (u32)0x6b206574U };

static inline void chacha20_init(u32 *ctx, u8 *k, u8 *n, u32 ctr)
{
  u32 *uu____0 = ctx;
  u32 *uu____1;
  u32 *uu____2;
  u32 i;
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)4U; i0++)
    {
      u32 *os = uu____0;
      u32 x = chacha20_constants[i0];
      os[i0] = x;
    }
  }
  uu____1 = ctx + (u32)4U;
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < (u32)8U; i0++)
    {
      u32 *os = uu____1;
      u8 *bj = k + i0 * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i0] = x;
    }
  }
  ctx[12U] = ctr;
  uu____2 = ctx + (u32)13U;
  for (i = (u32)0U; i < (u32)3U; i++)
  {
    u32 *os = uu____2;
    u8 *bj = n + i * (u32)4U;
    u32 u = load32_le(bj);
    u32 r = u;
    u32 x = r;
    os[i] = x;
  }
}

static inline void chacha20_encrypt_block(u32 *ctx, u8 *out, u32 incr, u8 *text)
{
  u32 k[16U] = { 0U };
  chacha20_core(k, ctx, incr);
  {
    u32 bl[16U] = { 0U };
    {
      u32 i;
      for (i = (u32)0U; i < (u32)16U; i++)
      {
        u32 *os = bl;
        u8 *bj = text + i * (u32)4U;
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
        u32 x = bl[i] ^ k[i];
        os[i] = x;
      }
    }
    {
      u32 i;
      for (i = (u32)0U; i < (u32)16U; i++)
        store32_le(out + i * (u32)4U, bl[i]);
    }
  }
}

static inline void chacha20_encrypt_last(u32 *ctx, u32 len, u8 *out, u32 incr, u8 *text)
{
  u8 plain[64U] = { 0U };
  memcpy(plain, text, len * sizeof (u8));
  chacha20_encrypt_block(ctx, plain, incr, plain);
  memcpy(out, plain, len * sizeof (u8));
}

static inline void chacha20_update(u32 *ctx, u32 len, u8 *out, u8 *text)
{
  u32 rem = len % (u32)64U;
  u32 nb = len / (u32)64U;
  u32 rem1 = len % (u32)64U;
  {
    u32 i;
    for (i = (u32)0U; i < nb; i++)
      chacha20_encrypt_block(ctx, out + i * (u32)64U, i, text + i * (u32)64U);
  }
  if (rem1 > (u32)0U)
    chacha20_encrypt_last(ctx, rem, out + nb * (u32)64U, nb, text + nb * (u32)64U);
}

void Hacl_Chacha20_chacha20_encrypt(u32 len, u8 *out, u8 *text, u8 *key, u8 *n, u32 ctr)
{
  u32 ctx[16U] = { 0U };
  chacha20_init(ctx, key, n, ctr);
  chacha20_update(ctx, len, out, text);
}

void Hacl_Chacha20_chacha20_decrypt(u32 len, u8 *out, u8 *cipher, u8 *key, u8 *n, u32 ctr)
{
  u32 ctx[16U] = { 0U };
  chacha20_init(ctx, key, n, ctr);
  chacha20_update(ctx, len, out, cipher);
}

