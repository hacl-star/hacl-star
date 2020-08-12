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


#include "Hacl_Chacha20_Vec32.h"

static inline void double_round_32(u32 *st)
{
  u32 std0;
  u32 std1;
  u32 std2;
  u32 std3;
  u32 std4;
  u32 std5;
  u32 std6;
  u32 std7;
  u32 std8;
  u32 std9;
  u32 std10;
  u32 std11;
  u32 std12;
  u32 std13;
  u32 std14;
  u32 std15;
  u32 std16;
  u32 std17;
  u32 std18;
  u32 std19;
  u32 std20;
  u32 std21;
  u32 std22;
  u32 std23;
  u32 std24;
  u32 std25;
  u32 std26;
  u32 std27;
  u32 std28;
  u32 std29;
  u32 std30;
  u32 std;
  st[0U] = st[0U] + st[4U];
  std0 = st[12U] ^ st[0U];
  st[12U] = std0 << (u32)16U | std0 >> ((u32)32U - (u32)16U);
  st[8U] = st[8U] + st[12U];
  std1 = st[4U] ^ st[8U];
  st[4U] = std1 << (u32)12U | std1 >> ((u32)32U - (u32)12U);
  st[0U] = st[0U] + st[4U];
  std2 = st[12U] ^ st[0U];
  st[12U] = std2 << (u32)8U | std2 >> ((u32)32U - (u32)8U);
  st[8U] = st[8U] + st[12U];
  std3 = st[4U] ^ st[8U];
  st[4U] = std3 << (u32)7U | std3 >> ((u32)32U - (u32)7U);
  st[1U] = st[1U] + st[5U];
  std4 = st[13U] ^ st[1U];
  st[13U] = std4 << (u32)16U | std4 >> ((u32)32U - (u32)16U);
  st[9U] = st[9U] + st[13U];
  std5 = st[5U] ^ st[9U];
  st[5U] = std5 << (u32)12U | std5 >> ((u32)32U - (u32)12U);
  st[1U] = st[1U] + st[5U];
  std6 = st[13U] ^ st[1U];
  st[13U] = std6 << (u32)8U | std6 >> ((u32)32U - (u32)8U);
  st[9U] = st[9U] + st[13U];
  std7 = st[5U] ^ st[9U];
  st[5U] = std7 << (u32)7U | std7 >> ((u32)32U - (u32)7U);
  st[2U] = st[2U] + st[6U];
  std8 = st[14U] ^ st[2U];
  st[14U] = std8 << (u32)16U | std8 >> ((u32)32U - (u32)16U);
  st[10U] = st[10U] + st[14U];
  std9 = st[6U] ^ st[10U];
  st[6U] = std9 << (u32)12U | std9 >> ((u32)32U - (u32)12U);
  st[2U] = st[2U] + st[6U];
  std10 = st[14U] ^ st[2U];
  st[14U] = std10 << (u32)8U | std10 >> ((u32)32U - (u32)8U);
  st[10U] = st[10U] + st[14U];
  std11 = st[6U] ^ st[10U];
  st[6U] = std11 << (u32)7U | std11 >> ((u32)32U - (u32)7U);
  st[3U] = st[3U] + st[7U];
  std12 = st[15U] ^ st[3U];
  st[15U] = std12 << (u32)16U | std12 >> ((u32)32U - (u32)16U);
  st[11U] = st[11U] + st[15U];
  std13 = st[7U] ^ st[11U];
  st[7U] = std13 << (u32)12U | std13 >> ((u32)32U - (u32)12U);
  st[3U] = st[3U] + st[7U];
  std14 = st[15U] ^ st[3U];
  st[15U] = std14 << (u32)8U | std14 >> ((u32)32U - (u32)8U);
  st[11U] = st[11U] + st[15U];
  std15 = st[7U] ^ st[11U];
  st[7U] = std15 << (u32)7U | std15 >> ((u32)32U - (u32)7U);
  st[0U] = st[0U] + st[5U];
  std16 = st[15U] ^ st[0U];
  st[15U] = std16 << (u32)16U | std16 >> ((u32)32U - (u32)16U);
  st[10U] = st[10U] + st[15U];
  std17 = st[5U] ^ st[10U];
  st[5U] = std17 << (u32)12U | std17 >> ((u32)32U - (u32)12U);
  st[0U] = st[0U] + st[5U];
  std18 = st[15U] ^ st[0U];
  st[15U] = std18 << (u32)8U | std18 >> ((u32)32U - (u32)8U);
  st[10U] = st[10U] + st[15U];
  std19 = st[5U] ^ st[10U];
  st[5U] = std19 << (u32)7U | std19 >> ((u32)32U - (u32)7U);
  st[1U] = st[1U] + st[6U];
  std20 = st[12U] ^ st[1U];
  st[12U] = std20 << (u32)16U | std20 >> ((u32)32U - (u32)16U);
  st[11U] = st[11U] + st[12U];
  std21 = st[6U] ^ st[11U];
  st[6U] = std21 << (u32)12U | std21 >> ((u32)32U - (u32)12U);
  st[1U] = st[1U] + st[6U];
  std22 = st[12U] ^ st[1U];
  st[12U] = std22 << (u32)8U | std22 >> ((u32)32U - (u32)8U);
  st[11U] = st[11U] + st[12U];
  std23 = st[6U] ^ st[11U];
  st[6U] = std23 << (u32)7U | std23 >> ((u32)32U - (u32)7U);
  st[2U] = st[2U] + st[7U];
  std24 = st[13U] ^ st[2U];
  st[13U] = std24 << (u32)16U | std24 >> ((u32)32U - (u32)16U);
  st[8U] = st[8U] + st[13U];
  std25 = st[7U] ^ st[8U];
  st[7U] = std25 << (u32)12U | std25 >> ((u32)32U - (u32)12U);
  st[2U] = st[2U] + st[7U];
  std26 = st[13U] ^ st[2U];
  st[13U] = std26 << (u32)8U | std26 >> ((u32)32U - (u32)8U);
  st[8U] = st[8U] + st[13U];
  std27 = st[7U] ^ st[8U];
  st[7U] = std27 << (u32)7U | std27 >> ((u32)32U - (u32)7U);
  st[3U] = st[3U] + st[4U];
  std28 = st[14U] ^ st[3U];
  st[14U] = std28 << (u32)16U | std28 >> ((u32)32U - (u32)16U);
  st[9U] = st[9U] + st[14U];
  std29 = st[4U] ^ st[9U];
  st[4U] = std29 << (u32)12U | std29 >> ((u32)32U - (u32)12U);
  st[3U] = st[3U] + st[4U];
  std30 = st[14U] ^ st[3U];
  st[14U] = std30 << (u32)8U | std30 >> ((u32)32U - (u32)8U);
  st[9U] = st[9U] + st[14U];
  std = st[4U] ^ st[9U];
  st[4U] = std << (u32)7U | std >> ((u32)32U - (u32)7U);
}

static inline void chacha20_core_32(u32 *k, u32 *ctx, u32 ctr)
{
  u32 ctr_u32;
  u32 cv;
  memcpy(k, ctx, (u32)16U * sizeof (u32));
  ctr_u32 = (u32)1U * ctr;
  cv = ctr_u32;
  k[12U] = k[12U] + cv;
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
    {
      u32 *os = k;
      u32 x = k[i] + ctx[i];
      os[i] = x;
    }
  }
  k[12U] = k[12U] + cv;
}

static inline void chacha20_init_32(u32 *ctx, u8 *k, u8 *n, u32 ctr)
{
  u32 ctx1[16U] = { 0U };
  u32 *uu____0 = ctx1;
  u32 *uu____1;
  u32 *uu____2;
  u32 ctr1;
  u32 c12;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)4U; i++)
    {
      u32 *os = uu____0;
      u32 x = Hacl_Impl_Chacha20_Vec_chacha20_constants[i];
      os[i] = x;
    }
  }
  uu____1 = ctx1 + (u32)4U;
  {
    u32 i;
    for (i = (u32)0U; i < (u32)8U; i++)
    {
      u32 *os = uu____1;
      u8 *bj = k + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  ctx1[12U] = ctr;
  uu____2 = ctx1 + (u32)13U;
  {
    u32 i;
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
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
    {
      u32 *os = ctx;
      u32 x = ctx1[i];
      os[i] = x;
    }
  }
  ctr1 = (u32)0U;
  c12 = ctx[12U];
  ctx[12U] = c12 + ctr1;
}

void
Hacl_Chacha20_Vec32_chacha20_encrypt_32(u32 len, u8 *out, u8 *text, u8 *key, u8 *n, u32 ctr)
{
  u32 ctx[16U] = { 0U };
  u32 rem;
  u32 nb;
  u32 rem1;
  chacha20_init_32(ctx, key, n, ctr);
  rem = len % (u32)64U;
  nb = len / (u32)64U;
  rem1 = len % (u32)64U;
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < nb; i0++)
    {
      u8 *uu____0 = out + i0 * (u32)64U;
      u8 *uu____1 = text + i0 * (u32)64U;
      u32 k[16U] = { 0U };
      chacha20_core_32(k, ctx, i0);
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u32 u = load32_le(uu____1 + i * (u32)4U);
          u32 x = u;
          u32 y = x ^ k[i];
          store32_le(uu____0 + i * (u32)4U, y);
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
      u32 k[16U] = { 0U };
      chacha20_core_32(k, ctx, nb);
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u32 u = load32_le(plain + i * (u32)4U);
          u32 x = u;
          u32 y = x ^ k[i];
          store32_le(plain + i * (u32)4U, y);
        }
      }
      memcpy(uu____2, plain, rem * sizeof (u8));
    }
  }
}

void
Hacl_Chacha20_Vec32_chacha20_decrypt_32(u32 len, u8 *out, u8 *cipher, u8 *key, u8 *n, u32 ctr)
{
  u32 ctx[16U] = { 0U };
  u32 rem;
  u32 nb;
  u32 rem1;
  chacha20_init_32(ctx, key, n, ctr);
  rem = len % (u32)64U;
  nb = len / (u32)64U;
  rem1 = len % (u32)64U;
  {
    u32 i0;
    for (i0 = (u32)0U; i0 < nb; i0++)
    {
      u8 *uu____0 = out + i0 * (u32)64U;
      u8 *uu____1 = cipher + i0 * (u32)64U;
      u32 k[16U] = { 0U };
      chacha20_core_32(k, ctx, i0);
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u32 u = load32_le(uu____1 + i * (u32)4U);
          u32 x = u;
          u32 y = x ^ k[i];
          store32_le(uu____0 + i * (u32)4U, y);
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
      u32 k[16U] = { 0U };
      chacha20_core_32(k, ctx, nb);
      {
        u32 i;
        for (i = (u32)0U; i < (u32)16U; i++)
        {
          u32 u = load32_le(plain + i * (u32)4U);
          u32 x = u;
          u32 y = x ^ k[i];
          store32_le(plain + i * (u32)4U, y);
        }
      }
      memcpy(uu____2, plain, rem * sizeof (u8));
    }
  }
}

