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

#include "internal/Hacl_Chacha20.h"

static inline void double_round_32(uint32_t *st)
{
  st[0U] = st[0U] + st[4U];
  uint32_t std = st[12U] ^ st[0U];
  st[12U] = std << (uint32_t)16U | std >> ((uint32_t)32U - (uint32_t)16U);
  st[8U] = st[8U] + st[12U];
  uint32_t std0 = st[4U] ^ st[8U];
  st[4U] = std0 << (uint32_t)12U | std0 >> ((uint32_t)32U - (uint32_t)12U);
  st[0U] = st[0U] + st[4U];
  uint32_t std1 = st[12U] ^ st[0U];
  st[12U] = std1 << (uint32_t)8U | std1 >> ((uint32_t)32U - (uint32_t)8U);
  st[8U] = st[8U] + st[12U];
  uint32_t std2 = st[4U] ^ st[8U];
  st[4U] = std2 << (uint32_t)7U | std2 >> ((uint32_t)32U - (uint32_t)7U);
  st[1U] = st[1U] + st[5U];
  uint32_t std3 = st[13U] ^ st[1U];
  st[13U] = std3 << (uint32_t)16U | std3 >> ((uint32_t)32U - (uint32_t)16U);
  st[9U] = st[9U] + st[13U];
  uint32_t std4 = st[5U] ^ st[9U];
  st[5U] = std4 << (uint32_t)12U | std4 >> ((uint32_t)32U - (uint32_t)12U);
  st[1U] = st[1U] + st[5U];
  uint32_t std5 = st[13U] ^ st[1U];
  st[13U] = std5 << (uint32_t)8U | std5 >> ((uint32_t)32U - (uint32_t)8U);
  st[9U] = st[9U] + st[13U];
  uint32_t std6 = st[5U] ^ st[9U];
  st[5U] = std6 << (uint32_t)7U | std6 >> ((uint32_t)32U - (uint32_t)7U);
  st[2U] = st[2U] + st[6U];
  uint32_t std7 = st[14U] ^ st[2U];
  st[14U] = std7 << (uint32_t)16U | std7 >> ((uint32_t)32U - (uint32_t)16U);
  st[10U] = st[10U] + st[14U];
  uint32_t std8 = st[6U] ^ st[10U];
  st[6U] = std8 << (uint32_t)12U | std8 >> ((uint32_t)32U - (uint32_t)12U);
  st[2U] = st[2U] + st[6U];
  uint32_t std9 = st[14U] ^ st[2U];
  st[14U] = std9 << (uint32_t)8U | std9 >> ((uint32_t)32U - (uint32_t)8U);
  st[10U] = st[10U] + st[14U];
  uint32_t std10 = st[6U] ^ st[10U];
  st[6U] = std10 << (uint32_t)7U | std10 >> ((uint32_t)32U - (uint32_t)7U);
  st[3U] = st[3U] + st[7U];
  uint32_t std11 = st[15U] ^ st[3U];
  st[15U] = std11 << (uint32_t)16U | std11 >> ((uint32_t)32U - (uint32_t)16U);
  st[11U] = st[11U] + st[15U];
  uint32_t std12 = st[7U] ^ st[11U];
  st[7U] = std12 << (uint32_t)12U | std12 >> ((uint32_t)32U - (uint32_t)12U);
  st[3U] = st[3U] + st[7U];
  uint32_t std13 = st[15U] ^ st[3U];
  st[15U] = std13 << (uint32_t)8U | std13 >> ((uint32_t)32U - (uint32_t)8U);
  st[11U] = st[11U] + st[15U];
  uint32_t std14 = st[7U] ^ st[11U];
  st[7U] = std14 << (uint32_t)7U | std14 >> ((uint32_t)32U - (uint32_t)7U);
  st[0U] = st[0U] + st[5U];
  uint32_t std15 = st[15U] ^ st[0U];
  st[15U] = std15 << (uint32_t)16U | std15 >> ((uint32_t)32U - (uint32_t)16U);
  st[10U] = st[10U] + st[15U];
  uint32_t std16 = st[5U] ^ st[10U];
  st[5U] = std16 << (uint32_t)12U | std16 >> ((uint32_t)32U - (uint32_t)12U);
  st[0U] = st[0U] + st[5U];
  uint32_t std17 = st[15U] ^ st[0U];
  st[15U] = std17 << (uint32_t)8U | std17 >> ((uint32_t)32U - (uint32_t)8U);
  st[10U] = st[10U] + st[15U];
  uint32_t std18 = st[5U] ^ st[10U];
  st[5U] = std18 << (uint32_t)7U | std18 >> ((uint32_t)32U - (uint32_t)7U);
  st[1U] = st[1U] + st[6U];
  uint32_t std19 = st[12U] ^ st[1U];
  st[12U] = std19 << (uint32_t)16U | std19 >> ((uint32_t)32U - (uint32_t)16U);
  st[11U] = st[11U] + st[12U];
  uint32_t std20 = st[6U] ^ st[11U];
  st[6U] = std20 << (uint32_t)12U | std20 >> ((uint32_t)32U - (uint32_t)12U);
  st[1U] = st[1U] + st[6U];
  uint32_t std21 = st[12U] ^ st[1U];
  st[12U] = std21 << (uint32_t)8U | std21 >> ((uint32_t)32U - (uint32_t)8U);
  st[11U] = st[11U] + st[12U];
  uint32_t std22 = st[6U] ^ st[11U];
  st[6U] = std22 << (uint32_t)7U | std22 >> ((uint32_t)32U - (uint32_t)7U);
  st[2U] = st[2U] + st[7U];
  uint32_t std23 = st[13U] ^ st[2U];
  st[13U] = std23 << (uint32_t)16U | std23 >> ((uint32_t)32U - (uint32_t)16U);
  st[8U] = st[8U] + st[13U];
  uint32_t std24 = st[7U] ^ st[8U];
  st[7U] = std24 << (uint32_t)12U | std24 >> ((uint32_t)32U - (uint32_t)12U);
  st[2U] = st[2U] + st[7U];
  uint32_t std25 = st[13U] ^ st[2U];
  st[13U] = std25 << (uint32_t)8U | std25 >> ((uint32_t)32U - (uint32_t)8U);
  st[8U] = st[8U] + st[13U];
  uint32_t std26 = st[7U] ^ st[8U];
  st[7U] = std26 << (uint32_t)7U | std26 >> ((uint32_t)32U - (uint32_t)7U);
  st[3U] = st[3U] + st[4U];
  uint32_t std27 = st[14U] ^ st[3U];
  st[14U] = std27 << (uint32_t)16U | std27 >> ((uint32_t)32U - (uint32_t)16U);
  st[9U] = st[9U] + st[14U];
  uint32_t std28 = st[4U] ^ st[9U];
  st[4U] = std28 << (uint32_t)12U | std28 >> ((uint32_t)32U - (uint32_t)12U);
  st[3U] = st[3U] + st[4U];
  uint32_t std29 = st[14U] ^ st[3U];
  st[14U] = std29 << (uint32_t)8U | std29 >> ((uint32_t)32U - (uint32_t)8U);
  st[9U] = st[9U] + st[14U];
  uint32_t std30 = st[4U] ^ st[9U];
  st[4U] = std30 << (uint32_t)7U | std30 >> ((uint32_t)32U - (uint32_t)7U);
}

static inline void chacha20_core_32(uint32_t *k, uint32_t *ctx, uint32_t ctr)
{
  memcpy(k, ctx, (uint32_t)16U * sizeof (uint32_t));
  uint32_t ctr_u32 = (uint32_t)1U * ctr;
  uint32_t cv = ctr_u32;
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
    uint32_t *os = k;
    uint32_t x = k[0U] + ctx[0U];
    os[0U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[1U] + ctx[1U];
    os[1U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[2U] + ctx[2U];
    os[2U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[3U] + ctx[3U];
    os[3U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[4U] + ctx[4U];
    os[4U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[5U] + ctx[5U];
    os[5U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[6U] + ctx[6U];
    os[6U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[7U] + ctx[7U];
    os[7U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[8U] + ctx[8U];
    os[8U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[9U] + ctx[9U];
    os[9U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[10U] + ctx[10U];
    os[10U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[11U] + ctx[11U];
    os[11U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[12U] + ctx[12U];
    os[12U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[13U] + ctx[13U];
    os[13U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[14U] + ctx[14U];
    os[14U] = x;
  }
  {
    uint32_t *os = k;
    uint32_t x = k[15U] + ctx[15U];
    os[15U] = x;
  }
  k[12U] = k[12U] + cv;
}

static inline void chacha20_init_32(uint32_t *ctx, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  uint32_t ctx1[16U] = { 0U };
  uint32_t *uu____0 = ctx1;
  {
    uint32_t *os = uu____0;
    uint32_t x = Hacl_Impl_Chacha20_Vec_chacha20_constants[0U];
    os[0U] = x;
  }
  {
    uint32_t *os = uu____0;
    uint32_t x = Hacl_Impl_Chacha20_Vec_chacha20_constants[1U];
    os[1U] = x;
  }
  {
    uint32_t *os = uu____0;
    uint32_t x = Hacl_Impl_Chacha20_Vec_chacha20_constants[2U];
    os[2U] = x;
  }
  {
    uint32_t *os = uu____0;
    uint32_t x = Hacl_Impl_Chacha20_Vec_chacha20_constants[3U];
    os[3U] = x;
  }
  uint32_t *uu____1 = ctx1 + (uint32_t)4U;
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)0U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[0U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)1U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[1U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)2U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[2U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)3U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[3U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)4U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[4U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)5U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[5U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)6U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[6U] = x;
  }
  {
    uint32_t *os = uu____1;
    uint8_t *bj = k + (uint32_t)7U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[7U] = x;
  }
  ctx1[12U] = ctr;
  uint32_t *uu____2 = ctx1 + (uint32_t)13U;
  {
    uint32_t *os = uu____2;
    uint8_t *bj = n + (uint32_t)0U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[0U] = x;
  }
  {
    uint32_t *os = uu____2;
    uint8_t *bj = n + (uint32_t)1U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[1U] = x;
  }
  {
    uint32_t *os = uu____2;
    uint8_t *bj = n + (uint32_t)2U * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[2U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[0U];
    os[0U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[1U];
    os[1U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[2U];
    os[2U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[3U];
    os[3U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[4U];
    os[4U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[5U];
    os[5U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[6U];
    os[6U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[7U];
    os[7U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[8U];
    os[8U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[9U];
    os[9U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[10U];
    os[10U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[11U];
    os[11U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[12U];
    os[12U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[13U];
    os[13U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[14U];
    os[14U] = x;
  }
  {
    uint32_t *os = ctx;
    uint32_t x = ctx1[15U];
    os[15U] = x;
  }
  uint32_t ctr1 = (uint32_t)0U;
  uint32_t c12 = ctx[12U];
  ctx[12U] = c12 + ctr1;
}

void
Hacl_Chacha20_Vec32_chacha20_encrypt_32(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  uint32_t ctx[16U] = { 0U };
  chacha20_init_32(ctx, key, n, ctr);
  uint32_t rem = len % (uint32_t)64U;
  uint32_t nb = len / (uint32_t)64U;
  uint32_t rem1 = len % (uint32_t)64U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
  {
    uint8_t *uu____0 = out + i0 * (uint32_t)64U;
    uint8_t *uu____1 = text + i0 * (uint32_t)64U;
    uint32_t k[16U] = { 0U };
    chacha20_core_32(k, ctx, i0);
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)0U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[0U];
      store32_le(uu____0 + (uint32_t)0U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)1U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[1U];
      store32_le(uu____0 + (uint32_t)1U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)2U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[2U];
      store32_le(uu____0 + (uint32_t)2U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)3U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[3U];
      store32_le(uu____0 + (uint32_t)3U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)4U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[4U];
      store32_le(uu____0 + (uint32_t)4U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)5U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[5U];
      store32_le(uu____0 + (uint32_t)5U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)6U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[6U];
      store32_le(uu____0 + (uint32_t)6U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)7U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[7U];
      store32_le(uu____0 + (uint32_t)7U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)8U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[8U];
      store32_le(uu____0 + (uint32_t)8U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)9U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[9U];
      store32_le(uu____0 + (uint32_t)9U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)10U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[10U];
      store32_le(uu____0 + (uint32_t)10U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)11U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[11U];
      store32_le(uu____0 + (uint32_t)11U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)12U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[12U];
      store32_le(uu____0 + (uint32_t)12U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)13U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[13U];
      store32_le(uu____0 + (uint32_t)13U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)14U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[14U];
      store32_le(uu____0 + (uint32_t)14U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)15U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[15U];
      store32_le(uu____0 + (uint32_t)15U * (uint32_t)4U, y);
    }
  }
  if (rem1 > (uint32_t)0U)
  {
    uint8_t *uu____2 = out + nb * (uint32_t)64U;
    uint8_t *uu____3 = text + nb * (uint32_t)64U;
    uint8_t plain[64U] = { 0U };
    memcpy(plain, uu____3, rem * sizeof (uint8_t));
    uint32_t k[16U] = { 0U };
    chacha20_core_32(k, ctx, nb);
    {
      uint32_t u = load32_le(plain + (uint32_t)0U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[0U];
      store32_le(plain + (uint32_t)0U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)1U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[1U];
      store32_le(plain + (uint32_t)1U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)2U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[2U];
      store32_le(plain + (uint32_t)2U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)3U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[3U];
      store32_le(plain + (uint32_t)3U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)4U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[4U];
      store32_le(plain + (uint32_t)4U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)5U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[5U];
      store32_le(plain + (uint32_t)5U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)6U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[6U];
      store32_le(plain + (uint32_t)6U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)7U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[7U];
      store32_le(plain + (uint32_t)7U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)8U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[8U];
      store32_le(plain + (uint32_t)8U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)9U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[9U];
      store32_le(plain + (uint32_t)9U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)10U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[10U];
      store32_le(plain + (uint32_t)10U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)11U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[11U];
      store32_le(plain + (uint32_t)11U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)12U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[12U];
      store32_le(plain + (uint32_t)12U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)13U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[13U];
      store32_le(plain + (uint32_t)13U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)14U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[14U];
      store32_le(plain + (uint32_t)14U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)15U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[15U];
      store32_le(plain + (uint32_t)15U * (uint32_t)4U, y);
    }
    memcpy(uu____2, plain, rem * sizeof (uint8_t));
  }
}

void
Hacl_Chacha20_Vec32_chacha20_decrypt_32(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  uint32_t ctx[16U] = { 0U };
  chacha20_init_32(ctx, key, n, ctr);
  uint32_t rem = len % (uint32_t)64U;
  uint32_t nb = len / (uint32_t)64U;
  uint32_t rem1 = len % (uint32_t)64U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
  {
    uint8_t *uu____0 = out + i0 * (uint32_t)64U;
    uint8_t *uu____1 = cipher + i0 * (uint32_t)64U;
    uint32_t k[16U] = { 0U };
    chacha20_core_32(k, ctx, i0);
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)0U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[0U];
      store32_le(uu____0 + (uint32_t)0U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)1U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[1U];
      store32_le(uu____0 + (uint32_t)1U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)2U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[2U];
      store32_le(uu____0 + (uint32_t)2U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)3U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[3U];
      store32_le(uu____0 + (uint32_t)3U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)4U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[4U];
      store32_le(uu____0 + (uint32_t)4U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)5U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[5U];
      store32_le(uu____0 + (uint32_t)5U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)6U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[6U];
      store32_le(uu____0 + (uint32_t)6U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)7U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[7U];
      store32_le(uu____0 + (uint32_t)7U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)8U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[8U];
      store32_le(uu____0 + (uint32_t)8U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)9U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[9U];
      store32_le(uu____0 + (uint32_t)9U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)10U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[10U];
      store32_le(uu____0 + (uint32_t)10U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)11U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[11U];
      store32_le(uu____0 + (uint32_t)11U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)12U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[12U];
      store32_le(uu____0 + (uint32_t)12U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)13U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[13U];
      store32_le(uu____0 + (uint32_t)13U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)14U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[14U];
      store32_le(uu____0 + (uint32_t)14U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(uu____1 + (uint32_t)15U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[15U];
      store32_le(uu____0 + (uint32_t)15U * (uint32_t)4U, y);
    }
  }
  if (rem1 > (uint32_t)0U)
  {
    uint8_t *uu____2 = out + nb * (uint32_t)64U;
    uint8_t *uu____3 = cipher + nb * (uint32_t)64U;
    uint8_t plain[64U] = { 0U };
    memcpy(plain, uu____3, rem * sizeof (uint8_t));
    uint32_t k[16U] = { 0U };
    chacha20_core_32(k, ctx, nb);
    {
      uint32_t u = load32_le(plain + (uint32_t)0U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[0U];
      store32_le(plain + (uint32_t)0U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)1U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[1U];
      store32_le(plain + (uint32_t)1U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)2U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[2U];
      store32_le(plain + (uint32_t)2U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)3U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[3U];
      store32_le(plain + (uint32_t)3U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)4U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[4U];
      store32_le(plain + (uint32_t)4U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)5U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[5U];
      store32_le(plain + (uint32_t)5U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)6U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[6U];
      store32_le(plain + (uint32_t)6U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)7U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[7U];
      store32_le(plain + (uint32_t)7U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)8U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[8U];
      store32_le(plain + (uint32_t)8U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)9U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[9U];
      store32_le(plain + (uint32_t)9U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)10U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[10U];
      store32_le(plain + (uint32_t)10U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)11U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[11U];
      store32_le(plain + (uint32_t)11U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)12U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[12U];
      store32_le(plain + (uint32_t)12U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)13U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[13U];
      store32_le(plain + (uint32_t)13U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)14U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[14U];
      store32_le(plain + (uint32_t)14U * (uint32_t)4U, y);
    }
    {
      uint32_t u = load32_le(plain + (uint32_t)15U * (uint32_t)4U);
      uint32_t x = u;
      uint32_t y = x ^ k[15U];
      store32_le(plain + (uint32_t)15U * (uint32_t)4U, y);
    }
    memcpy(uu____2, plain, rem * sizeof (uint8_t));
  }
}

