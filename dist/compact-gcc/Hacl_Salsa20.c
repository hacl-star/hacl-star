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

inline static void
Hacl_Impl_Salsa20_Core32_quarter_round(
  uint32_t *st,
  uint32_t a,
  uint32_t b,
  uint32_t c,
  uint32_t d
)
{
  uint32_t sta = st[b];
  uint32_t stb0 = st[a];
  uint32_t std0 = st[d];
  uint32_t sta1 = sta ^ ((stb0 + std0) << (uint32_t)7U | (stb0 + std0) >> (uint32_t)25U);
  st[b] = sta1;
  uint32_t sta0 = st[c];
  uint32_t stb1 = st[b];
  uint32_t std1 = st[a];
  uint32_t sta10 = sta0 ^ ((stb1 + std1) << (uint32_t)9U | (stb1 + std1) >> (uint32_t)23U);
  st[c] = sta10;
  uint32_t sta2 = st[d];
  uint32_t stb2 = st[c];
  uint32_t std2 = st[b];
  uint32_t sta11 = sta2 ^ ((stb2 + std2) << (uint32_t)13U | (stb2 + std2) >> (uint32_t)19U);
  st[d] = sta11;
  uint32_t sta3 = st[a];
  uint32_t stb = st[d];
  uint32_t std = st[c];
  uint32_t sta12 = sta3 ^ ((stb + std) << (uint32_t)18U | (stb + std) >> (uint32_t)14U);
  st[a] = sta12;
}

inline static void Hacl_Impl_Salsa20_Core32_double_round(uint32_t *st)
{
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)8U,
    (uint32_t)12U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)5U,
    (uint32_t)9U,
    (uint32_t)13U,
    (uint32_t)1U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)10U,
    (uint32_t)14U,
    (uint32_t)2U,
    (uint32_t)6U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)15U,
    (uint32_t)3U,
    (uint32_t)7U,
    (uint32_t)11U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)0U,
    (uint32_t)1U,
    (uint32_t)2U,
    (uint32_t)3U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)5U,
    (uint32_t)6U,
    (uint32_t)7U,
    (uint32_t)4U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)10U,
    (uint32_t)11U,
    (uint32_t)8U,
    (uint32_t)9U);
  Hacl_Impl_Salsa20_Core32_quarter_round(st,
    (uint32_t)15U,
    (uint32_t)12U,
    (uint32_t)13U,
    (uint32_t)14U);
}

inline static void Hacl_Impl_Salsa20_rounds(uint32_t *st)
{
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
  Hacl_Impl_Salsa20_Core32_double_round(st);
}

inline static void Hacl_Impl_Salsa20_salsa20_core(uint32_t *k, uint32_t *ctx, uint32_t ctr)
{
  memcpy(k, ctx, (uint32_t)16U * sizeof ctx[0U]);
  uint32_t ctr_u32 = ctr;
  k[8U] = k[8U] + ctr_u32;
  Hacl_Impl_Salsa20_rounds(k);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
  {
    uint32_t *os = k;
    uint32_t x = k[i] + ctx[i];
    os[i] = x;
  }
  k[8U] = k[8U] + ctr_u32;
}

inline static void
Hacl_Impl_Salsa20_salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n1)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i = i + (uint32_t)1U)
  {
    uint32_t *os = n32;
    uint8_t *bj = n1 + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[0U] = (uint32_t)0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k1 = k32 + (uint32_t)4U;
  memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof k0[0U]);
  ctx[5U] = (uint32_t)0x3320646eU;
  memcpy(ctx + (uint32_t)6U, n32, (uint32_t)2U * sizeof n32[0U]);
  ctx[8U] = (uint32_t)0U;
  ctx[9U] = (uint32_t)0U;
  ctx[10U] = (uint32_t)0x79622d32U;
  memcpy(ctx + (uint32_t)11U, k1, (uint32_t)4U * sizeof k1[0U]);
  ctx[15U] = (uint32_t)0x6b206574U;
  Hacl_Impl_Salsa20_salsa20_core(k, ctx, (uint32_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
  {
    store32_le(out + i * (uint32_t)4U, k[i]);
  }
}

inline static void
Hacl_Impl_Salsa20_salsa20_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n1,
  uint32_t ctr
)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i = i + (uint32_t)1U)
  {
    uint32_t *os = n32;
    uint8_t *bj = n1 + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[0U] = (uint32_t)0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k10 = k32 + (uint32_t)4U;
  memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof k0[0U]);
  ctx[5U] = (uint32_t)0x3320646eU;
  memcpy(ctx + (uint32_t)6U, n32, (uint32_t)2U * sizeof n32[0U]);
  ctx[8U] = ctr;
  ctx[9U] = (uint32_t)0U;
  ctx[10U] = (uint32_t)0x79622d32U;
  memcpy(ctx + (uint32_t)11U, k10, (uint32_t)4U * sizeof k10[0U]);
  ctx[15U] = (uint32_t)0x6b206574U;
  uint32_t k[16U] = { 0U };
  uint32_t rem1 = len % (uint32_t)64U;
  uint32_t nb = len / (uint32_t)64U;
  uint32_t rem2 = len % (uint32_t)64U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0 = i0 + (uint32_t)1U)
  {
    uint8_t *uu____0 = out + i0 * (uint32_t)64U;
    uint8_t *uu____1 = text + i0 * (uint32_t)64U;
    uint32_t k1[16U] = { 0U };
    Hacl_Impl_Salsa20_salsa20_core(k1, ctx, i0);
    uint32_t bl[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint8_t *bj = uu____1 + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      store32_le(uu____0 + i * (uint32_t)4U, bl[i]);
    }
  }
  if (rem2 > (uint32_t)0U)
  {
    uint8_t *uu____2 = out + nb * (uint32_t)64U;
    uint8_t *uu____3 = text + nb * (uint32_t)64U;
    uint8_t plain[64U] = { 0U };
    memcpy(plain, uu____3, rem1 * sizeof uu____3[0U]);
    uint32_t k1[16U] = { 0U };
    Hacl_Impl_Salsa20_salsa20_core(k1, ctx, nb);
    uint32_t bl[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint8_t *bj = plain + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      store32_le(plain + i * (uint32_t)4U, bl[i]);
    }
    memcpy(uu____2, plain, rem1 * sizeof plain[0U]);
  }
}

inline static void
Hacl_Impl_Salsa20_salsa20_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n1,
  uint32_t ctr
)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i = i + (uint32_t)1U)
  {
    uint32_t *os = n32;
    uint8_t *bj = n1 + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[0U] = (uint32_t)0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k10 = k32 + (uint32_t)4U;
  memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof k0[0U]);
  ctx[5U] = (uint32_t)0x3320646eU;
  memcpy(ctx + (uint32_t)6U, n32, (uint32_t)2U * sizeof n32[0U]);
  ctx[8U] = ctr;
  ctx[9U] = (uint32_t)0U;
  ctx[10U] = (uint32_t)0x79622d32U;
  memcpy(ctx + (uint32_t)11U, k10, (uint32_t)4U * sizeof k10[0U]);
  ctx[15U] = (uint32_t)0x6b206574U;
  uint32_t k[16U] = { 0U };
  uint32_t rem1 = len % (uint32_t)64U;
  uint32_t nb = len / (uint32_t)64U;
  uint32_t rem2 = len % (uint32_t)64U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0 = i0 + (uint32_t)1U)
  {
    uint8_t *uu____0 = out + i0 * (uint32_t)64U;
    uint8_t *uu____1 = cipher + i0 * (uint32_t)64U;
    uint32_t k1[16U] = { 0U };
    Hacl_Impl_Salsa20_salsa20_core(k1, ctx, i0);
    uint32_t bl[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint8_t *bj = uu____1 + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      store32_le(uu____0 + i * (uint32_t)4U, bl[i]);
    }
  }
  if (rem2 > (uint32_t)0U)
  {
    uint8_t *uu____2 = out + nb * (uint32_t)64U;
    uint8_t *uu____3 = cipher + nb * (uint32_t)64U;
    uint8_t plain[64U] = { 0U };
    memcpy(plain, uu____3, rem1 * sizeof uu____3[0U]);
    uint32_t k1[16U] = { 0U };
    Hacl_Impl_Salsa20_salsa20_core(k1, ctx, nb);
    uint32_t bl[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint8_t *bj = plain + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      store32_le(plain + i * (uint32_t)4U, bl[i]);
    }
    memcpy(uu____2, plain, rem1 * sizeof plain[0U]);
  }
}

inline static void Hacl_Impl_HSalsa20_hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n1)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
  {
    uint32_t *os = n32;
    uint8_t *bj = n1 + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  uint32_t *k0 = k32;
  uint32_t *k1 = k32 + (uint32_t)4U;
  ctx[0U] = (uint32_t)0x61707865U;
  memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof k0[0U]);
  ctx[5U] = (uint32_t)0x3320646eU;
  memcpy(ctx + (uint32_t)6U, n32, (uint32_t)4U * sizeof n32[0U]);
  ctx[10U] = (uint32_t)0x79622d32U;
  memcpy(ctx + (uint32_t)11U, k1, (uint32_t)4U * sizeof k1[0U]);
  ctx[15U] = (uint32_t)0x6b206574U;
  Hacl_Impl_Salsa20_rounds(ctx);
  uint32_t r0 = ctx[0U];
  uint32_t r1 = ctx[5U];
  uint32_t r2 = ctx[10U];
  uint32_t r3 = ctx[15U];
  uint32_t r4 = ctx[6U];
  uint32_t r5 = ctx[7U];
  uint32_t r6 = ctx[8U];
  uint32_t r7 = ctx[9U];
  uint32_t res[8U] = { r0, r1, r2, r3, r4, r5, r6, r7 };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i = i + (uint32_t)1U)
  {
    store32_le(out + i * (uint32_t)4U, res[i]);
  }
}

void
Hacl_Salsa20_salsa20_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n1,
  uint32_t ctr
)
{
  Hacl_Impl_Salsa20_salsa20_encrypt(len, out, text, key, n1, ctr);
}

void
Hacl_Salsa20_salsa20_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n1,
  uint32_t ctr
)
{
  Hacl_Impl_Salsa20_salsa20_decrypt(len, out, cipher, key, n1, ctr);
}

void Hacl_Salsa20_salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n1)
{
  Hacl_Impl_Salsa20_salsa20_key_block0(out, key, n1);
}

void Hacl_Salsa20_hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n1)
{
  Hacl_Impl_HSalsa20_hsalsa20(out, key, n1);
}

