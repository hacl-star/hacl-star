/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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

static inline void quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  uint32_t sta = st[b];
  uint32_t stb0 = st[a];
  uint32_t std0 = st[d];
  uint32_t sta1 = sta ^ ((stb0 + std0) << 7U | (stb0 + std0) >> 25U);
  st[b] = sta1;
  uint32_t sta0 = st[c];
  uint32_t stb1 = st[b];
  uint32_t std1 = st[a];
  uint32_t sta10 = sta0 ^ ((stb1 + std1) << 9U | (stb1 + std1) >> 23U);
  st[c] = sta10;
  uint32_t sta2 = st[d];
  uint32_t stb2 = st[c];
  uint32_t std2 = st[b];
  uint32_t sta11 = sta2 ^ ((stb2 + std2) << 13U | (stb2 + std2) >> 19U);
  st[d] = sta11;
  uint32_t sta3 = st[a];
  uint32_t stb = st[d];
  uint32_t std = st[c];
  uint32_t sta12 = sta3 ^ ((stb + std) << 18U | (stb + std) >> 14U);
  st[a] = sta12;
}

static inline void double_round(uint32_t *st)
{
  quarter_round(st, 0U, 4U, 8U, 12U);
  quarter_round(st, 5U, 9U, 13U, 1U);
  quarter_round(st, 10U, 14U, 2U, 6U);
  quarter_round(st, 15U, 3U, 7U, 11U);
  quarter_round(st, 0U, 1U, 2U, 3U);
  quarter_round(st, 5U, 6U, 7U, 4U);
  quarter_round(st, 10U, 11U, 8U, 9U);
  quarter_round(st, 15U, 12U, 13U, 14U);
}

static inline void rounds(uint32_t *st)
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

static inline void salsa20_core(uint32_t *k, uint32_t *ctx, uint32_t ctr)
{
  memcpy(k, ctx, 16U * sizeof (uint32_t));
  uint32_t ctr_u32 = ctr;
  k[8U] = k[8U] + ctr_u32;
  rounds(k);
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint32_t *os = k;
    uint32_t x = k[i] + ctx[i];
    os[i] = x;);
  k[8U] = k[8U] + ctr_u32;
}

static inline void salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t *os = k32;
    uint8_t *bj = key + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t *os = n32;
    uint8_t *bj = n + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  ctx[0U] = 0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k1 = k32 + 4U;
  memcpy(ctx + 1U, k0, 4U * sizeof (uint32_t));
  ctx[5U] = 0x3320646eU;
  memcpy(ctx + 6U, n32, 2U * sizeof (uint32_t));
  ctx[8U] = 0U;
  ctx[9U] = 0U;
  ctx[10U] = 0x79622d32U;
  memcpy(ctx + 11U, k1, 4U * sizeof (uint32_t));
  ctx[15U] = 0x6b206574U;
  salsa20_core(k, ctx, 0U);
  KRML_MAYBE_FOR16(i, 0U, 16U, 1U, store32_le(out + i * 4U, k[i]););
}

static inline void
salsa20_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t *os = k32;
    uint8_t *bj = key + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t *os = n32;
    uint8_t *bj = n + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  ctx[0U] = 0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k10 = k32 + 4U;
  memcpy(ctx + 1U, k0, 4U * sizeof (uint32_t));
  ctx[5U] = 0x3320646eU;
  memcpy(ctx + 6U, n32, 2U * sizeof (uint32_t));
  ctx[8U] = ctr;
  ctx[9U] = 0U;
  ctx[10U] = 0x79622d32U;
  memcpy(ctx + 11U, k10, 4U * sizeof (uint32_t));
  ctx[15U] = 0x6b206574U;
  uint32_t k[16U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(k);
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i0 = 0U; i0 < nb; i0++)
  {
    uint8_t *uu____0 = out + i0 * 64U;
    uint8_t *uu____1 = text + i0 * 64U;
    uint32_t k1[16U] = { 0U };
    salsa20_core(k1, ctx, i0);
    uint32_t bl[16U] = { 0U };
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint8_t *bj = uu____1 + i * 4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;);
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;);
    KRML_MAYBE_FOR16(i, 0U, 16U, 1U, store32_le(uu____0 + i * 4U, bl[i]););
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____2 = out + nb * 64U;
    uint8_t plain[64U] = { 0U };
    memcpy(plain, text + nb * 64U, rem * sizeof (uint8_t));
    uint32_t k1[16U] = { 0U };
    salsa20_core(k1, ctx, nb);
    uint32_t bl[16U] = { 0U };
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint8_t *bj = plain + i * 4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;);
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;);
    KRML_MAYBE_FOR16(i, 0U, 16U, 1U, store32_le(plain + i * 4U, bl[i]););
    memcpy(uu____2, plain, rem * sizeof (uint8_t));
  }
}

static inline void
salsa20_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t *os = k32;
    uint8_t *bj = key + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t *os = n32;
    uint8_t *bj = n + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  ctx[0U] = 0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k10 = k32 + 4U;
  memcpy(ctx + 1U, k0, 4U * sizeof (uint32_t));
  ctx[5U] = 0x3320646eU;
  memcpy(ctx + 6U, n32, 2U * sizeof (uint32_t));
  ctx[8U] = ctr;
  ctx[9U] = 0U;
  ctx[10U] = 0x79622d32U;
  memcpy(ctx + 11U, k10, 4U * sizeof (uint32_t));
  ctx[15U] = 0x6b206574U;
  uint32_t k[16U] = { 0U };
  KRML_MAYBE_UNUSED_VAR(k);
  uint32_t rem = len % 64U;
  uint32_t nb = len / 64U;
  uint32_t rem1 = len % 64U;
  for (uint32_t i0 = 0U; i0 < nb; i0++)
  {
    uint8_t *uu____0 = out + i0 * 64U;
    uint8_t *uu____1 = cipher + i0 * 64U;
    uint32_t k1[16U] = { 0U };
    salsa20_core(k1, ctx, i0);
    uint32_t bl[16U] = { 0U };
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint8_t *bj = uu____1 + i * 4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;);
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;);
    KRML_MAYBE_FOR16(i, 0U, 16U, 1U, store32_le(uu____0 + i * 4U, bl[i]););
  }
  if (rem1 > 0U)
  {
    uint8_t *uu____2 = out + nb * 64U;
    uint8_t plain[64U] = { 0U };
    memcpy(plain, cipher + nb * 64U, rem * sizeof (uint8_t));
    uint32_t k1[16U] = { 0U };
    salsa20_core(k1, ctx, nb);
    uint32_t bl[16U] = { 0U };
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint8_t *bj = plain + i * 4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;);
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t *os = bl;
      uint32_t x = bl[i] ^ k1[i];
      os[i] = x;);
    KRML_MAYBE_FOR16(i, 0U, 16U, 1U, store32_le(plain + i * 4U, bl[i]););
    memcpy(uu____2, plain, rem * sizeof (uint8_t));
  }
}

static inline void hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[4U] = { 0U };
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    uint32_t *os = k32;
    uint8_t *bj = key + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint32_t *os = n32;
    uint8_t *bj = n + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  uint32_t *k0 = k32;
  uint32_t *k1 = k32 + 4U;
  ctx[0U] = 0x61707865U;
  memcpy(ctx + 1U, k0, 4U * sizeof (uint32_t));
  ctx[5U] = 0x3320646eU;
  memcpy(ctx + 6U, n32, 4U * sizeof (uint32_t));
  ctx[10U] = 0x79622d32U;
  memcpy(ctx + 11U, k1, 4U * sizeof (uint32_t));
  ctx[15U] = 0x6b206574U;
  rounds(ctx);
  uint32_t r0 = ctx[0U];
  uint32_t r1 = ctx[5U];
  uint32_t r2 = ctx[10U];
  uint32_t r3 = ctx[15U];
  uint32_t r4 = ctx[6U];
  uint32_t r5 = ctx[7U];
  uint32_t r6 = ctx[8U];
  uint32_t r7 = ctx[9U];
  uint32_t res[8U] = { r0, r1, r2, r3, r4, r5, r6, r7 };
  KRML_MAYBE_FOR8(i, 0U, 8U, 1U, store32_le(out + i * 4U, res[i]););
}

void
Hacl_Salsa20_salsa20_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  salsa20_encrypt(len, out, text, key, n, ctr);
}

void
Hacl_Salsa20_salsa20_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  salsa20_decrypt(len, out, cipher, key, n, ctr);
}

void Hacl_Salsa20_salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n)
{
  salsa20_key_block0(out, key, n);
}

void Hacl_Salsa20_hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n)
{
  hsalsa20(out, key, n);
}

