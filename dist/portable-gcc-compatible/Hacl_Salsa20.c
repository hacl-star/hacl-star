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

/* SNIPPET_START: quarter_round */

static inline void quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
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

/* SNIPPET_END: quarter_round */

/* SNIPPET_START: double_round */

static inline void double_round(uint32_t *st)
{
  quarter_round(st, (uint32_t)0U, (uint32_t)4U, (uint32_t)8U, (uint32_t)12U);
  quarter_round(st, (uint32_t)5U, (uint32_t)9U, (uint32_t)13U, (uint32_t)1U);
  quarter_round(st, (uint32_t)10U, (uint32_t)14U, (uint32_t)2U, (uint32_t)6U);
  quarter_round(st, (uint32_t)15U, (uint32_t)3U, (uint32_t)7U, (uint32_t)11U);
  quarter_round(st, (uint32_t)0U, (uint32_t)1U, (uint32_t)2U, (uint32_t)3U);
  quarter_round(st, (uint32_t)5U, (uint32_t)6U, (uint32_t)7U, (uint32_t)4U);
  quarter_round(st, (uint32_t)10U, (uint32_t)11U, (uint32_t)8U, (uint32_t)9U);
  quarter_round(st, (uint32_t)15U, (uint32_t)12U, (uint32_t)13U, (uint32_t)14U);
}

/* SNIPPET_END: double_round */

/* SNIPPET_START: rounds */

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

/* SNIPPET_END: rounds */

/* SNIPPET_START: salsa20_core */

static inline void salsa20_core(uint32_t *k, uint32_t *ctx, uint32_t ctr)
{
  memcpy(k, ctx, (uint32_t)16U * sizeof (ctx[0U]));
  uint32_t ctr_u32 = ctr;
  k[8U] = k[8U] + ctr_u32;
  rounds(k);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = k;
    uint32_t x = k[i] + ctx[i];
    os[i] = x;
  }
  k[8U] = k[8U] + ctr_u32;
}

/* SNIPPET_END: salsa20_core */

/* SNIPPET_START: salsa20_key_block0 */

static inline void salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[2U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i++)
  {
    uint32_t *os = n32;
    uint8_t *bj = n + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[0U] = (uint32_t)0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k1 = k32 + (uint32_t)4U;
  bool uu____0 = k0 == NULL;
  if (!(uu____0 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof (k0[0U]));
  }
  ctx[5U] = (uint32_t)0x3320646eU;
  bool uu____1 = n32 == NULL;
  if (!(uu____1 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)6U, n32, (uint32_t)2U * sizeof (n32[0U]));
  }
  ctx[8U] = (uint32_t)0U;
  ctx[9U] = (uint32_t)0U;
  ctx[10U] = (uint32_t)0x79622d32U;
  bool uu____2 = k1 == NULL;
  if (!(uu____2 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)11U, k1, (uint32_t)4U * sizeof (k1[0U]));
  }
  ctx[15U] = (uint32_t)0x6b206574U;
  salsa20_core(k, ctx, (uint32_t)0U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint8_t *block;
    if (out == NULL)
    {
      block = NULL;
    }
    else
    {
      block = out + i * (uint32_t)4U;
    }
    store32_le(out + i * (uint32_t)4U, k[i]);
  }
}

/* SNIPPET_END: salsa20_key_block0 */

/* SNIPPET_START: salsa20_encrypt */

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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i++)
  {
    uint32_t *os = n32;
    uint8_t *bj = n + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[0U] = (uint32_t)0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k10 = k32 + (uint32_t)4U;
  bool uu____0 = k0 == NULL;
  if (!(uu____0 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof (k0[0U]));
  }
  ctx[5U] = (uint32_t)0x3320646eU;
  bool uu____1 = n32 == NULL;
  if (!(uu____1 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)6U, n32, (uint32_t)2U * sizeof (n32[0U]));
  }
  ctx[8U] = ctr;
  ctx[9U] = (uint32_t)0U;
  ctx[10U] = (uint32_t)0x79622d32U;
  bool uu____2 = k10 == NULL;
  if (!(uu____2 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)11U, k10, (uint32_t)4U * sizeof (k10[0U]));
  }
  ctx[15U] = (uint32_t)0x6b206574U;
  uint32_t k[16U] = { 0U };
  uint32_t rem = len % (uint32_t)64U;
  if (!(len == (uint32_t)0U))
  {
    uint32_t nb = len / (uint32_t)64U;
    uint32_t rem1 = len % (uint32_t)64U;
    uint8_t *ib;
    if (text == NULL)
    {
      ib = NULL;
    }
    else
    {
      ib = text;
    }
    uint8_t *ob;
    if (out == NULL)
    {
      ob = NULL;
    }
    else
    {
      ob = out;
    }
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
    {
      uint8_t *uu____3 = out + i0 * (uint32_t)64U;
      uint8_t *uu____4 = text + i0 * (uint32_t)64U;
      uint32_t k1[16U] = { 0U };
      salsa20_core(k1, ctx, i0);
      uint32_t bl[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint8_t *bj = uu____4 + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint32_t x = bl[i] ^ k1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint8_t *block1;
        if (uu____3 == NULL)
        {
          block1 = NULL;
        }
        else
        {
          block1 = uu____3 + i * (uint32_t)4U;
        }
        store32_le(uu____3 + i * (uint32_t)4U, bl[i]);
      }
    }
    if (rem1 > (uint32_t)0U)
    {
      uint8_t *uu____5 = out + nb * (uint32_t)64U;
      uint8_t *uu____6 = text + nb * (uint32_t)64U;
      uint8_t plain[64U] = { 0U };
      bool uu____7 = uu____6 == NULL;
      if (!(uu____7 || plain == NULL))
      {
        memcpy(plain, uu____6, rem * sizeof (uu____6[0U]));
      }
      uint32_t k1[16U] = { 0U };
      salsa20_core(k1, ctx, nb);
      uint32_t bl[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint8_t *bj = plain + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint32_t x = bl[i] ^ k1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint8_t *block;
        if (plain == NULL)
        {
          block = NULL;
        }
        else
        {
          block = plain + i * (uint32_t)4U;
        }
        store32_le(plain + i * (uint32_t)4U, bl[i]);
      }
      memcpy(uu____5, plain, rem * sizeof (plain[0U]));
    }
  }
}

/* SNIPPET_END: salsa20_encrypt */

/* SNIPPET_START: salsa20_decrypt */

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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)2U; i++)
  {
    uint32_t *os = n32;
    uint8_t *bj = n + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  ctx[0U] = (uint32_t)0x61707865U;
  uint32_t *k0 = k32;
  uint32_t *k10 = k32 + (uint32_t)4U;
  bool uu____0 = k0 == NULL;
  if (!(uu____0 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof (k0[0U]));
  }
  ctx[5U] = (uint32_t)0x3320646eU;
  bool uu____1 = n32 == NULL;
  if (!(uu____1 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)6U, n32, (uint32_t)2U * sizeof (n32[0U]));
  }
  ctx[8U] = ctr;
  ctx[9U] = (uint32_t)0U;
  ctx[10U] = (uint32_t)0x79622d32U;
  bool uu____2 = k10 == NULL;
  if (!(uu____2 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)11U, k10, (uint32_t)4U * sizeof (k10[0U]));
  }
  ctx[15U] = (uint32_t)0x6b206574U;
  uint32_t k[16U] = { 0U };
  uint32_t rem = len % (uint32_t)64U;
  if (!(len == (uint32_t)0U))
  {
    uint32_t nb = len / (uint32_t)64U;
    uint32_t rem1 = len % (uint32_t)64U;
    uint8_t *ib;
    if (cipher == NULL)
    {
      ib = NULL;
    }
    else
    {
      ib = cipher;
    }
    uint8_t *ob;
    if (out == NULL)
    {
      ob = NULL;
    }
    else
    {
      ob = out;
    }
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
    {
      uint8_t *uu____3 = out + i0 * (uint32_t)64U;
      uint8_t *uu____4 = cipher + i0 * (uint32_t)64U;
      uint32_t k1[16U] = { 0U };
      salsa20_core(k1, ctx, i0);
      uint32_t bl[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint8_t *bj = uu____4 + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint32_t x = bl[i] ^ k1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint8_t *block1;
        if (uu____3 == NULL)
        {
          block1 = NULL;
        }
        else
        {
          block1 = uu____3 + i * (uint32_t)4U;
        }
        store32_le(uu____3 + i * (uint32_t)4U, bl[i]);
      }
    }
    if (rem1 > (uint32_t)0U)
    {
      uint8_t *uu____5 = out + nb * (uint32_t)64U;
      uint8_t *uu____6 = cipher + nb * (uint32_t)64U;
      uint8_t plain[64U] = { 0U };
      bool uu____7 = uu____6 == NULL;
      if (!(uu____7 || plain == NULL))
      {
        memcpy(plain, uu____6, rem * sizeof (uu____6[0U]));
      }
      uint32_t k1[16U] = { 0U };
      salsa20_core(k1, ctx, nb);
      uint32_t bl[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint8_t *bj = plain + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = bl;
        uint32_t x = bl[i] ^ k1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint8_t *block;
        if (plain == NULL)
        {
          block = NULL;
        }
        else
        {
          block = plain + i * (uint32_t)4U;
        }
        store32_le(plain + i * (uint32_t)4U, bl[i]);
      }
      memcpy(uu____5, plain, rem * sizeof (plain[0U]));
    }
  }
}

/* SNIPPET_END: salsa20_decrypt */

/* SNIPPET_START: hsalsa20 */

static inline void hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n)
{
  uint32_t ctx[16U] = { 0U };
  uint32_t k32[8U] = { 0U };
  uint32_t n32[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = k32;
    uint8_t *bj = key + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = n32;
    uint8_t *bj = n + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  uint32_t *k0 = k32;
  uint32_t *k1 = k32 + (uint32_t)4U;
  ctx[0U] = (uint32_t)0x61707865U;
  bool uu____0 = k0 == NULL;
  if (!(uu____0 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)1U, k0, (uint32_t)4U * sizeof (k0[0U]));
  }
  ctx[5U] = (uint32_t)0x3320646eU;
  bool uu____1 = n32 == NULL;
  if (!(uu____1 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)6U, n32, (uint32_t)4U * sizeof (n32[0U]));
  }
  ctx[10U] = (uint32_t)0x79622d32U;
  bool uu____2 = k1 == NULL;
  if (!(uu____2 || ctx == NULL))
  {
    memcpy(ctx + (uint32_t)11U, k1, (uint32_t)4U * sizeof (k1[0U]));
  }
  ctx[15U] = (uint32_t)0x6b206574U;
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint8_t *block;
    if (out == NULL)
    {
      block = NULL;
    }
    else
    {
      block = out + i * (uint32_t)4U;
    }
    store32_le(out + i * (uint32_t)4U, res[i]);
  }
}

/* SNIPPET_END: hsalsa20 */

/* SNIPPET_START: Hacl_Salsa20_salsa20_encrypt */

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

/* SNIPPET_END: Hacl_Salsa20_salsa20_encrypt */

/* SNIPPET_START: Hacl_Salsa20_salsa20_decrypt */

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

/* SNIPPET_END: Hacl_Salsa20_salsa20_decrypt */

/* SNIPPET_START: Hacl_Salsa20_salsa20_key_block0 */

void Hacl_Salsa20_salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n)
{
  salsa20_key_block0(out, key, n);
}

/* SNIPPET_END: Hacl_Salsa20_salsa20_key_block0 */

/* SNIPPET_START: Hacl_Salsa20_hsalsa20 */

void Hacl_Salsa20_hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n)
{
  hsalsa20(out, key, n);
}

/* SNIPPET_END: Hacl_Salsa20_hsalsa20 */

