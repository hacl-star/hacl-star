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


#include "Hacl_Gf128_PreComp.h"

#include "internal/Hacl_Gf128_NI.h"

/* SNIPPET_START: Hacl_Gf128_PreComp_gcm_init */

void Hacl_Gf128_PreComp_gcm_init(uint64_t *ctx, uint8_t *key)
{
  uint64_t *acc = ctx;
  uint64_t *pre = ctx + (uint32_t)2U;
  acc[0U] = (uint64_t)0U;
  acc[1U] = (uint64_t)0U;
  Hacl_Impl_Gf128_FieldPreComp_load_precompute_r(pre, key);
}

/* SNIPPET_END: Hacl_Gf128_PreComp_gcm_init */

/* SNIPPET_START: Hacl_Gf128_PreComp_gcm_update_blocks */

void Hacl_Gf128_PreComp_gcm_update_blocks(uint64_t *ctx, uint32_t len, uint8_t *text)
{
  uint64_t *acc = ctx;
  uint64_t *pre = ctx + (uint32_t)2U;
  uint32_t len0 = len / (uint32_t)64U * (uint32_t)64U;
  uint8_t *t0 = text;
  if (len0 > (uint32_t)0U)
  {
    uint64_t f0[8U] = { 0U };
    uint64_t *b4 = f0;
    uint64_t f[8U] = { 0U };
    uint64_t *acc4 = f;
    uint8_t *tb = t0;
    memcpy(acc4, acc, (uint32_t)2U * sizeof (uint64_t));
    uint64_t *x00 = b4;
    uint8_t *y00 = tb;
    uint64_t *x10 = b4 + (uint32_t)2U;
    uint8_t *y10 = tb + (uint32_t)16U;
    uint64_t *x20 = b4 + (uint32_t)4U;
    uint8_t *y20 = tb + (uint32_t)32U;
    uint64_t *x30 = b4 + (uint32_t)6U;
    uint8_t *y30 = tb + (uint32_t)48U;
    uint64_t u0 = load64_be(y00);
    x00[1U] = u0;
    uint64_t u1 = load64_be(y00 + (uint32_t)8U);
    x00[0U] = u1;
    uint64_t u2 = load64_be(y10);
    x10[1U] = u2;
    uint64_t u3 = load64_be(y10 + (uint32_t)8U);
    x10[0U] = u3;
    uint64_t u4 = load64_be(y20);
    x20[1U] = u4;
    uint64_t u5 = load64_be(y20 + (uint32_t)8U);
    x20[0U] = u5;
    uint64_t u6 = load64_be(y30);
    x30[1U] = u6;
    uint64_t u7 = load64_be(y30 + (uint32_t)8U);
    x30[0U] = u7;
    uint64_t *x01 = acc4;
    uint64_t *y01 = b4;
    uint64_t *x11 = acc4 + (uint32_t)2U;
    uint64_t *y11 = b4 + (uint32_t)2U;
    uint64_t *x21 = acc4 + (uint32_t)4U;
    uint64_t *y21 = b4 + (uint32_t)4U;
    uint64_t *x31 = acc4 + (uint32_t)6U;
    uint64_t *y31 = b4 + (uint32_t)6U;
    x01[0U] = x01[0U] ^ y01[0U];
    x01[1U] = x01[1U] ^ y01[1U];
    x11[0U] = x11[0U] ^ y11[0U];
    x11[1U] = x11[1U] ^ y11[1U];
    x21[0U] = x21[0U] ^ y21[0U];
    x21[1U] = x21[1U] ^ y21[1U];
    x31[0U] = x31[0U] ^ y31[0U];
    x31[1U] = x31[1U] ^ y31[1U];
    uint32_t len1 = len0 - (uint32_t)64U;
    uint8_t *text1 = t0 + (uint32_t)64U;
    uint32_t nb = len1 / (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < nb; i++)
    {
      uint8_t *tb1 = text1 + i * (uint32_t)64U;
      uint64_t *x0 = b4;
      uint8_t *y02 = tb1;
      uint64_t *x12 = b4 + (uint32_t)2U;
      uint8_t *y12 = tb1 + (uint32_t)16U;
      uint64_t *x22 = b4 + (uint32_t)4U;
      uint8_t *y22 = tb1 + (uint32_t)32U;
      uint64_t *x32 = b4 + (uint32_t)6U;
      uint8_t *y32 = tb1 + (uint32_t)48U;
      uint64_t u = load64_be(y02);
      x0[1U] = u;
      uint64_t u8 = load64_be(y02 + (uint32_t)8U);
      x0[0U] = u8;
      uint64_t u9 = load64_be(y12);
      x12[1U] = u9;
      uint64_t u10 = load64_be(y12 + (uint32_t)8U);
      x12[0U] = u10;
      uint64_t u11 = load64_be(y22);
      x22[1U] = u11;
      uint64_t u12 = load64_be(y22 + (uint32_t)8U);
      x22[0U] = u12;
      uint64_t u13 = load64_be(y32);
      x32[1U] = u13;
      uint64_t u14 = load64_be(y32 + (uint32_t)8U);
      x32[0U] = u14;
      Hacl_Impl_Gf128_FieldPreComp_fmul_r4(acc4, pre);
      uint64_t *x02 = acc4;
      uint64_t *y0 = b4;
      uint64_t *x1 = acc4 + (uint32_t)2U;
      uint64_t *y1 = b4 + (uint32_t)2U;
      uint64_t *x2 = acc4 + (uint32_t)4U;
      uint64_t *y2 = b4 + (uint32_t)4U;
      uint64_t *x3 = acc4 + (uint32_t)6U;
      uint64_t *y3 = b4 + (uint32_t)6U;
      x02[0U] = x02[0U] ^ y0[0U];
      x02[1U] = x02[1U] ^ y0[1U];
      x1[0U] = x1[0U] ^ y1[0U];
      x1[1U] = x1[1U] ^ y1[1U];
      x2[0U] = x2[0U] ^ y2[0U];
      x2[1U] = x2[1U] ^ y2[1U];
      x3[0U] = x3[0U] ^ y3[0U];
      x3[1U] = x3[1U] ^ y3[1U];
    }
    Hacl_Impl_Gf128_FieldPreComp_normalize4(acc, acc4, pre);
  }
  uint32_t len1 = len - len0;
  uint8_t *t1 = text + len0;
  uint64_t *r1 = pre + (uint32_t)6U;
  uint32_t nb = len1 / (uint32_t)16U;
  uint32_t rem = len1 % (uint32_t)16U;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *tb = t1 + i * (uint32_t)16U;
    uint64_t elem[2U] = { 0U };
    uint64_t u = load64_be(tb);
    elem[1U] = u;
    uint64_t u0 = load64_be(tb + (uint32_t)8U);
    elem[0U] = u0;
    acc[0U] = acc[0U] ^ elem[0U];
    acc[1U] = acc[1U] ^ elem[1U];
    Hacl_Impl_Gf128_FieldPreComp_fmul(acc, r1);
  }
  if (rem > (uint32_t)0U)
  {
    uint8_t *last = t1 + nb * (uint32_t)16U;
    uint64_t elem[2U] = { 0U };
    uint8_t b[16U] = { 0U };
    memcpy(b, last, rem * sizeof (uint8_t));
    uint64_t u = load64_be(b);
    elem[1U] = u;
    uint64_t u0 = load64_be(b + (uint32_t)8U);
    elem[0U] = u0;
    acc[0U] = acc[0U] ^ elem[0U];
    acc[1U] = acc[1U] ^ elem[1U];
    Hacl_Impl_Gf128_FieldPreComp_fmul(acc, r1);
    return;
  }
}

/* SNIPPET_END: Hacl_Gf128_PreComp_gcm_update_blocks */

/* SNIPPET_START: Hacl_Gf128_PreComp_gcm_update_blocks_padded */

void
(*Hacl_Gf128_PreComp_gcm_update_blocks_padded)(uint64_t *x0, uint32_t x1, uint8_t *x2) =
  Hacl_Gf128_PreComp_gcm_update_blocks;

/* SNIPPET_END: Hacl_Gf128_PreComp_gcm_update_blocks_padded */

/* SNIPPET_START: Hacl_Gf128_PreComp_gcm_emit */

void Hacl_Gf128_PreComp_gcm_emit(uint8_t *tag, uint64_t *ctx)
{
  uint64_t *acc = ctx;
  uint64_t r0 = acc[1U];
  uint64_t r1 = acc[0U];
  store64_be(tag, r0);
  store64_be(tag + (uint32_t)8U, r1);
}

/* SNIPPET_END: Hacl_Gf128_PreComp_gcm_emit */

/* SNIPPET_START: Hacl_Gf128_PreComp_ghash */

inline void Hacl_Gf128_PreComp_ghash(uint8_t *tag, uint32_t len, uint8_t *text, uint8_t *key)
{
  uint64_t ctx[266U] = { 0U };
  uint64_t *acc = ctx;
  uint64_t *pre0 = ctx + (uint32_t)2U;
  acc[0U] = (uint64_t)0U;
  acc[1U] = (uint64_t)0U;
  Hacl_Impl_Gf128_FieldPreComp_load_precompute_r(pre0, key);
  uint64_t *acc0 = ctx;
  uint64_t *pre = ctx + (uint32_t)2U;
  uint32_t len0 = len / (uint32_t)64U * (uint32_t)64U;
  uint8_t *t0 = text;
  if (len0 > (uint32_t)0U)
  {
    uint64_t f0[8U] = { 0U };
    uint64_t *b4 = f0;
    uint64_t f[8U] = { 0U };
    uint64_t *acc4 = f;
    uint8_t *tb = t0;
    memcpy(acc4, acc0, (uint32_t)2U * sizeof (uint64_t));
    uint64_t *x00 = b4;
    uint8_t *y00 = tb;
    uint64_t *x10 = b4 + (uint32_t)2U;
    uint8_t *y10 = tb + (uint32_t)16U;
    uint64_t *x20 = b4 + (uint32_t)4U;
    uint8_t *y20 = tb + (uint32_t)32U;
    uint64_t *x30 = b4 + (uint32_t)6U;
    uint8_t *y30 = tb + (uint32_t)48U;
    uint64_t u0 = load64_be(y00);
    x00[1U] = u0;
    uint64_t u1 = load64_be(y00 + (uint32_t)8U);
    x00[0U] = u1;
    uint64_t u2 = load64_be(y10);
    x10[1U] = u2;
    uint64_t u3 = load64_be(y10 + (uint32_t)8U);
    x10[0U] = u3;
    uint64_t u4 = load64_be(y20);
    x20[1U] = u4;
    uint64_t u5 = load64_be(y20 + (uint32_t)8U);
    x20[0U] = u5;
    uint64_t u6 = load64_be(y30);
    x30[1U] = u6;
    uint64_t u7 = load64_be(y30 + (uint32_t)8U);
    x30[0U] = u7;
    uint64_t *x01 = acc4;
    uint64_t *y01 = b4;
    uint64_t *x11 = acc4 + (uint32_t)2U;
    uint64_t *y11 = b4 + (uint32_t)2U;
    uint64_t *x21 = acc4 + (uint32_t)4U;
    uint64_t *y21 = b4 + (uint32_t)4U;
    uint64_t *x31 = acc4 + (uint32_t)6U;
    uint64_t *y31 = b4 + (uint32_t)6U;
    x01[0U] = x01[0U] ^ y01[0U];
    x01[1U] = x01[1U] ^ y01[1U];
    x11[0U] = x11[0U] ^ y11[0U];
    x11[1U] = x11[1U] ^ y11[1U];
    x21[0U] = x21[0U] ^ y21[0U];
    x21[1U] = x21[1U] ^ y21[1U];
    x31[0U] = x31[0U] ^ y31[0U];
    x31[1U] = x31[1U] ^ y31[1U];
    uint32_t len1 = len0 - (uint32_t)64U;
    uint8_t *text1 = t0 + (uint32_t)64U;
    uint32_t nb = len1 / (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < nb; i++)
    {
      uint8_t *tb1 = text1 + i * (uint32_t)64U;
      uint64_t *x0 = b4;
      uint8_t *y02 = tb1;
      uint64_t *x12 = b4 + (uint32_t)2U;
      uint8_t *y12 = tb1 + (uint32_t)16U;
      uint64_t *x22 = b4 + (uint32_t)4U;
      uint8_t *y22 = tb1 + (uint32_t)32U;
      uint64_t *x32 = b4 + (uint32_t)6U;
      uint8_t *y32 = tb1 + (uint32_t)48U;
      uint64_t u = load64_be(y02);
      x0[1U] = u;
      uint64_t u8 = load64_be(y02 + (uint32_t)8U);
      x0[0U] = u8;
      uint64_t u9 = load64_be(y12);
      x12[1U] = u9;
      uint64_t u10 = load64_be(y12 + (uint32_t)8U);
      x12[0U] = u10;
      uint64_t u11 = load64_be(y22);
      x22[1U] = u11;
      uint64_t u12 = load64_be(y22 + (uint32_t)8U);
      x22[0U] = u12;
      uint64_t u13 = load64_be(y32);
      x32[1U] = u13;
      uint64_t u14 = load64_be(y32 + (uint32_t)8U);
      x32[0U] = u14;
      Hacl_Impl_Gf128_FieldPreComp_fmul_r4(acc4, pre);
      uint64_t *x02 = acc4;
      uint64_t *y0 = b4;
      uint64_t *x1 = acc4 + (uint32_t)2U;
      uint64_t *y1 = b4 + (uint32_t)2U;
      uint64_t *x2 = acc4 + (uint32_t)4U;
      uint64_t *y2 = b4 + (uint32_t)4U;
      uint64_t *x3 = acc4 + (uint32_t)6U;
      uint64_t *y3 = b4 + (uint32_t)6U;
      x02[0U] = x02[0U] ^ y0[0U];
      x02[1U] = x02[1U] ^ y0[1U];
      x1[0U] = x1[0U] ^ y1[0U];
      x1[1U] = x1[1U] ^ y1[1U];
      x2[0U] = x2[0U] ^ y2[0U];
      x2[1U] = x2[1U] ^ y2[1U];
      x3[0U] = x3[0U] ^ y3[0U];
      x3[1U] = x3[1U] ^ y3[1U];
    }
    Hacl_Impl_Gf128_FieldPreComp_normalize4(acc0, acc4, pre);
  }
  uint32_t len1 = len - len0;
  uint8_t *t1 = text + len0;
  uint64_t *r10 = pre + (uint32_t)6U;
  uint32_t nb = len1 / (uint32_t)16U;
  uint32_t rem = len1 % (uint32_t)16U;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *tb = t1 + i * (uint32_t)16U;
    uint64_t elem[2U] = { 0U };
    uint64_t u = load64_be(tb);
    elem[1U] = u;
    uint64_t u0 = load64_be(tb + (uint32_t)8U);
    elem[0U] = u0;
    acc0[0U] = acc0[0U] ^ elem[0U];
    acc0[1U] = acc0[1U] ^ elem[1U];
    Hacl_Impl_Gf128_FieldPreComp_fmul(acc0, r10);
  }
  if (rem > (uint32_t)0U)
  {
    uint8_t *last = t1 + nb * (uint32_t)16U;
    uint64_t elem[2U] = { 0U };
    uint8_t b[16U] = { 0U };
    memcpy(b, last, rem * sizeof (uint8_t));
    uint64_t u = load64_be(b);
    elem[1U] = u;
    uint64_t u0 = load64_be(b + (uint32_t)8U);
    elem[0U] = u0;
    acc0[0U] = acc0[0U] ^ elem[0U];
    acc0[1U] = acc0[1U] ^ elem[1U];
    Hacl_Impl_Gf128_FieldPreComp_fmul(acc0, r10);
  }
  uint64_t *acc1 = ctx;
  uint64_t r0 = acc1[1U];
  uint64_t r1 = acc1[0U];
  store64_be(tag, r0);
  store64_be(tag + (uint32_t)8U, r1);
}

/* SNIPPET_END: Hacl_Gf128_PreComp_ghash */

