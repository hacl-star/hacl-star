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


#include "Hacl_Gf128_NI.h"

static inline void
fadd0(Lib_IntVector_Intrinsics_vec128 *x, Lib_IntVector_Intrinsics_vec128 *y)
{
  x[0U] = Lib_IntVector_Intrinsics_vec128_xor(x[0U], y[0U]);
}

static inline void
fmul0(Lib_IntVector_Intrinsics_vec128 *x, Lib_IntVector_Intrinsics_vec128 *y)
{
  Lib_IntVector_Intrinsics_vec128 xe = x[0U];
  Lib_IntVector_Intrinsics_vec128 ye = y[0U];
  Lib_IntVector_Intrinsics_vec128 lo0 = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, 0x00U);
  Lib_IntVector_Intrinsics_vec128 m1 = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, 0x10U);
  Lib_IntVector_Intrinsics_vec128 m2 = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, 0x01U);
  Lib_IntVector_Intrinsics_vec128 hi = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, 0x11U);
  Lib_IntVector_Intrinsics_vec128 m11 = Lib_IntVector_Intrinsics_vec128_xor(m1, m2);
  Lib_IntVector_Intrinsics_vec128 m21 = Lib_IntVector_Intrinsics_vec128_shift_left(m11, 64U);
  Lib_IntVector_Intrinsics_vec128 m12 = Lib_IntVector_Intrinsics_vec128_shift_right(m11, 64U);
  Lib_IntVector_Intrinsics_vec128 lo10 = Lib_IntVector_Intrinsics_vec128_xor(lo0, m21);
  Lib_IntVector_Intrinsics_vec128 hi10 = Lib_IntVector_Intrinsics_vec128_xor(hi, m12);
  Lib_IntVector_Intrinsics_vec128 hi0 = hi10;
  Lib_IntVector_Intrinsics_vec128 lo = lo10;
  Lib_IntVector_Intrinsics_vec128 lo1 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, 63U);
  Lib_IntVector_Intrinsics_vec128 lo2 = Lib_IntVector_Intrinsics_vec128_shift_left(lo1, 64U);
  Lib_IntVector_Intrinsics_vec128 lo3 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo, 1U);
  Lib_IntVector_Intrinsics_vec128 lo31 = Lib_IntVector_Intrinsics_vec128_xor(lo3, lo2);
  Lib_IntVector_Intrinsics_vec128 hi1 = Lib_IntVector_Intrinsics_vec128_shift_right64(hi0, 63U);
  Lib_IntVector_Intrinsics_vec128 hi11 = Lib_IntVector_Intrinsics_vec128_shift_left(hi1, 64U);
  Lib_IntVector_Intrinsics_vec128 hi2 = Lib_IntVector_Intrinsics_vec128_shift_left64(hi0, 1U);
  Lib_IntVector_Intrinsics_vec128 hi21 = Lib_IntVector_Intrinsics_vec128_xor(hi2, hi11);
  Lib_IntVector_Intrinsics_vec128 lo11 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, 63U);
  Lib_IntVector_Intrinsics_vec128 lo12 = Lib_IntVector_Intrinsics_vec128_shift_right(lo11, 64U);
  Lib_IntVector_Intrinsics_vec128 hi22 = Lib_IntVector_Intrinsics_vec128_xor(hi21, lo12);
  Lib_IntVector_Intrinsics_vec128 lo4 = lo31;
  Lib_IntVector_Intrinsics_vec128 hi3 = hi22;
  Lib_IntVector_Intrinsics_vec128 lo13 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, 63U);
  Lib_IntVector_Intrinsics_vec128 lo21 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, 62U);
  Lib_IntVector_Intrinsics_vec128 lo32 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, 57U);
  Lib_IntVector_Intrinsics_vec128 lo14 = Lib_IntVector_Intrinsics_vec128_xor(lo13, lo21);
  Lib_IntVector_Intrinsics_vec128 lo15 = Lib_IntVector_Intrinsics_vec128_xor(lo14, lo32);
  Lib_IntVector_Intrinsics_vec128 lo22 = Lib_IntVector_Intrinsics_vec128_shift_right(lo15, 64U);
  Lib_IntVector_Intrinsics_vec128 lo33 = Lib_IntVector_Intrinsics_vec128_shift_left(lo15, 64U);
  Lib_IntVector_Intrinsics_vec128 lo5 = Lib_IntVector_Intrinsics_vec128_xor(lo4, lo33);
  Lib_IntVector_Intrinsics_vec128 lo_ = lo22;
  Lib_IntVector_Intrinsics_vec128 lo16 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo5, 1U);
  Lib_IntVector_Intrinsics_vec128 lo23 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo5, 2U);
  Lib_IntVector_Intrinsics_vec128 lo34 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo5, 7U);
  Lib_IntVector_Intrinsics_vec128 lo17 = Lib_IntVector_Intrinsics_vec128_xor(lo16, lo23);
  Lib_IntVector_Intrinsics_vec128 lo18 = Lib_IntVector_Intrinsics_vec128_xor(lo17, lo34);
  Lib_IntVector_Intrinsics_vec128 lo19 = Lib_IntVector_Intrinsics_vec128_xor(lo18, lo_);
  Lib_IntVector_Intrinsics_vec128 lo6 = Lib_IntVector_Intrinsics_vec128_xor(lo5, lo19);
  Lib_IntVector_Intrinsics_vec128 lo7 = Lib_IntVector_Intrinsics_vec128_xor(lo6, hi3);
  Lib_IntVector_Intrinsics_vec128 lo110 = lo7;
  x[0U] = lo110;
}

static inline void load_precompute_r(Lib_IntVector_Intrinsics_vec128 *pre, uint8_t *key)
{
  Lib_IntVector_Intrinsics_vec128 *r4 = pre;
  Lib_IntVector_Intrinsics_vec128 *r3 = pre + 1U;
  Lib_IntVector_Intrinsics_vec128 *r2 = pre + 2U;
  Lib_IntVector_Intrinsics_vec128 *r1 = pre + 3U;
  r1[0U] = Lib_IntVector_Intrinsics_vec128_load_be(key);
  r4[0U] = r1[0U];
  r3[0U] = r1[0U];
  r2[0U] = r1[0U];
  fmul0(r2, r1);
  fmul0(r3, r2);
  fmul0(r4, r3);
}

static inline void
normalize4(
  Lib_IntVector_Intrinsics_vec128 *acc,
  Lib_IntVector_Intrinsics_vec128 *x,
  Lib_IntVector_Intrinsics_vec128 *pre
)
{
  Lib_IntVector_Intrinsics_vec128 x1 = x[0U];
  Lib_IntVector_Intrinsics_vec128 x2 = x[1U];
  Lib_IntVector_Intrinsics_vec128 x3 = x[2U];
  Lib_IntVector_Intrinsics_vec128 x4 = x[3U];
  Lib_IntVector_Intrinsics_vec128 y1 = pre[0U];
  Lib_IntVector_Intrinsics_vec128 y2 = pre[1U];
  Lib_IntVector_Intrinsics_vec128 y3 = pre[2U];
  Lib_IntVector_Intrinsics_vec128 y4 = pre[3U];
  Lib_IntVector_Intrinsics_vec128 lo10 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, 0x00U);
  Lib_IntVector_Intrinsics_vec128 lo2 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, 0x00U);
  Lib_IntVector_Intrinsics_vec128 lo30 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, 0x00U);
  Lib_IntVector_Intrinsics_vec128 lo40 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, 0x00U);
  Lib_IntVector_Intrinsics_vec128 lo0 = Lib_IntVector_Intrinsics_vec128_xor(lo10, lo2);
  Lib_IntVector_Intrinsics_vec128 lo5 = Lib_IntVector_Intrinsics_vec128_xor(lo0, lo30);
  Lib_IntVector_Intrinsics_vec128 lo6 = Lib_IntVector_Intrinsics_vec128_xor(lo5, lo40);
  Lib_IntVector_Intrinsics_vec128 m1 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, 0x10U);
  Lib_IntVector_Intrinsics_vec128 m2 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, 0x10U);
  Lib_IntVector_Intrinsics_vec128 m3 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, 0x10U);
  Lib_IntVector_Intrinsics_vec128 m4 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, 0x10U);
  Lib_IntVector_Intrinsics_vec128 m = Lib_IntVector_Intrinsics_vec128_xor(m1, m2);
  Lib_IntVector_Intrinsics_vec128 m5 = Lib_IntVector_Intrinsics_vec128_xor(m, m3);
  Lib_IntVector_Intrinsics_vec128 m6 = Lib_IntVector_Intrinsics_vec128_xor(m5, m4);
  Lib_IntVector_Intrinsics_vec128 m11 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, 0x01U);
  Lib_IntVector_Intrinsics_vec128 m21 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, 0x01U);
  Lib_IntVector_Intrinsics_vec128 m31 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, 0x01U);
  Lib_IntVector_Intrinsics_vec128 m41 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, 0x01U);
  Lib_IntVector_Intrinsics_vec128 m7 = Lib_IntVector_Intrinsics_vec128_xor(m6, m11);
  Lib_IntVector_Intrinsics_vec128 m8 = Lib_IntVector_Intrinsics_vec128_xor(m7, m21);
  Lib_IntVector_Intrinsics_vec128 m9 = Lib_IntVector_Intrinsics_vec128_xor(m8, m31);
  Lib_IntVector_Intrinsics_vec128 m10 = Lib_IntVector_Intrinsics_vec128_xor(m9, m41);
  Lib_IntVector_Intrinsics_vec128 hi10 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, 0x11U);
  Lib_IntVector_Intrinsics_vec128 hi20 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, 0x11U);
  Lib_IntVector_Intrinsics_vec128 hi30 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, 0x11U);
  Lib_IntVector_Intrinsics_vec128 hi4 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, 0x11U);
  Lib_IntVector_Intrinsics_vec128 hi = Lib_IntVector_Intrinsics_vec128_xor(hi10, hi20);
  Lib_IntVector_Intrinsics_vec128 hi5 = Lib_IntVector_Intrinsics_vec128_xor(hi, hi30);
  Lib_IntVector_Intrinsics_vec128 hi6 = Lib_IntVector_Intrinsics_vec128_xor(hi5, hi4);
  Lib_IntVector_Intrinsics_vec128 m12 = Lib_IntVector_Intrinsics_vec128_shift_left(m10, 64U);
  Lib_IntVector_Intrinsics_vec128 m22 = Lib_IntVector_Intrinsics_vec128_shift_right(m10, 64U);
  Lib_IntVector_Intrinsics_vec128 lo7 = Lib_IntVector_Intrinsics_vec128_xor(lo6, m12);
  Lib_IntVector_Intrinsics_vec128 hi7 = Lib_IntVector_Intrinsics_vec128_xor(hi6, m22);
  Lib_IntVector_Intrinsics_vec128 hi0 = hi7;
  Lib_IntVector_Intrinsics_vec128 lo = lo7;
  Lib_IntVector_Intrinsics_vec128 lo1 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, 63U);
  Lib_IntVector_Intrinsics_vec128 lo20 = Lib_IntVector_Intrinsics_vec128_shift_left(lo1, 64U);
  Lib_IntVector_Intrinsics_vec128 lo3 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo, 1U);
  Lib_IntVector_Intrinsics_vec128 lo31 = Lib_IntVector_Intrinsics_vec128_xor(lo3, lo20);
  Lib_IntVector_Intrinsics_vec128 hi1 = Lib_IntVector_Intrinsics_vec128_shift_right64(hi0, 63U);
  Lib_IntVector_Intrinsics_vec128 hi11 = Lib_IntVector_Intrinsics_vec128_shift_left(hi1, 64U);
  Lib_IntVector_Intrinsics_vec128 hi2 = Lib_IntVector_Intrinsics_vec128_shift_left64(hi0, 1U);
  Lib_IntVector_Intrinsics_vec128 hi21 = Lib_IntVector_Intrinsics_vec128_xor(hi2, hi11);
  Lib_IntVector_Intrinsics_vec128 lo11 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, 63U);
  Lib_IntVector_Intrinsics_vec128 lo12 = Lib_IntVector_Intrinsics_vec128_shift_right(lo11, 64U);
  Lib_IntVector_Intrinsics_vec128 hi22 = Lib_IntVector_Intrinsics_vec128_xor(hi21, lo12);
  Lib_IntVector_Intrinsics_vec128 lo4 = lo31;
  Lib_IntVector_Intrinsics_vec128 hi3 = hi22;
  Lib_IntVector_Intrinsics_vec128 lo13 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, 63U);
  Lib_IntVector_Intrinsics_vec128 lo21 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, 62U);
  Lib_IntVector_Intrinsics_vec128 lo32 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, 57U);
  Lib_IntVector_Intrinsics_vec128 lo14 = Lib_IntVector_Intrinsics_vec128_xor(lo13, lo21);
  Lib_IntVector_Intrinsics_vec128 lo15 = Lib_IntVector_Intrinsics_vec128_xor(lo14, lo32);
  Lib_IntVector_Intrinsics_vec128 lo22 = Lib_IntVector_Intrinsics_vec128_shift_right(lo15, 64U);
  Lib_IntVector_Intrinsics_vec128 lo33 = Lib_IntVector_Intrinsics_vec128_shift_left(lo15, 64U);
  Lib_IntVector_Intrinsics_vec128 lo50 = Lib_IntVector_Intrinsics_vec128_xor(lo4, lo33);
  Lib_IntVector_Intrinsics_vec128 lo_ = lo22;
  Lib_IntVector_Intrinsics_vec128 lo16 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo50, 1U);
  Lib_IntVector_Intrinsics_vec128 lo23 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo50, 2U);
  Lib_IntVector_Intrinsics_vec128 lo34 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo50, 7U);
  Lib_IntVector_Intrinsics_vec128 lo17 = Lib_IntVector_Intrinsics_vec128_xor(lo16, lo23);
  Lib_IntVector_Intrinsics_vec128 lo18 = Lib_IntVector_Intrinsics_vec128_xor(lo17, lo34);
  Lib_IntVector_Intrinsics_vec128 lo19 = Lib_IntVector_Intrinsics_vec128_xor(lo18, lo_);
  Lib_IntVector_Intrinsics_vec128 lo60 = Lib_IntVector_Intrinsics_vec128_xor(lo50, lo19);
  Lib_IntVector_Intrinsics_vec128 lo70 = Lib_IntVector_Intrinsics_vec128_xor(lo60, hi3);
  Lib_IntVector_Intrinsics_vec128 lo110 = lo70;
  acc[0U] = lo110;
}

inline void Hacl_Gf128_NI_gcm_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + 1U;
  acc[0U] = Lib_IntVector_Intrinsics_vec128_zero;
  load_precompute_r(pre, key);
}

inline void
Hacl_Gf128_NI_gcm_update_blocks(
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t len,
  uint8_t *text
)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + 1U;
  uint32_t len0 = len / 64U * 64U;
  uint8_t *t0 = text;
  if (len0 > 0U)
  {
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 f[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *b4 = f;
    uint32_t nb = len0 / 64U;
    for (uint32_t i = 0U; i < nb; i++)
    {
      uint8_t *tb = t0 + i * 64U;
      b4[0U] = Lib_IntVector_Intrinsics_vec128_load_be(tb);
      b4[1U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + 16U);
      b4[2U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + 32U);
      b4[3U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + 48U);
      b4[0U] = Lib_IntVector_Intrinsics_vec128_xor(acc[0U], b4[0U]);
      normalize4(acc, b4, pre);
    }
  }
  uint32_t len1 = len - len0;
  uint8_t *t1 = text + len0;
  Lib_IntVector_Intrinsics_vec128 *r1 = pre + 3U;
  uint32_t nb = len1 / 16U;
  uint32_t rem = len1 % 16U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *tb = t1 + i * 16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    elem = Lib_IntVector_Intrinsics_vec128_load_be(tb);
    fadd0(acc, &elem);
    fmul0(acc, r1);
  }
  if (rem > 0U)
  {
    uint8_t *last = t1 + nb * 16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    uint8_t b[16U] = { 0U };
    memcpy(b, last, rem * sizeof (uint8_t));
    elem = Lib_IntVector_Intrinsics_vec128_load_be(b);
    fadd0(acc, &elem);
    fmul0(acc, r1);
    return;
  }
}

void
(*Hacl_Gf128_NI_gcm_update_padded)(
  Lib_IntVector_Intrinsics_vec128 *x0,
  uint32_t x1,
  uint8_t *x2
) = Hacl_Gf128_NI_gcm_update_blocks;

inline void Hacl_Gf128_NI_gcm_emit(uint8_t *tag, Lib_IntVector_Intrinsics_vec128 *ctx)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128_store_be(tag, acc[0U]);
}

inline void Hacl_Gf128_NI_ghash(uint8_t *tag, uint32_t len, uint8_t *text, uint8_t *key)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[5U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre0 = ctx + 1U;
  acc[0U] = Lib_IntVector_Intrinsics_vec128_zero;
  load_precompute_r(pre0, key);
  Lib_IntVector_Intrinsics_vec128 *acc0 = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + 1U;
  uint32_t len0 = len / 64U * 64U;
  uint8_t *t0 = text;
  if (len0 > 0U)
  {
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 f[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *b4 = f;
    uint32_t nb = len0 / 64U;
    for (uint32_t i = 0U; i < nb; i++)
    {
      uint8_t *tb = t0 + i * 64U;
      b4[0U] = Lib_IntVector_Intrinsics_vec128_load_be(tb);
      b4[1U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + 16U);
      b4[2U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + 32U);
      b4[3U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + 48U);
      b4[0U] = Lib_IntVector_Intrinsics_vec128_xor(acc0[0U], b4[0U]);
      normalize4(acc0, b4, pre);
    }
  }
  uint32_t len1 = len - len0;
  uint8_t *t1 = text + len0;
  Lib_IntVector_Intrinsics_vec128 *r1 = pre + 3U;
  uint32_t nb = len1 / 16U;
  uint32_t rem = len1 % 16U;
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint8_t *tb = t1 + i * 16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    elem = Lib_IntVector_Intrinsics_vec128_load_be(tb);
    fadd0(acc0, &elem);
    fmul0(acc0, r1);
  }
  if (rem > 0U)
  {
    uint8_t *last = t1 + nb * 16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    uint8_t b[16U] = { 0U };
    memcpy(b, last, rem * sizeof (uint8_t));
    elem = Lib_IntVector_Intrinsics_vec128_load_be(b);
    fadd0(acc0, &elem);
    fmul0(acc0, r1);
  }
  Lib_IntVector_Intrinsics_vec128 *acc1 = ctx;
  Lib_IntVector_Intrinsics_vec128_store_be(tag, acc1[0U]);
}

