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


#include "internal/Hacl_Gf128_NI.h"

/* SNIPPET_START: fadd0 */

static inline void
fadd0(Lib_IntVector_Intrinsics_vec128 *x, Lib_IntVector_Intrinsics_vec128 *y)
{
  x[0U] = Lib_IntVector_Intrinsics_vec128_xor(x[0U], y[0U]);
}

/* SNIPPET_END: fadd0 */

/* SNIPPET_START: fmul0 */

static inline void
fmul0(Lib_IntVector_Intrinsics_vec128 *x, Lib_IntVector_Intrinsics_vec128 *y)
{
  Lib_IntVector_Intrinsics_vec128 xe = x[0U];
  Lib_IntVector_Intrinsics_vec128 ye = y[0U];
  Lib_IntVector_Intrinsics_vec128
  lo0 = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, (uint8_t)0x00U);
  Lib_IntVector_Intrinsics_vec128 m1 = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, (uint8_t)0x10U);
  Lib_IntVector_Intrinsics_vec128 m2 = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, (uint8_t)0x01U);
  Lib_IntVector_Intrinsics_vec128 hi = Lib_IntVector_Intrinsics_ni_clmul(xe, ye, (uint8_t)0x11U);
  Lib_IntVector_Intrinsics_vec128 m11 = Lib_IntVector_Intrinsics_vec128_xor(m1, m2);
  Lib_IntVector_Intrinsics_vec128
  m21 = Lib_IntVector_Intrinsics_vec128_shift_left(m11, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  m12 = Lib_IntVector_Intrinsics_vec128_shift_right(m11, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128 lo10 = Lib_IntVector_Intrinsics_vec128_xor(lo0, m21);
  Lib_IntVector_Intrinsics_vec128 hi10 = Lib_IntVector_Intrinsics_vec128_xor(hi, m12);
  Lib_IntVector_Intrinsics_vec128 hi0 = hi10;
  Lib_IntVector_Intrinsics_vec128 lo = lo10;
  Lib_IntVector_Intrinsics_vec128
  lo1 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  lo2 = Lib_IntVector_Intrinsics_vec128_shift_left(lo1, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  lo3 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo, (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 lo31 = Lib_IntVector_Intrinsics_vec128_xor(lo3, lo2);
  Lib_IntVector_Intrinsics_vec128
  hi1 = Lib_IntVector_Intrinsics_vec128_shift_right64(hi0, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  hi11 = Lib_IntVector_Intrinsics_vec128_shift_left(hi1, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  hi2 = Lib_IntVector_Intrinsics_vec128_shift_left64(hi0, (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 hi21 = Lib_IntVector_Intrinsics_vec128_xor(hi2, hi11);
  Lib_IntVector_Intrinsics_vec128
  lo11 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  lo12 = Lib_IntVector_Intrinsics_vec128_shift_right(lo11, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128 hi22 = Lib_IntVector_Intrinsics_vec128_xor(hi21, lo12);
  Lib_IntVector_Intrinsics_vec128 lo4 = lo31;
  Lib_IntVector_Intrinsics_vec128 hi3 = hi22;
  Lib_IntVector_Intrinsics_vec128
  lo13 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  lo21 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, (uint32_t)62U);
  Lib_IntVector_Intrinsics_vec128
  lo32 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, (uint32_t)57U);
  Lib_IntVector_Intrinsics_vec128 lo14 = Lib_IntVector_Intrinsics_vec128_xor(lo13, lo21);
  Lib_IntVector_Intrinsics_vec128 lo15 = Lib_IntVector_Intrinsics_vec128_xor(lo14, lo32);
  Lib_IntVector_Intrinsics_vec128
  lo22 = Lib_IntVector_Intrinsics_vec128_shift_right(lo15, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  lo33 = Lib_IntVector_Intrinsics_vec128_shift_left(lo15, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128 lo5 = Lib_IntVector_Intrinsics_vec128_xor(lo4, lo33);
  Lib_IntVector_Intrinsics_vec128 lo_ = lo22;
  Lib_IntVector_Intrinsics_vec128
  lo16 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo5, (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128
  lo23 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo5, (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128
  lo34 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo5, (uint32_t)7U);
  Lib_IntVector_Intrinsics_vec128 lo17 = Lib_IntVector_Intrinsics_vec128_xor(lo16, lo23);
  Lib_IntVector_Intrinsics_vec128 lo18 = Lib_IntVector_Intrinsics_vec128_xor(lo17, lo34);
  Lib_IntVector_Intrinsics_vec128 lo19 = Lib_IntVector_Intrinsics_vec128_xor(lo18, lo_);
  Lib_IntVector_Intrinsics_vec128 lo6 = Lib_IntVector_Intrinsics_vec128_xor(lo5, lo19);
  Lib_IntVector_Intrinsics_vec128 lo7 = Lib_IntVector_Intrinsics_vec128_xor(lo6, hi3);
  Lib_IntVector_Intrinsics_vec128 lo110 = lo7;
  x[0U] = lo110;
}

/* SNIPPET_END: fmul0 */

/* SNIPPET_START: load_precompute_r */

static inline void load_precompute_r(Lib_IntVector_Intrinsics_vec128 *pre, uint8_t *key)
{
  Lib_IntVector_Intrinsics_vec128 *r4 = pre;
  Lib_IntVector_Intrinsics_vec128 *r3 = pre + (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 *r2 = pre + (uint32_t)2U;
  Lib_IntVector_Intrinsics_vec128 *r1 = pre + (uint32_t)3U;
  r1[0U] = Lib_IntVector_Intrinsics_vec128_load_be(key);
  r4[0U] = r1[0U];
  r3[0U] = r1[0U];
  r2[0U] = r1[0U];
  fmul0(r2, r1);
  fmul0(r3, r2);
  fmul0(r4, r3);
}

/* SNIPPET_END: load_precompute_r */

/* SNIPPET_START: normalize4 */

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
  Lib_IntVector_Intrinsics_vec128
  lo10 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, (uint8_t)0x00U);
  Lib_IntVector_Intrinsics_vec128
  lo2 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, (uint8_t)0x00U);
  Lib_IntVector_Intrinsics_vec128
  lo30 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, (uint8_t)0x00U);
  Lib_IntVector_Intrinsics_vec128
  lo40 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, (uint8_t)0x00U);
  Lib_IntVector_Intrinsics_vec128 lo0 = Lib_IntVector_Intrinsics_vec128_xor(lo10, lo2);
  Lib_IntVector_Intrinsics_vec128 lo5 = Lib_IntVector_Intrinsics_vec128_xor(lo0, lo30);
  Lib_IntVector_Intrinsics_vec128 lo6 = Lib_IntVector_Intrinsics_vec128_xor(lo5, lo40);
  Lib_IntVector_Intrinsics_vec128 m1 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, (uint8_t)0x10U);
  Lib_IntVector_Intrinsics_vec128 m2 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, (uint8_t)0x10U);
  Lib_IntVector_Intrinsics_vec128 m3 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, (uint8_t)0x10U);
  Lib_IntVector_Intrinsics_vec128 m4 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, (uint8_t)0x10U);
  Lib_IntVector_Intrinsics_vec128 m = Lib_IntVector_Intrinsics_vec128_xor(m1, m2);
  Lib_IntVector_Intrinsics_vec128 m5 = Lib_IntVector_Intrinsics_vec128_xor(m, m3);
  Lib_IntVector_Intrinsics_vec128 m6 = Lib_IntVector_Intrinsics_vec128_xor(m5, m4);
  Lib_IntVector_Intrinsics_vec128
  m11 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, (uint8_t)0x01U);
  Lib_IntVector_Intrinsics_vec128
  m21 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, (uint8_t)0x01U);
  Lib_IntVector_Intrinsics_vec128
  m31 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, (uint8_t)0x01U);
  Lib_IntVector_Intrinsics_vec128
  m41 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, (uint8_t)0x01U);
  Lib_IntVector_Intrinsics_vec128 m7 = Lib_IntVector_Intrinsics_vec128_xor(m6, m11);
  Lib_IntVector_Intrinsics_vec128 m8 = Lib_IntVector_Intrinsics_vec128_xor(m7, m21);
  Lib_IntVector_Intrinsics_vec128 m9 = Lib_IntVector_Intrinsics_vec128_xor(m8, m31);
  Lib_IntVector_Intrinsics_vec128 m10 = Lib_IntVector_Intrinsics_vec128_xor(m9, m41);
  Lib_IntVector_Intrinsics_vec128
  hi10 = Lib_IntVector_Intrinsics_ni_clmul(x1, y1, (uint8_t)0x11U);
  Lib_IntVector_Intrinsics_vec128
  hi20 = Lib_IntVector_Intrinsics_ni_clmul(x2, y2, (uint8_t)0x11U);
  Lib_IntVector_Intrinsics_vec128
  hi30 = Lib_IntVector_Intrinsics_ni_clmul(x3, y3, (uint8_t)0x11U);
  Lib_IntVector_Intrinsics_vec128
  hi4 = Lib_IntVector_Intrinsics_ni_clmul(x4, y4, (uint8_t)0x11U);
  Lib_IntVector_Intrinsics_vec128 hi = Lib_IntVector_Intrinsics_vec128_xor(hi10, hi20);
  Lib_IntVector_Intrinsics_vec128 hi5 = Lib_IntVector_Intrinsics_vec128_xor(hi, hi30);
  Lib_IntVector_Intrinsics_vec128 hi6 = Lib_IntVector_Intrinsics_vec128_xor(hi5, hi4);
  Lib_IntVector_Intrinsics_vec128
  m12 = Lib_IntVector_Intrinsics_vec128_shift_left(m10, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  m22 = Lib_IntVector_Intrinsics_vec128_shift_right(m10, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128 lo7 = Lib_IntVector_Intrinsics_vec128_xor(lo6, m12);
  Lib_IntVector_Intrinsics_vec128 hi7 = Lib_IntVector_Intrinsics_vec128_xor(hi6, m22);
  Lib_IntVector_Intrinsics_vec128 hi0 = hi7;
  Lib_IntVector_Intrinsics_vec128 lo = lo7;
  Lib_IntVector_Intrinsics_vec128
  lo1 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  lo20 = Lib_IntVector_Intrinsics_vec128_shift_left(lo1, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  lo3 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo, (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 lo31 = Lib_IntVector_Intrinsics_vec128_xor(lo3, lo20);
  Lib_IntVector_Intrinsics_vec128
  hi1 = Lib_IntVector_Intrinsics_vec128_shift_right64(hi0, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  hi11 = Lib_IntVector_Intrinsics_vec128_shift_left(hi1, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  hi2 = Lib_IntVector_Intrinsics_vec128_shift_left64(hi0, (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128 hi21 = Lib_IntVector_Intrinsics_vec128_xor(hi2, hi11);
  Lib_IntVector_Intrinsics_vec128
  lo11 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  lo12 = Lib_IntVector_Intrinsics_vec128_shift_right(lo11, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128 hi22 = Lib_IntVector_Intrinsics_vec128_xor(hi21, lo12);
  Lib_IntVector_Intrinsics_vec128 lo4 = lo31;
  Lib_IntVector_Intrinsics_vec128 hi3 = hi22;
  Lib_IntVector_Intrinsics_vec128
  lo13 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, (uint32_t)63U);
  Lib_IntVector_Intrinsics_vec128
  lo21 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, (uint32_t)62U);
  Lib_IntVector_Intrinsics_vec128
  lo32 = Lib_IntVector_Intrinsics_vec128_shift_left64(lo4, (uint32_t)57U);
  Lib_IntVector_Intrinsics_vec128 lo14 = Lib_IntVector_Intrinsics_vec128_xor(lo13, lo21);
  Lib_IntVector_Intrinsics_vec128 lo15 = Lib_IntVector_Intrinsics_vec128_xor(lo14, lo32);
  Lib_IntVector_Intrinsics_vec128
  lo22 = Lib_IntVector_Intrinsics_vec128_shift_right(lo15, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128
  lo33 = Lib_IntVector_Intrinsics_vec128_shift_left(lo15, (uint32_t)64U);
  Lib_IntVector_Intrinsics_vec128 lo50 = Lib_IntVector_Intrinsics_vec128_xor(lo4, lo33);
  Lib_IntVector_Intrinsics_vec128 lo_ = lo22;
  Lib_IntVector_Intrinsics_vec128
  lo16 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo50, (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec128
  lo23 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo50, (uint32_t)2U);
  Lib_IntVector_Intrinsics_vec128
  lo34 = Lib_IntVector_Intrinsics_vec128_shift_right64(lo50, (uint32_t)7U);
  Lib_IntVector_Intrinsics_vec128 lo17 = Lib_IntVector_Intrinsics_vec128_xor(lo16, lo23);
  Lib_IntVector_Intrinsics_vec128 lo18 = Lib_IntVector_Intrinsics_vec128_xor(lo17, lo34);
  Lib_IntVector_Intrinsics_vec128 lo19 = Lib_IntVector_Intrinsics_vec128_xor(lo18, lo_);
  Lib_IntVector_Intrinsics_vec128 lo60 = Lib_IntVector_Intrinsics_vec128_xor(lo50, lo19);
  Lib_IntVector_Intrinsics_vec128 lo70 = Lib_IntVector_Intrinsics_vec128_xor(lo60, hi3);
  Lib_IntVector_Intrinsics_vec128 lo110 = lo70;
  acc[0U] = lo110;
}

/* SNIPPET_END: normalize4 */

/* SNIPPET_START: Hacl_Impl_Gf128_FieldPreComp_fmul */

void Hacl_Impl_Gf128_FieldPreComp_fmul(uint64_t *x, uint64_t *y)
{
  uint64_t res[2U] = { 0U };
  uint64_t y_[2U] = { 0U };
  y_[0U] = y[0U];
  y_[1U] = y[1U];
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t m = (uint64_t)0U - (x[1U] >> ((uint32_t)63U - i) & (uint64_t)1U);
    res[0U] = res[0U] ^ (y_[0U] & m);
    res[1U] = res[1U] ^ (y_[1U] & m);
    uint64_t m0 = (uint64_t)0U - (y_[0U] & (uint64_t)1U);
    y_[0U] = y_[0U] >> (uint32_t)1U | y_[1U] << (uint32_t)63U;
    y_[1U] = y_[1U] >> (uint32_t)1U ^ ((uint64_t)0xE100000000000000U & m0);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t m = (uint64_t)0U - (x[0U] >> ((uint32_t)63U - i) & (uint64_t)1U);
    res[0U] = res[0U] ^ (y_[0U] & m);
    res[1U] = res[1U] ^ (y_[1U] & m);
    uint64_t m0 = (uint64_t)0U - (y_[0U] & (uint64_t)1U);
    y_[0U] = y_[0U] >> (uint32_t)1U | y_[1U] << (uint32_t)63U;
    y_[1U] = y_[1U] >> (uint32_t)1U ^ ((uint64_t)0xE100000000000000U & m0);
  }
  x[0U] = res[0U];
  x[1U] = res[1U];
}

/* SNIPPET_END: Hacl_Impl_Gf128_FieldPreComp_fmul */

/* SNIPPET_START: prepare */

static inline void prepare(uint64_t *pre, uint64_t *r)
{
  memset(pre, 0U, (uint32_t)256U * sizeof (uint64_t));
  uint64_t sh[2U] = { 0U };
  sh[0U] = r[0U];
  sh[1U] = r[1U];
  uint64_t *pre1 = pre;
  uint64_t *pre2 = pre + (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    memcpy(pre1 + (uint32_t)2U * i, sh, (uint32_t)2U * sizeof (uint64_t));
    uint64_t m = (uint64_t)0U - (sh[0U] & (uint64_t)1U);
    sh[0U] = sh[0U] >> (uint32_t)1U | sh[1U] << (uint32_t)63U;
    sh[1U] = sh[1U] >> (uint32_t)1U ^ ((uint64_t)0xE100000000000000U & m);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    memcpy(pre2 + (uint32_t)2U * i, sh, (uint32_t)2U * sizeof (uint64_t));
    uint64_t m = (uint64_t)0U - (sh[0U] & (uint64_t)1U);
    sh[0U] = sh[0U] >> (uint32_t)1U | sh[1U] << (uint32_t)63U;
    sh[1U] = sh[1U] >> (uint32_t)1U ^ ((uint64_t)0xE100000000000000U & m);
  }
}

/* SNIPPET_END: prepare */

/* SNIPPET_START: Hacl_Impl_Gf128_FieldPreComp_load_precompute_r */

void Hacl_Impl_Gf128_FieldPreComp_load_precompute_r(uint64_t *pre, uint8_t *key)
{
  uint64_t *r4321 = pre;
  uint64_t *r1 = r4321 + (uint32_t)6U;
  uint64_t *r2 = r4321 + (uint32_t)4U;
  uint64_t *r3 = r4321 + (uint32_t)2U;
  uint64_t *r4 = r4321;
  uint64_t *table2 = pre + (uint32_t)8U;
  uint64_t u = load64_be(key);
  r1[1U] = u;
  uint64_t u0 = load64_be(key + (uint32_t)8U);
  r1[0U] = u0;
  r4[0U] = r1[0U];
  r4[1U] = r1[1U];
  r3[0U] = r1[0U];
  r3[1U] = r1[1U];
  r2[0U] = r1[0U];
  r2[1U] = r1[1U];
  Hacl_Impl_Gf128_FieldPreComp_fmul(r2, r1);
  Hacl_Impl_Gf128_FieldPreComp_fmul(r3, r2);
  Hacl_Impl_Gf128_FieldPreComp_fmul(r4, r3);
  prepare(table2, r4);
}

/* SNIPPET_END: Hacl_Impl_Gf128_FieldPreComp_load_precompute_r */

/* SNIPPET_START: fmul_pre */

static inline void fmul_pre(uint64_t *x, uint64_t *pre)
{
  uint64_t *tab = pre + (uint32_t)8U;
  uint64_t tmp[2U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *uu____0 = tab + (uint32_t)2U * i;
    uint64_t m = (uint64_t)0U - (x[1U] >> ((uint32_t)63U - i) & (uint64_t)1U);
    tmp[0U] = tmp[0U] ^ (uu____0[0U] & m);
    tmp[1U] = tmp[1U] ^ (uu____0[1U] & m);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *uu____1 = tab + (uint32_t)128U + (uint32_t)2U * i;
    uint64_t m = (uint64_t)0U - (x[0U] >> ((uint32_t)63U - i) & (uint64_t)1U);
    tmp[0U] = tmp[0U] ^ (uu____1[0U] & m);
    tmp[1U] = tmp[1U] ^ (uu____1[1U] & m);
  }
  x[0U] = tmp[0U];
  x[1U] = tmp[1U];
}

/* SNIPPET_END: fmul_pre */

/* SNIPPET_START: Hacl_Impl_Gf128_FieldPreComp_fmul_r4 */

void Hacl_Impl_Gf128_FieldPreComp_fmul_r4(uint64_t *x, uint64_t *pre)
{
  fmul_pre(x, pre);
  fmul_pre(x + (uint32_t)2U, pre);
  fmul_pre(x + (uint32_t)4U, pre);
  fmul_pre(x + (uint32_t)6U, pre);
}

/* SNIPPET_END: Hacl_Impl_Gf128_FieldPreComp_fmul_r4 */

/* SNIPPET_START: Hacl_Impl_Gf128_FieldPreComp_normalize4 */

void Hacl_Impl_Gf128_FieldPreComp_normalize4(uint64_t *acc, uint64_t *x, uint64_t *pre)
{
  uint64_t *x1 = x;
  uint64_t *x2 = x + (uint32_t)2U;
  uint64_t *x3 = x + (uint32_t)4U;
  uint64_t *x4 = x + (uint32_t)6U;
  fmul_pre(x, pre);
  Hacl_Impl_Gf128_FieldPreComp_fmul(x + (uint32_t)2U, pre + (uint32_t)2U);
  Hacl_Impl_Gf128_FieldPreComp_fmul(x + (uint32_t)4U, pre + (uint32_t)4U);
  Hacl_Impl_Gf128_FieldPreComp_fmul(x + (uint32_t)6U, pre + (uint32_t)6U);
  acc[0U] = x1[0U];
  acc[1U] = x1[1U];
  acc[0U] = acc[0U] ^ x2[0U];
  acc[1U] = acc[1U] ^ x2[1U];
  acc[0U] = acc[0U] ^ x3[0U];
  acc[1U] = acc[1U] ^ x3[1U];
  acc[0U] = acc[0U] ^ x4[0U];
  acc[1U] = acc[1U] ^ x4[1U];
}

/* SNIPPET_END: Hacl_Impl_Gf128_FieldPreComp_normalize4 */

/* SNIPPET_START: Hacl_Gf128_NI_gcm_init */

void Hacl_Gf128_NI_gcm_init(Lib_IntVector_Intrinsics_vec128 *ctx, uint8_t *key)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + (uint32_t)1U;
  acc[0U] = Lib_IntVector_Intrinsics_vec128_zero;
  load_precompute_r(pre, key);
}

/* SNIPPET_END: Hacl_Gf128_NI_gcm_init */

/* SNIPPET_START: Hacl_Gf128_NI_gcm_update_blocks */

void
Hacl_Gf128_NI_gcm_update_blocks(
  Lib_IntVector_Intrinsics_vec128 *ctx,
  uint32_t len,
  uint8_t *text
)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + (uint32_t)1U;
  uint32_t len0 = len / (uint32_t)64U * (uint32_t)64U;
  uint8_t *t0 = text;
  if (len0 > (uint32_t)0U)
  {
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 f[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *b4 = f;
    uint32_t nb = len0 / (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < nb; i++)
    {
      uint8_t *tb = t0 + i * (uint32_t)64U;
      b4[0U] = Lib_IntVector_Intrinsics_vec128_load_be(tb);
      b4[1U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + (uint32_t)16U);
      b4[2U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + (uint32_t)32U);
      b4[3U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + (uint32_t)48U);
      b4[0U] = Lib_IntVector_Intrinsics_vec128_xor(acc[0U], b4[0U]);
      normalize4(acc, b4, pre);
    }
  }
  uint32_t len1 = len - len0;
  uint8_t *t1 = text + len0;
  Lib_IntVector_Intrinsics_vec128 *r1 = pre + (uint32_t)3U;
  uint32_t nb = len1 / (uint32_t)16U;
  uint32_t rem = len1 % (uint32_t)16U;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *tb = t1 + i * (uint32_t)16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    elem = Lib_IntVector_Intrinsics_vec128_load_be(tb);
    fadd0(acc, &elem);
    fmul0(acc, r1);
  }
  if (rem > (uint32_t)0U)
  {
    uint8_t *last = t1 + nb * (uint32_t)16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    uint8_t b[16U] = { 0U };
    memcpy(b, last, rem * sizeof (uint8_t));
    elem = Lib_IntVector_Intrinsics_vec128_load_be(b);
    fadd0(acc, &elem);
    fmul0(acc, r1);
    return;
  }
}

/* SNIPPET_END: Hacl_Gf128_NI_gcm_update_blocks */

/* SNIPPET_START: Hacl_Gf128_NI_gcm_update_padded */

void
(*Hacl_Gf128_NI_gcm_update_padded)(
  Lib_IntVector_Intrinsics_vec128 *x0,
  uint32_t x1,
  uint8_t *x2
) = Hacl_Gf128_NI_gcm_update_blocks;

/* SNIPPET_END: Hacl_Gf128_NI_gcm_update_padded */

/* SNIPPET_START: Hacl_Gf128_NI_gcm_emit */

void Hacl_Gf128_NI_gcm_emit(uint8_t *tag, Lib_IntVector_Intrinsics_vec128 *ctx)
{
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128_store_be(tag, acc[0U]);
}

/* SNIPPET_END: Hacl_Gf128_NI_gcm_emit */

/* SNIPPET_START: Hacl_Gf128_NI_ghash */

inline void Hacl_Gf128_NI_ghash(uint8_t *tag, uint32_t len, uint8_t *text, uint8_t *key)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ctx[5U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *acc = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre0 = ctx + (uint32_t)1U;
  acc[0U] = Lib_IntVector_Intrinsics_vec128_zero;
  load_precompute_r(pre0, key);
  Lib_IntVector_Intrinsics_vec128 *acc0 = ctx;
  Lib_IntVector_Intrinsics_vec128 *pre = ctx + (uint32_t)1U;
  uint32_t len0 = len / (uint32_t)64U * (uint32_t)64U;
  uint8_t *t0 = text;
  if (len0 > (uint32_t)0U)
  {
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 f[4U] KRML_POST_ALIGN(16) = { 0U };
    Lib_IntVector_Intrinsics_vec128 *b4 = f;
    uint32_t nb = len0 / (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < nb; i++)
    {
      uint8_t *tb = t0 + i * (uint32_t)64U;
      b4[0U] = Lib_IntVector_Intrinsics_vec128_load_be(tb);
      b4[1U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + (uint32_t)16U);
      b4[2U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + (uint32_t)32U);
      b4[3U] = Lib_IntVector_Intrinsics_vec128_load_be(tb + (uint32_t)48U);
      b4[0U] = Lib_IntVector_Intrinsics_vec128_xor(acc0[0U], b4[0U]);
      normalize4(acc0, b4, pre);
    }
  }
  uint32_t len1 = len - len0;
  uint8_t *t1 = text + len0;
  Lib_IntVector_Intrinsics_vec128 *r1 = pre + (uint32_t)3U;
  uint32_t nb = len1 / (uint32_t)16U;
  uint32_t rem = len1 % (uint32_t)16U;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *tb = t1 + i * (uint32_t)16U;
    Lib_IntVector_Intrinsics_vec128 elem = Lib_IntVector_Intrinsics_vec128_zero;
    elem = Lib_IntVector_Intrinsics_vec128_load_be(tb);
    fadd0(acc0, &elem);
    fmul0(acc0, r1);
  }
  if (rem > (uint32_t)0U)
  {
    uint8_t *last = t1 + nb * (uint32_t)16U;
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

/* SNIPPET_END: Hacl_Gf128_NI_ghash */

