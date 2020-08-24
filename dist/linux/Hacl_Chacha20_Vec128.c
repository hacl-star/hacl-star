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


#include "Hacl_Chacha20_Vec128.h"

static inline void double_round_128(Lib_IntVector_Intrinsics_vec128 *st)
{
  Lib_IntVector_Intrinsics_vec128 std0;
  Lib_IntVector_Intrinsics_vec128 std1;
  Lib_IntVector_Intrinsics_vec128 std2;
  Lib_IntVector_Intrinsics_vec128 std3;
  Lib_IntVector_Intrinsics_vec128 std4;
  Lib_IntVector_Intrinsics_vec128 std5;
  Lib_IntVector_Intrinsics_vec128 std6;
  Lib_IntVector_Intrinsics_vec128 std7;
  Lib_IntVector_Intrinsics_vec128 std8;
  Lib_IntVector_Intrinsics_vec128 std9;
  Lib_IntVector_Intrinsics_vec128 std10;
  Lib_IntVector_Intrinsics_vec128 std11;
  Lib_IntVector_Intrinsics_vec128 std12;
  Lib_IntVector_Intrinsics_vec128 std13;
  Lib_IntVector_Intrinsics_vec128 std14;
  Lib_IntVector_Intrinsics_vec128 std15;
  Lib_IntVector_Intrinsics_vec128 std16;
  Lib_IntVector_Intrinsics_vec128 std17;
  Lib_IntVector_Intrinsics_vec128 std18;
  Lib_IntVector_Intrinsics_vec128 std19;
  Lib_IntVector_Intrinsics_vec128 std20;
  Lib_IntVector_Intrinsics_vec128 std21;
  Lib_IntVector_Intrinsics_vec128 std22;
  Lib_IntVector_Intrinsics_vec128 std23;
  Lib_IntVector_Intrinsics_vec128 std24;
  Lib_IntVector_Intrinsics_vec128 std25;
  Lib_IntVector_Intrinsics_vec128 std26;
  Lib_IntVector_Intrinsics_vec128 std27;
  Lib_IntVector_Intrinsics_vec128 std28;
  Lib_IntVector_Intrinsics_vec128 std29;
  Lib_IntVector_Intrinsics_vec128 std30;
  Lib_IntVector_Intrinsics_vec128 std;
  st[0U] = Lib_IntVector_Intrinsics_vec128_add32(st[0U], st[4U]);
  std0 = Lib_IntVector_Intrinsics_vec128_xor(st[12U], st[0U]);
  st[12U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std0, (u32)16U);
  st[8U] = Lib_IntVector_Intrinsics_vec128_add32(st[8U], st[12U]);
  std1 = Lib_IntVector_Intrinsics_vec128_xor(st[4U], st[8U]);
  st[4U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std1, (u32)12U);
  st[0U] = Lib_IntVector_Intrinsics_vec128_add32(st[0U], st[4U]);
  std2 = Lib_IntVector_Intrinsics_vec128_xor(st[12U], st[0U]);
  st[12U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std2, (u32)8U);
  st[8U] = Lib_IntVector_Intrinsics_vec128_add32(st[8U], st[12U]);
  std3 = Lib_IntVector_Intrinsics_vec128_xor(st[4U], st[8U]);
  st[4U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std3, (u32)7U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_add32(st[1U], st[5U]);
  std4 = Lib_IntVector_Intrinsics_vec128_xor(st[13U], st[1U]);
  st[13U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std4, (u32)16U);
  st[9U] = Lib_IntVector_Intrinsics_vec128_add32(st[9U], st[13U]);
  std5 = Lib_IntVector_Intrinsics_vec128_xor(st[5U], st[9U]);
  st[5U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std5, (u32)12U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_add32(st[1U], st[5U]);
  std6 = Lib_IntVector_Intrinsics_vec128_xor(st[13U], st[1U]);
  st[13U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std6, (u32)8U);
  st[9U] = Lib_IntVector_Intrinsics_vec128_add32(st[9U], st[13U]);
  std7 = Lib_IntVector_Intrinsics_vec128_xor(st[5U], st[9U]);
  st[5U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std7, (u32)7U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_add32(st[2U], st[6U]);
  std8 = Lib_IntVector_Intrinsics_vec128_xor(st[14U], st[2U]);
  st[14U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std8, (u32)16U);
  st[10U] = Lib_IntVector_Intrinsics_vec128_add32(st[10U], st[14U]);
  std9 = Lib_IntVector_Intrinsics_vec128_xor(st[6U], st[10U]);
  st[6U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std9, (u32)12U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_add32(st[2U], st[6U]);
  std10 = Lib_IntVector_Intrinsics_vec128_xor(st[14U], st[2U]);
  st[14U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std10, (u32)8U);
  st[10U] = Lib_IntVector_Intrinsics_vec128_add32(st[10U], st[14U]);
  std11 = Lib_IntVector_Intrinsics_vec128_xor(st[6U], st[10U]);
  st[6U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std11, (u32)7U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_add32(st[3U], st[7U]);
  std12 = Lib_IntVector_Intrinsics_vec128_xor(st[15U], st[3U]);
  st[15U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std12, (u32)16U);
  st[11U] = Lib_IntVector_Intrinsics_vec128_add32(st[11U], st[15U]);
  std13 = Lib_IntVector_Intrinsics_vec128_xor(st[7U], st[11U]);
  st[7U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std13, (u32)12U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_add32(st[3U], st[7U]);
  std14 = Lib_IntVector_Intrinsics_vec128_xor(st[15U], st[3U]);
  st[15U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std14, (u32)8U);
  st[11U] = Lib_IntVector_Intrinsics_vec128_add32(st[11U], st[15U]);
  std15 = Lib_IntVector_Intrinsics_vec128_xor(st[7U], st[11U]);
  st[7U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std15, (u32)7U);
  st[0U] = Lib_IntVector_Intrinsics_vec128_add32(st[0U], st[5U]);
  std16 = Lib_IntVector_Intrinsics_vec128_xor(st[15U], st[0U]);
  st[15U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std16, (u32)16U);
  st[10U] = Lib_IntVector_Intrinsics_vec128_add32(st[10U], st[15U]);
  std17 = Lib_IntVector_Intrinsics_vec128_xor(st[5U], st[10U]);
  st[5U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std17, (u32)12U);
  st[0U] = Lib_IntVector_Intrinsics_vec128_add32(st[0U], st[5U]);
  std18 = Lib_IntVector_Intrinsics_vec128_xor(st[15U], st[0U]);
  st[15U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std18, (u32)8U);
  st[10U] = Lib_IntVector_Intrinsics_vec128_add32(st[10U], st[15U]);
  std19 = Lib_IntVector_Intrinsics_vec128_xor(st[5U], st[10U]);
  st[5U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std19, (u32)7U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_add32(st[1U], st[6U]);
  std20 = Lib_IntVector_Intrinsics_vec128_xor(st[12U], st[1U]);
  st[12U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std20, (u32)16U);
  st[11U] = Lib_IntVector_Intrinsics_vec128_add32(st[11U], st[12U]);
  std21 = Lib_IntVector_Intrinsics_vec128_xor(st[6U], st[11U]);
  st[6U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std21, (u32)12U);
  st[1U] = Lib_IntVector_Intrinsics_vec128_add32(st[1U], st[6U]);
  std22 = Lib_IntVector_Intrinsics_vec128_xor(st[12U], st[1U]);
  st[12U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std22, (u32)8U);
  st[11U] = Lib_IntVector_Intrinsics_vec128_add32(st[11U], st[12U]);
  std23 = Lib_IntVector_Intrinsics_vec128_xor(st[6U], st[11U]);
  st[6U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std23, (u32)7U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_add32(st[2U], st[7U]);
  std24 = Lib_IntVector_Intrinsics_vec128_xor(st[13U], st[2U]);
  st[13U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std24, (u32)16U);
  st[8U] = Lib_IntVector_Intrinsics_vec128_add32(st[8U], st[13U]);
  std25 = Lib_IntVector_Intrinsics_vec128_xor(st[7U], st[8U]);
  st[7U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std25, (u32)12U);
  st[2U] = Lib_IntVector_Intrinsics_vec128_add32(st[2U], st[7U]);
  std26 = Lib_IntVector_Intrinsics_vec128_xor(st[13U], st[2U]);
  st[13U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std26, (u32)8U);
  st[8U] = Lib_IntVector_Intrinsics_vec128_add32(st[8U], st[13U]);
  std27 = Lib_IntVector_Intrinsics_vec128_xor(st[7U], st[8U]);
  st[7U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std27, (u32)7U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_add32(st[3U], st[4U]);
  std28 = Lib_IntVector_Intrinsics_vec128_xor(st[14U], st[3U]);
  st[14U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std28, (u32)16U);
  st[9U] = Lib_IntVector_Intrinsics_vec128_add32(st[9U], st[14U]);
  std29 = Lib_IntVector_Intrinsics_vec128_xor(st[4U], st[9U]);
  st[4U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std29, (u32)12U);
  st[3U] = Lib_IntVector_Intrinsics_vec128_add32(st[3U], st[4U]);
  std30 = Lib_IntVector_Intrinsics_vec128_xor(st[14U], st[3U]);
  st[14U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std30, (u32)8U);
  st[9U] = Lib_IntVector_Intrinsics_vec128_add32(st[9U], st[14U]);
  std = Lib_IntVector_Intrinsics_vec128_xor(st[4U], st[9U]);
  st[4U] = Lib_IntVector_Intrinsics_vec128_rotate_left32(std, (u32)7U);
}

static inline void
chacha20_core_128(
  Lib_IntVector_Intrinsics_vec128 *k,
  Lib_IntVector_Intrinsics_vec128 *ctx,
  u32 ctr
)
{
  u32 ctr_u32;
  Lib_IntVector_Intrinsics_vec128 cv;
  memcpy(k, ctx, (u32)16U * sizeof (Lib_IntVector_Intrinsics_vec128));
  ctr_u32 = (u32)4U * ctr;
  cv = Lib_IntVector_Intrinsics_vec128_load32(ctr_u32);
  k[12U] = Lib_IntVector_Intrinsics_vec128_add32(k[12U], cv);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  double_round_128(k);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
    {
      Lib_IntVector_Intrinsics_vec128 *os = k;
      Lib_IntVector_Intrinsics_vec128 x = Lib_IntVector_Intrinsics_vec128_add32(k[i], ctx[i]);
      os[i] = x;
    }
  }
  k[12U] = Lib_IntVector_Intrinsics_vec128_add32(k[12U], cv);
}

static inline void
chacha20_init_128(Lib_IntVector_Intrinsics_vec128 *ctx, u8 *k, u8 *n, u32 ctr)
{
  u32 ctx1[16U] = { 0U };
  u32 *uu____0 = ctx1;
  u32 *uu____1;
  u32 *uu____2;
  Lib_IntVector_Intrinsics_vec128 ctr1;
  Lib_IntVector_Intrinsics_vec128 c12;
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
      Lib_IntVector_Intrinsics_vec128 *os = ctx;
      u32 x = ctx1[i];
      Lib_IntVector_Intrinsics_vec128 x0 = Lib_IntVector_Intrinsics_vec128_load32(x);
      os[i] = x0;
    }
  }
  ctr1 = Lib_IntVector_Intrinsics_vec128_load32s((u32)0U, (u32)1U, (u32)2U, (u32)3U);
  c12 = ctx[12U];
  ctx[12U] = Lib_IntVector_Intrinsics_vec128_add32(c12, ctr1);
}

void
Hacl_Chacha20_Vec128_chacha20_encrypt_128(u32 len, u8 *out, u8 *text, u8 *key, u8 *n, u32 ctr)
{
  Lib_IntVector_Intrinsics_vec128 ctx[16U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)16U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    u32 rem;
    u32 nb;
    u32 rem1;
    chacha20_init_128(ctx, key, n, ctr);
    rem = len % (u32)256U;
    nb = len / (u32)256U;
    rem1 = len % (u32)256U;
    {
      u32 i;
      for (i = (u32)0U; i < nb; i++)
      {
        u8 *uu____0 = out + i * (u32)256U;
        u8 *uu____1 = text + i * (u32)256U;
        Lib_IntVector_Intrinsics_vec128 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
        chacha20_core_128(k, ctx, i);
        {
          Lib_IntVector_Intrinsics_vec128 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec128 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec128 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec128 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec128
          v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v2_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v3_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v0__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v1__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v2__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128
          v3__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128 v0 = v0__;
          Lib_IntVector_Intrinsics_vec128 v1 = v1__;
          Lib_IntVector_Intrinsics_vec128 v2 = v2__;
          Lib_IntVector_Intrinsics_vec128 v3 = v3__;
          Lib_IntVector_Intrinsics_vec128 v010 = k[4U];
          Lib_IntVector_Intrinsics_vec128 v110 = k[5U];
          Lib_IntVector_Intrinsics_vec128 v210 = k[6U];
          Lib_IntVector_Intrinsics_vec128 v310 = k[7U];
          Lib_IntVector_Intrinsics_vec128
          v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v0__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v1__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v2__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128
          v3__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128 v4 = v0__0;
          Lib_IntVector_Intrinsics_vec128 v5 = v1__0;
          Lib_IntVector_Intrinsics_vec128 v6 = v2__0;
          Lib_IntVector_Intrinsics_vec128 v7 = v3__0;
          Lib_IntVector_Intrinsics_vec128 v011 = k[8U];
          Lib_IntVector_Intrinsics_vec128 v111 = k[9U];
          Lib_IntVector_Intrinsics_vec128 v211 = k[10U];
          Lib_IntVector_Intrinsics_vec128 v311 = k[11U];
          Lib_IntVector_Intrinsics_vec128
          v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128
          v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128 v8 = v0__1;
          Lib_IntVector_Intrinsics_vec128 v9 = v1__1;
          Lib_IntVector_Intrinsics_vec128 v10 = v2__1;
          Lib_IntVector_Intrinsics_vec128 v11 = v3__1;
          Lib_IntVector_Intrinsics_vec128 v01 = k[12U];
          Lib_IntVector_Intrinsics_vec128 v120 = k[13U];
          Lib_IntVector_Intrinsics_vec128 v21 = k[14U];
          Lib_IntVector_Intrinsics_vec128 v31 = k[15U];
          Lib_IntVector_Intrinsics_vec128
          v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v0__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v1__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v2__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128
          v3__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128 v12 = v0__2;
          Lib_IntVector_Intrinsics_vec128 v13 = v1__2;
          Lib_IntVector_Intrinsics_vec128 v14 = v2__2;
          Lib_IntVector_Intrinsics_vec128 v15 = v3__2;
          k[0U] = v0;
          k[1U] = v4;
          k[2U] = v8;
          k[3U] = v12;
          k[4U] = v1;
          k[5U] = v5;
          k[6U] = v9;
          k[7U] = v13;
          k[8U] = v2;
          k[9U] = v6;
          k[10U] = v10;
          k[11U] = v14;
          k[12U] = v3;
          k[13U] = v7;
          k[14U] = v11;
          k[15U] = v15;
          {
            u32 i0;
            for (i0 = (u32)0U; i0 < (u32)16U; i0++)
            {
              Lib_IntVector_Intrinsics_vec128
              x = Lib_IntVector_Intrinsics_vec128_load_le(uu____1 + i0 * (u32)16U);
              Lib_IntVector_Intrinsics_vec128 y = Lib_IntVector_Intrinsics_vec128_xor(x, k[i0]);
              Lib_IntVector_Intrinsics_vec128_store_le(uu____0 + i0 * (u32)16U, y);
            }
          }
        }
      }
    }
    if (rem1 > (u32)0U)
    {
      u8 *uu____2 = out + nb * (u32)256U;
      u8 *uu____3 = text + nb * (u32)256U;
      u8 plain[256U] = { 0U };
      memcpy(plain, uu____3, rem * sizeof (u8));
      {
        Lib_IntVector_Intrinsics_vec128 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
        chacha20_core_128(k, ctx, nb);
        {
          Lib_IntVector_Intrinsics_vec128 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec128 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec128 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec128 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec128
          v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v2_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v3_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v0__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v1__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v2__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128
          v3__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128 v0 = v0__;
          Lib_IntVector_Intrinsics_vec128 v1 = v1__;
          Lib_IntVector_Intrinsics_vec128 v2 = v2__;
          Lib_IntVector_Intrinsics_vec128 v3 = v3__;
          Lib_IntVector_Intrinsics_vec128 v010 = k[4U];
          Lib_IntVector_Intrinsics_vec128 v110 = k[5U];
          Lib_IntVector_Intrinsics_vec128 v210 = k[6U];
          Lib_IntVector_Intrinsics_vec128 v310 = k[7U];
          Lib_IntVector_Intrinsics_vec128
          v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v0__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v1__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v2__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128
          v3__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128 v4 = v0__0;
          Lib_IntVector_Intrinsics_vec128 v5 = v1__0;
          Lib_IntVector_Intrinsics_vec128 v6 = v2__0;
          Lib_IntVector_Intrinsics_vec128 v7 = v3__0;
          Lib_IntVector_Intrinsics_vec128 v011 = k[8U];
          Lib_IntVector_Intrinsics_vec128 v111 = k[9U];
          Lib_IntVector_Intrinsics_vec128 v211 = k[10U];
          Lib_IntVector_Intrinsics_vec128 v311 = k[11U];
          Lib_IntVector_Intrinsics_vec128
          v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128
          v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128 v8 = v0__1;
          Lib_IntVector_Intrinsics_vec128 v9 = v1__1;
          Lib_IntVector_Intrinsics_vec128 v10 = v2__1;
          Lib_IntVector_Intrinsics_vec128 v11 = v3__1;
          Lib_IntVector_Intrinsics_vec128 v01 = k[12U];
          Lib_IntVector_Intrinsics_vec128 v120 = k[13U];
          Lib_IntVector_Intrinsics_vec128 v21 = k[14U];
          Lib_IntVector_Intrinsics_vec128 v31 = k[15U];
          Lib_IntVector_Intrinsics_vec128
          v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v0__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v1__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v2__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128
          v3__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128 v12 = v0__2;
          Lib_IntVector_Intrinsics_vec128 v13 = v1__2;
          Lib_IntVector_Intrinsics_vec128 v14 = v2__2;
          Lib_IntVector_Intrinsics_vec128 v15 = v3__2;
          k[0U] = v0;
          k[1U] = v4;
          k[2U] = v8;
          k[3U] = v12;
          k[4U] = v1;
          k[5U] = v5;
          k[6U] = v9;
          k[7U] = v13;
          k[8U] = v2;
          k[9U] = v6;
          k[10U] = v10;
          k[11U] = v14;
          k[12U] = v3;
          k[13U] = v7;
          k[14U] = v11;
          k[15U] = v15;
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              Lib_IntVector_Intrinsics_vec128
              x = Lib_IntVector_Intrinsics_vec128_load_le(plain + i * (u32)16U);
              Lib_IntVector_Intrinsics_vec128 y = Lib_IntVector_Intrinsics_vec128_xor(x, k[i]);
              Lib_IntVector_Intrinsics_vec128_store_le(plain + i * (u32)16U, y);
            }
          }
          memcpy(uu____2, plain, rem * sizeof (u8));
        }
      }
    }
  }
}

void
Hacl_Chacha20_Vec128_chacha20_decrypt_128(
  u32 len,
  u8 *out,
  u8 *cipher,
  u8 *key,
  u8 *n,
  u32 ctr
)
{
  Lib_IntVector_Intrinsics_vec128 ctx[16U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)16U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    u32 rem;
    u32 nb;
    u32 rem1;
    chacha20_init_128(ctx, key, n, ctr);
    rem = len % (u32)256U;
    nb = len / (u32)256U;
    rem1 = len % (u32)256U;
    {
      u32 i;
      for (i = (u32)0U; i < nb; i++)
      {
        u8 *uu____0 = out + i * (u32)256U;
        u8 *uu____1 = cipher + i * (u32)256U;
        Lib_IntVector_Intrinsics_vec128 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
        chacha20_core_128(k, ctx, i);
        {
          Lib_IntVector_Intrinsics_vec128 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec128 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec128 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec128 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec128
          v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v2_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v3_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v0__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v1__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v2__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128
          v3__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128 v0 = v0__;
          Lib_IntVector_Intrinsics_vec128 v1 = v1__;
          Lib_IntVector_Intrinsics_vec128 v2 = v2__;
          Lib_IntVector_Intrinsics_vec128 v3 = v3__;
          Lib_IntVector_Intrinsics_vec128 v010 = k[4U];
          Lib_IntVector_Intrinsics_vec128 v110 = k[5U];
          Lib_IntVector_Intrinsics_vec128 v210 = k[6U];
          Lib_IntVector_Intrinsics_vec128 v310 = k[7U];
          Lib_IntVector_Intrinsics_vec128
          v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v0__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v1__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v2__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128
          v3__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128 v4 = v0__0;
          Lib_IntVector_Intrinsics_vec128 v5 = v1__0;
          Lib_IntVector_Intrinsics_vec128 v6 = v2__0;
          Lib_IntVector_Intrinsics_vec128 v7 = v3__0;
          Lib_IntVector_Intrinsics_vec128 v011 = k[8U];
          Lib_IntVector_Intrinsics_vec128 v111 = k[9U];
          Lib_IntVector_Intrinsics_vec128 v211 = k[10U];
          Lib_IntVector_Intrinsics_vec128 v311 = k[11U];
          Lib_IntVector_Intrinsics_vec128
          v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128
          v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128 v8 = v0__1;
          Lib_IntVector_Intrinsics_vec128 v9 = v1__1;
          Lib_IntVector_Intrinsics_vec128 v10 = v2__1;
          Lib_IntVector_Intrinsics_vec128 v11 = v3__1;
          Lib_IntVector_Intrinsics_vec128 v01 = k[12U];
          Lib_IntVector_Intrinsics_vec128 v120 = k[13U];
          Lib_IntVector_Intrinsics_vec128 v21 = k[14U];
          Lib_IntVector_Intrinsics_vec128 v31 = k[15U];
          Lib_IntVector_Intrinsics_vec128
          v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v0__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v1__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v2__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128
          v3__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128 v12 = v0__2;
          Lib_IntVector_Intrinsics_vec128 v13 = v1__2;
          Lib_IntVector_Intrinsics_vec128 v14 = v2__2;
          Lib_IntVector_Intrinsics_vec128 v15 = v3__2;
          k[0U] = v0;
          k[1U] = v4;
          k[2U] = v8;
          k[3U] = v12;
          k[4U] = v1;
          k[5U] = v5;
          k[6U] = v9;
          k[7U] = v13;
          k[8U] = v2;
          k[9U] = v6;
          k[10U] = v10;
          k[11U] = v14;
          k[12U] = v3;
          k[13U] = v7;
          k[14U] = v11;
          k[15U] = v15;
          {
            u32 i0;
            for (i0 = (u32)0U; i0 < (u32)16U; i0++)
            {
              Lib_IntVector_Intrinsics_vec128
              x = Lib_IntVector_Intrinsics_vec128_load_le(uu____1 + i0 * (u32)16U);
              Lib_IntVector_Intrinsics_vec128 y = Lib_IntVector_Intrinsics_vec128_xor(x, k[i0]);
              Lib_IntVector_Intrinsics_vec128_store_le(uu____0 + i0 * (u32)16U, y);
            }
          }
        }
      }
    }
    if (rem1 > (u32)0U)
    {
      u8 *uu____2 = out + nb * (u32)256U;
      u8 *uu____3 = cipher + nb * (u32)256U;
      u8 plain[256U] = { 0U };
      memcpy(plain, uu____3, rem * sizeof (u8));
      {
        Lib_IntVector_Intrinsics_vec128 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
        chacha20_core_128(k, ctx, nb);
        {
          Lib_IntVector_Intrinsics_vec128 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec128 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec128 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec128 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec128
          v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec128
          v2_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v3_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec128
          v0__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v1__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec128
          v2__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128
          v3__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec128 v0 = v0__;
          Lib_IntVector_Intrinsics_vec128 v1 = v1__;
          Lib_IntVector_Intrinsics_vec128 v2 = v2__;
          Lib_IntVector_Intrinsics_vec128 v3 = v3__;
          Lib_IntVector_Intrinsics_vec128 v010 = k[4U];
          Lib_IntVector_Intrinsics_vec128 v110 = k[5U];
          Lib_IntVector_Intrinsics_vec128 v210 = k[6U];
          Lib_IntVector_Intrinsics_vec128 v310 = k[7U];
          Lib_IntVector_Intrinsics_vec128
          v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v010, v110);
          Lib_IntVector_Intrinsics_vec128
          v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v210, v310);
          Lib_IntVector_Intrinsics_vec128
          v0__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v1__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec128
          v2__0 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128
          v3__0 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec128 v4 = v0__0;
          Lib_IntVector_Intrinsics_vec128 v5 = v1__0;
          Lib_IntVector_Intrinsics_vec128 v6 = v2__0;
          Lib_IntVector_Intrinsics_vec128 v7 = v3__0;
          Lib_IntVector_Intrinsics_vec128 v011 = k[8U];
          Lib_IntVector_Intrinsics_vec128 v111 = k[9U];
          Lib_IntVector_Intrinsics_vec128 v211 = k[10U];
          Lib_IntVector_Intrinsics_vec128 v311 = k[11U];
          Lib_IntVector_Intrinsics_vec128
          v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v011, v111);
          Lib_IntVector_Intrinsics_vec128
          v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v211, v311);
          Lib_IntVector_Intrinsics_vec128
          v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
          Lib_IntVector_Intrinsics_vec128
          v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128
          v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
          Lib_IntVector_Intrinsics_vec128 v8 = v0__1;
          Lib_IntVector_Intrinsics_vec128 v9 = v1__1;
          Lib_IntVector_Intrinsics_vec128 v10 = v2__1;
          Lib_IntVector_Intrinsics_vec128 v11 = v3__1;
          Lib_IntVector_Intrinsics_vec128 v01 = k[12U];
          Lib_IntVector_Intrinsics_vec128 v120 = k[13U];
          Lib_IntVector_Intrinsics_vec128 v21 = k[14U];
          Lib_IntVector_Intrinsics_vec128 v31 = k[15U];
          Lib_IntVector_Intrinsics_vec128
          v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v120);
          Lib_IntVector_Intrinsics_vec128
          v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec128
          v0__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v1__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
          Lib_IntVector_Intrinsics_vec128
          v2__2 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128
          v3__2 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
          Lib_IntVector_Intrinsics_vec128 v12 = v0__2;
          Lib_IntVector_Intrinsics_vec128 v13 = v1__2;
          Lib_IntVector_Intrinsics_vec128 v14 = v2__2;
          Lib_IntVector_Intrinsics_vec128 v15 = v3__2;
          k[0U] = v0;
          k[1U] = v4;
          k[2U] = v8;
          k[3U] = v12;
          k[4U] = v1;
          k[5U] = v5;
          k[6U] = v9;
          k[7U] = v13;
          k[8U] = v2;
          k[9U] = v6;
          k[10U] = v10;
          k[11U] = v14;
          k[12U] = v3;
          k[13U] = v7;
          k[14U] = v11;
          k[15U] = v15;
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              Lib_IntVector_Intrinsics_vec128
              x = Lib_IntVector_Intrinsics_vec128_load_le(plain + i * (u32)16U);
              Lib_IntVector_Intrinsics_vec128 y = Lib_IntVector_Intrinsics_vec128_xor(x, k[i]);
              Lib_IntVector_Intrinsics_vec128_store_le(plain + i * (u32)16U, y);
            }
          }
          memcpy(uu____2, plain, rem * sizeof (u8));
        }
      }
    }
  }
}

