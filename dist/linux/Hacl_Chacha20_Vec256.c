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


#include "Hacl_Chacha20_Vec256.h"

static inline void double_round_256(Lib_IntVector_Intrinsics_vec256 *st)
{
  Lib_IntVector_Intrinsics_vec256 std0;
  Lib_IntVector_Intrinsics_vec256 std1;
  Lib_IntVector_Intrinsics_vec256 std2;
  Lib_IntVector_Intrinsics_vec256 std3;
  Lib_IntVector_Intrinsics_vec256 std4;
  Lib_IntVector_Intrinsics_vec256 std5;
  Lib_IntVector_Intrinsics_vec256 std6;
  Lib_IntVector_Intrinsics_vec256 std7;
  Lib_IntVector_Intrinsics_vec256 std8;
  Lib_IntVector_Intrinsics_vec256 std9;
  Lib_IntVector_Intrinsics_vec256 std10;
  Lib_IntVector_Intrinsics_vec256 std11;
  Lib_IntVector_Intrinsics_vec256 std12;
  Lib_IntVector_Intrinsics_vec256 std13;
  Lib_IntVector_Intrinsics_vec256 std14;
  Lib_IntVector_Intrinsics_vec256 std15;
  Lib_IntVector_Intrinsics_vec256 std16;
  Lib_IntVector_Intrinsics_vec256 std17;
  Lib_IntVector_Intrinsics_vec256 std18;
  Lib_IntVector_Intrinsics_vec256 std19;
  Lib_IntVector_Intrinsics_vec256 std20;
  Lib_IntVector_Intrinsics_vec256 std21;
  Lib_IntVector_Intrinsics_vec256 std22;
  Lib_IntVector_Intrinsics_vec256 std23;
  Lib_IntVector_Intrinsics_vec256 std24;
  Lib_IntVector_Intrinsics_vec256 std25;
  Lib_IntVector_Intrinsics_vec256 std26;
  Lib_IntVector_Intrinsics_vec256 std27;
  Lib_IntVector_Intrinsics_vec256 std28;
  Lib_IntVector_Intrinsics_vec256 std29;
  Lib_IntVector_Intrinsics_vec256 std30;
  Lib_IntVector_Intrinsics_vec256 std;
  st[0U] = Lib_IntVector_Intrinsics_vec256_add32(st[0U], st[4U]);
  std0 = Lib_IntVector_Intrinsics_vec256_xor(st[12U], st[0U]);
  st[12U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std0, (u32)16U);
  st[8U] = Lib_IntVector_Intrinsics_vec256_add32(st[8U], st[12U]);
  std1 = Lib_IntVector_Intrinsics_vec256_xor(st[4U], st[8U]);
  st[4U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std1, (u32)12U);
  st[0U] = Lib_IntVector_Intrinsics_vec256_add32(st[0U], st[4U]);
  std2 = Lib_IntVector_Intrinsics_vec256_xor(st[12U], st[0U]);
  st[12U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std2, (u32)8U);
  st[8U] = Lib_IntVector_Intrinsics_vec256_add32(st[8U], st[12U]);
  std3 = Lib_IntVector_Intrinsics_vec256_xor(st[4U], st[8U]);
  st[4U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std3, (u32)7U);
  st[1U] = Lib_IntVector_Intrinsics_vec256_add32(st[1U], st[5U]);
  std4 = Lib_IntVector_Intrinsics_vec256_xor(st[13U], st[1U]);
  st[13U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std4, (u32)16U);
  st[9U] = Lib_IntVector_Intrinsics_vec256_add32(st[9U], st[13U]);
  std5 = Lib_IntVector_Intrinsics_vec256_xor(st[5U], st[9U]);
  st[5U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std5, (u32)12U);
  st[1U] = Lib_IntVector_Intrinsics_vec256_add32(st[1U], st[5U]);
  std6 = Lib_IntVector_Intrinsics_vec256_xor(st[13U], st[1U]);
  st[13U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std6, (u32)8U);
  st[9U] = Lib_IntVector_Intrinsics_vec256_add32(st[9U], st[13U]);
  std7 = Lib_IntVector_Intrinsics_vec256_xor(st[5U], st[9U]);
  st[5U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std7, (u32)7U);
  st[2U] = Lib_IntVector_Intrinsics_vec256_add32(st[2U], st[6U]);
  std8 = Lib_IntVector_Intrinsics_vec256_xor(st[14U], st[2U]);
  st[14U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std8, (u32)16U);
  st[10U] = Lib_IntVector_Intrinsics_vec256_add32(st[10U], st[14U]);
  std9 = Lib_IntVector_Intrinsics_vec256_xor(st[6U], st[10U]);
  st[6U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std9, (u32)12U);
  st[2U] = Lib_IntVector_Intrinsics_vec256_add32(st[2U], st[6U]);
  std10 = Lib_IntVector_Intrinsics_vec256_xor(st[14U], st[2U]);
  st[14U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std10, (u32)8U);
  st[10U] = Lib_IntVector_Intrinsics_vec256_add32(st[10U], st[14U]);
  std11 = Lib_IntVector_Intrinsics_vec256_xor(st[6U], st[10U]);
  st[6U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std11, (u32)7U);
  st[3U] = Lib_IntVector_Intrinsics_vec256_add32(st[3U], st[7U]);
  std12 = Lib_IntVector_Intrinsics_vec256_xor(st[15U], st[3U]);
  st[15U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std12, (u32)16U);
  st[11U] = Lib_IntVector_Intrinsics_vec256_add32(st[11U], st[15U]);
  std13 = Lib_IntVector_Intrinsics_vec256_xor(st[7U], st[11U]);
  st[7U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std13, (u32)12U);
  st[3U] = Lib_IntVector_Intrinsics_vec256_add32(st[3U], st[7U]);
  std14 = Lib_IntVector_Intrinsics_vec256_xor(st[15U], st[3U]);
  st[15U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std14, (u32)8U);
  st[11U] = Lib_IntVector_Intrinsics_vec256_add32(st[11U], st[15U]);
  std15 = Lib_IntVector_Intrinsics_vec256_xor(st[7U], st[11U]);
  st[7U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std15, (u32)7U);
  st[0U] = Lib_IntVector_Intrinsics_vec256_add32(st[0U], st[5U]);
  std16 = Lib_IntVector_Intrinsics_vec256_xor(st[15U], st[0U]);
  st[15U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std16, (u32)16U);
  st[10U] = Lib_IntVector_Intrinsics_vec256_add32(st[10U], st[15U]);
  std17 = Lib_IntVector_Intrinsics_vec256_xor(st[5U], st[10U]);
  st[5U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std17, (u32)12U);
  st[0U] = Lib_IntVector_Intrinsics_vec256_add32(st[0U], st[5U]);
  std18 = Lib_IntVector_Intrinsics_vec256_xor(st[15U], st[0U]);
  st[15U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std18, (u32)8U);
  st[10U] = Lib_IntVector_Intrinsics_vec256_add32(st[10U], st[15U]);
  std19 = Lib_IntVector_Intrinsics_vec256_xor(st[5U], st[10U]);
  st[5U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std19, (u32)7U);
  st[1U] = Lib_IntVector_Intrinsics_vec256_add32(st[1U], st[6U]);
  std20 = Lib_IntVector_Intrinsics_vec256_xor(st[12U], st[1U]);
  st[12U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std20, (u32)16U);
  st[11U] = Lib_IntVector_Intrinsics_vec256_add32(st[11U], st[12U]);
  std21 = Lib_IntVector_Intrinsics_vec256_xor(st[6U], st[11U]);
  st[6U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std21, (u32)12U);
  st[1U] = Lib_IntVector_Intrinsics_vec256_add32(st[1U], st[6U]);
  std22 = Lib_IntVector_Intrinsics_vec256_xor(st[12U], st[1U]);
  st[12U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std22, (u32)8U);
  st[11U] = Lib_IntVector_Intrinsics_vec256_add32(st[11U], st[12U]);
  std23 = Lib_IntVector_Intrinsics_vec256_xor(st[6U], st[11U]);
  st[6U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std23, (u32)7U);
  st[2U] = Lib_IntVector_Intrinsics_vec256_add32(st[2U], st[7U]);
  std24 = Lib_IntVector_Intrinsics_vec256_xor(st[13U], st[2U]);
  st[13U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std24, (u32)16U);
  st[8U] = Lib_IntVector_Intrinsics_vec256_add32(st[8U], st[13U]);
  std25 = Lib_IntVector_Intrinsics_vec256_xor(st[7U], st[8U]);
  st[7U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std25, (u32)12U);
  st[2U] = Lib_IntVector_Intrinsics_vec256_add32(st[2U], st[7U]);
  std26 = Lib_IntVector_Intrinsics_vec256_xor(st[13U], st[2U]);
  st[13U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std26, (u32)8U);
  st[8U] = Lib_IntVector_Intrinsics_vec256_add32(st[8U], st[13U]);
  std27 = Lib_IntVector_Intrinsics_vec256_xor(st[7U], st[8U]);
  st[7U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std27, (u32)7U);
  st[3U] = Lib_IntVector_Intrinsics_vec256_add32(st[3U], st[4U]);
  std28 = Lib_IntVector_Intrinsics_vec256_xor(st[14U], st[3U]);
  st[14U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std28, (u32)16U);
  st[9U] = Lib_IntVector_Intrinsics_vec256_add32(st[9U], st[14U]);
  std29 = Lib_IntVector_Intrinsics_vec256_xor(st[4U], st[9U]);
  st[4U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std29, (u32)12U);
  st[3U] = Lib_IntVector_Intrinsics_vec256_add32(st[3U], st[4U]);
  std30 = Lib_IntVector_Intrinsics_vec256_xor(st[14U], st[3U]);
  st[14U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std30, (u32)8U);
  st[9U] = Lib_IntVector_Intrinsics_vec256_add32(st[9U], st[14U]);
  std = Lib_IntVector_Intrinsics_vec256_xor(st[4U], st[9U]);
  st[4U] = Lib_IntVector_Intrinsics_vec256_rotate_left32(std, (u32)7U);
}

static inline void
chacha20_core_256(
  Lib_IntVector_Intrinsics_vec256 *k,
  Lib_IntVector_Intrinsics_vec256 *ctx,
  u32 ctr
)
{
  u32 ctr_u32;
  Lib_IntVector_Intrinsics_vec256 cv;
  memcpy(k, ctx, (u32)16U * sizeof (Lib_IntVector_Intrinsics_vec256));
  ctr_u32 = (u32)8U * ctr;
  cv = Lib_IntVector_Intrinsics_vec256_load32(ctr_u32);
  k[12U] = Lib_IntVector_Intrinsics_vec256_add32(k[12U], cv);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
    {
      Lib_IntVector_Intrinsics_vec256 *os = k;
      Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_add32(k[i], ctx[i]);
      os[i] = x;
    }
  }
  k[12U] = Lib_IntVector_Intrinsics_vec256_add32(k[12U], cv);
}

static inline void
chacha20_init_256(Lib_IntVector_Intrinsics_vec256 *ctx, u8 *k, u8 *n, u32 ctr)
{
  u32 ctx1[16U] = { 0U };
  u32 *uu____0 = ctx1;
  u32 *uu____1;
  u32 *uu____2;
  Lib_IntVector_Intrinsics_vec256 ctr1;
  Lib_IntVector_Intrinsics_vec256 c12;
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
      Lib_IntVector_Intrinsics_vec256 *os = ctx;
      u32 x = ctx1[i];
      Lib_IntVector_Intrinsics_vec256 x0 = Lib_IntVector_Intrinsics_vec256_load32(x);
      os[i] = x0;
    }
  }
  ctr1 =
    Lib_IntVector_Intrinsics_vec256_load32s((u32)0U,
      (u32)1U,
      (u32)2U,
      (u32)3U,
      (u32)4U,
      (u32)5U,
      (u32)6U,
      (u32)7U);
  c12 = ctx[12U];
  ctx[12U] = Lib_IntVector_Intrinsics_vec256_add32(c12, ctr1);
}

void
Hacl_Chacha20_Vec256_chacha20_encrypt_256(u32 len, u8 *out, u8 *text, u8 *key, u8 *n, u32 ctr)
{
  Lib_IntVector_Intrinsics_vec256 ctx[16U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)16U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    u32 rem;
    u32 nb;
    u32 rem1;
    chacha20_init_256(ctx, key, n, ctr);
    rem = len % (u32)512U;
    nb = len / (u32)512U;
    rem1 = len % (u32)512U;
    {
      u32 i;
      for (i = (u32)0U; i < nb; i++)
      {
        u8 *uu____0 = out + i * (u32)512U;
        u8 *uu____1 = text + i * (u32)512U;
        Lib_IntVector_Intrinsics_vec256 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        }
        chacha20_core_256(k, ctx, i);
        {
          Lib_IntVector_Intrinsics_vec256 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec256 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec256 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec256 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec256 v40 = k[4U];
          Lib_IntVector_Intrinsics_vec256 v50 = k[5U];
          Lib_IntVector_Intrinsics_vec256 v60 = k[6U];
          Lib_IntVector_Intrinsics_vec256 v70 = k[7U];
          Lib_IntVector_Intrinsics_vec256
          v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v4__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v5__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v6__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v7__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v0___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v1___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v2___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v3___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v4___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v5___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v6___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256
          v7___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256 v0 = v0___;
          Lib_IntVector_Intrinsics_vec256 v1 = v2___;
          Lib_IntVector_Intrinsics_vec256 v2 = v4___;
          Lib_IntVector_Intrinsics_vec256 v3 = v6___;
          Lib_IntVector_Intrinsics_vec256 v4 = v1___;
          Lib_IntVector_Intrinsics_vec256 v5 = v3___;
          Lib_IntVector_Intrinsics_vec256 v6 = v5___;
          Lib_IntVector_Intrinsics_vec256 v7 = v7___;
          Lib_IntVector_Intrinsics_vec256 v01 = k[8U];
          Lib_IntVector_Intrinsics_vec256 v110 = k[9U];
          Lib_IntVector_Intrinsics_vec256 v21 = k[10U];
          Lib_IntVector_Intrinsics_vec256 v31 = k[11U];
          Lib_IntVector_Intrinsics_vec256 v41 = k[12U];
          Lib_IntVector_Intrinsics_vec256 v51 = k[13U];
          Lib_IntVector_Intrinsics_vec256 v61 = k[14U];
          Lib_IntVector_Intrinsics_vec256 v71 = k[15U];
          Lib_IntVector_Intrinsics_vec256
          v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v4_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v5_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v6_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v7_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v4__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v5__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v6__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v7__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v0___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v1___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v2___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v3___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v4___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v5___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v6___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256
          v7___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256 v8 = v0___0;
          Lib_IntVector_Intrinsics_vec256 v9 = v2___0;
          Lib_IntVector_Intrinsics_vec256 v10 = v4___0;
          Lib_IntVector_Intrinsics_vec256 v11 = v6___0;
          Lib_IntVector_Intrinsics_vec256 v12 = v1___0;
          Lib_IntVector_Intrinsics_vec256 v13 = v3___0;
          Lib_IntVector_Intrinsics_vec256 v14 = v5___0;
          Lib_IntVector_Intrinsics_vec256 v15 = v7___0;
          k[0U] = v0;
          k[1U] = v8;
          k[2U] = v1;
          k[3U] = v9;
          k[4U] = v2;
          k[5U] = v10;
          k[6U] = v3;
          k[7U] = v11;
          k[8U] = v4;
          k[9U] = v12;
          k[10U] = v5;
          k[11U] = v13;
          k[12U] = v6;
          k[13U] = v14;
          k[14U] = v7;
          k[15U] = v15;
          {
            u32 i0;
            for (i0 = (u32)0U; i0 < (u32)16U; i0++)
            {
              Lib_IntVector_Intrinsics_vec256
              x = Lib_IntVector_Intrinsics_vec256_load_le(uu____1 + i0 * (u32)32U);
              Lib_IntVector_Intrinsics_vec256 y = Lib_IntVector_Intrinsics_vec256_xor(x, k[i0]);
              Lib_IntVector_Intrinsics_vec256_store_le(uu____0 + i0 * (u32)32U, y);
            }
          }
        }
      }
    }
    if (rem1 > (u32)0U)
    {
      u8 *uu____2 = out + nb * (u32)512U;
      u8 *uu____3 = text + nb * (u32)512U;
      u8 plain[512U] = { 0U };
      memcpy(plain, uu____3, rem * sizeof (u8));
      {
        Lib_IntVector_Intrinsics_vec256 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        }
        chacha20_core_256(k, ctx, nb);
        {
          Lib_IntVector_Intrinsics_vec256 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec256 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec256 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec256 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec256 v40 = k[4U];
          Lib_IntVector_Intrinsics_vec256 v50 = k[5U];
          Lib_IntVector_Intrinsics_vec256 v60 = k[6U];
          Lib_IntVector_Intrinsics_vec256 v70 = k[7U];
          Lib_IntVector_Intrinsics_vec256
          v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v4__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v5__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v6__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v7__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v0___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v1___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v2___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v3___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v4___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v5___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v6___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256
          v7___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256 v0 = v0___;
          Lib_IntVector_Intrinsics_vec256 v1 = v2___;
          Lib_IntVector_Intrinsics_vec256 v2 = v4___;
          Lib_IntVector_Intrinsics_vec256 v3 = v6___;
          Lib_IntVector_Intrinsics_vec256 v4 = v1___;
          Lib_IntVector_Intrinsics_vec256 v5 = v3___;
          Lib_IntVector_Intrinsics_vec256 v6 = v5___;
          Lib_IntVector_Intrinsics_vec256 v7 = v7___;
          Lib_IntVector_Intrinsics_vec256 v01 = k[8U];
          Lib_IntVector_Intrinsics_vec256 v110 = k[9U];
          Lib_IntVector_Intrinsics_vec256 v21 = k[10U];
          Lib_IntVector_Intrinsics_vec256 v31 = k[11U];
          Lib_IntVector_Intrinsics_vec256 v41 = k[12U];
          Lib_IntVector_Intrinsics_vec256 v51 = k[13U];
          Lib_IntVector_Intrinsics_vec256 v61 = k[14U];
          Lib_IntVector_Intrinsics_vec256 v71 = k[15U];
          Lib_IntVector_Intrinsics_vec256
          v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v4_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v5_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v6_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v7_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v4__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v5__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v6__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v7__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v0___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v1___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v2___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v3___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v4___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v5___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v6___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256
          v7___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256 v8 = v0___0;
          Lib_IntVector_Intrinsics_vec256 v9 = v2___0;
          Lib_IntVector_Intrinsics_vec256 v10 = v4___0;
          Lib_IntVector_Intrinsics_vec256 v11 = v6___0;
          Lib_IntVector_Intrinsics_vec256 v12 = v1___0;
          Lib_IntVector_Intrinsics_vec256 v13 = v3___0;
          Lib_IntVector_Intrinsics_vec256 v14 = v5___0;
          Lib_IntVector_Intrinsics_vec256 v15 = v7___0;
          k[0U] = v0;
          k[1U] = v8;
          k[2U] = v1;
          k[3U] = v9;
          k[4U] = v2;
          k[5U] = v10;
          k[6U] = v3;
          k[7U] = v11;
          k[8U] = v4;
          k[9U] = v12;
          k[10U] = v5;
          k[11U] = v13;
          k[12U] = v6;
          k[13U] = v14;
          k[14U] = v7;
          k[15U] = v15;
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              Lib_IntVector_Intrinsics_vec256
              x = Lib_IntVector_Intrinsics_vec256_load_le(plain + i * (u32)32U);
              Lib_IntVector_Intrinsics_vec256 y = Lib_IntVector_Intrinsics_vec256_xor(x, k[i]);
              Lib_IntVector_Intrinsics_vec256_store_le(plain + i * (u32)32U, y);
            }
          }
          memcpy(uu____2, plain, rem * sizeof (u8));
        }
      }
    }
  }
}

void
Hacl_Chacha20_Vec256_chacha20_decrypt_256(
  u32 len,
  u8 *out,
  u8 *cipher,
  u8 *key,
  u8 *n,
  u32 ctr
)
{
  Lib_IntVector_Intrinsics_vec256 ctx[16U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)16U; ++_i)
      ctx[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    u32 rem;
    u32 nb;
    u32 rem1;
    chacha20_init_256(ctx, key, n, ctr);
    rem = len % (u32)512U;
    nb = len / (u32)512U;
    rem1 = len % (u32)512U;
    {
      u32 i;
      for (i = (u32)0U; i < nb; i++)
      {
        u8 *uu____0 = out + i * (u32)512U;
        u8 *uu____1 = cipher + i * (u32)512U;
        Lib_IntVector_Intrinsics_vec256 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        }
        chacha20_core_256(k, ctx, i);
        {
          Lib_IntVector_Intrinsics_vec256 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec256 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec256 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec256 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec256 v40 = k[4U];
          Lib_IntVector_Intrinsics_vec256 v50 = k[5U];
          Lib_IntVector_Intrinsics_vec256 v60 = k[6U];
          Lib_IntVector_Intrinsics_vec256 v70 = k[7U];
          Lib_IntVector_Intrinsics_vec256
          v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v4__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v5__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v6__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v7__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v0___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v1___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v2___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v3___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v4___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v5___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v6___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256
          v7___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256 v0 = v0___;
          Lib_IntVector_Intrinsics_vec256 v1 = v2___;
          Lib_IntVector_Intrinsics_vec256 v2 = v4___;
          Lib_IntVector_Intrinsics_vec256 v3 = v6___;
          Lib_IntVector_Intrinsics_vec256 v4 = v1___;
          Lib_IntVector_Intrinsics_vec256 v5 = v3___;
          Lib_IntVector_Intrinsics_vec256 v6 = v5___;
          Lib_IntVector_Intrinsics_vec256 v7 = v7___;
          Lib_IntVector_Intrinsics_vec256 v01 = k[8U];
          Lib_IntVector_Intrinsics_vec256 v110 = k[9U];
          Lib_IntVector_Intrinsics_vec256 v21 = k[10U];
          Lib_IntVector_Intrinsics_vec256 v31 = k[11U];
          Lib_IntVector_Intrinsics_vec256 v41 = k[12U];
          Lib_IntVector_Intrinsics_vec256 v51 = k[13U];
          Lib_IntVector_Intrinsics_vec256 v61 = k[14U];
          Lib_IntVector_Intrinsics_vec256 v71 = k[15U];
          Lib_IntVector_Intrinsics_vec256
          v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v4_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v5_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v6_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v7_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v4__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v5__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v6__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v7__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v0___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v1___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v2___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v3___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v4___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v5___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v6___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256
          v7___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256 v8 = v0___0;
          Lib_IntVector_Intrinsics_vec256 v9 = v2___0;
          Lib_IntVector_Intrinsics_vec256 v10 = v4___0;
          Lib_IntVector_Intrinsics_vec256 v11 = v6___0;
          Lib_IntVector_Intrinsics_vec256 v12 = v1___0;
          Lib_IntVector_Intrinsics_vec256 v13 = v3___0;
          Lib_IntVector_Intrinsics_vec256 v14 = v5___0;
          Lib_IntVector_Intrinsics_vec256 v15 = v7___0;
          k[0U] = v0;
          k[1U] = v8;
          k[2U] = v1;
          k[3U] = v9;
          k[4U] = v2;
          k[5U] = v10;
          k[6U] = v3;
          k[7U] = v11;
          k[8U] = v4;
          k[9U] = v12;
          k[10U] = v5;
          k[11U] = v13;
          k[12U] = v6;
          k[13U] = v14;
          k[14U] = v7;
          k[15U] = v15;
          {
            u32 i0;
            for (i0 = (u32)0U; i0 < (u32)16U; i0++)
            {
              Lib_IntVector_Intrinsics_vec256
              x = Lib_IntVector_Intrinsics_vec256_load_le(uu____1 + i0 * (u32)32U);
              Lib_IntVector_Intrinsics_vec256 y = Lib_IntVector_Intrinsics_vec256_xor(x, k[i0]);
              Lib_IntVector_Intrinsics_vec256_store_le(uu____0 + i0 * (u32)32U, y);
            }
          }
        }
      }
    }
    if (rem1 > (u32)0U)
    {
      u8 *uu____2 = out + nb * (u32)512U;
      u8 *uu____3 = cipher + nb * (u32)512U;
      u8 plain[512U] = { 0U };
      memcpy(plain, uu____3, rem * sizeof (u8));
      {
        Lib_IntVector_Intrinsics_vec256 k[16U];
        {
          u32 _i;
          for (_i = 0U; _i < (u32)16U; ++_i)
            k[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        }
        chacha20_core_256(k, ctx, nb);
        {
          Lib_IntVector_Intrinsics_vec256 v00 = k[0U];
          Lib_IntVector_Intrinsics_vec256 v16 = k[1U];
          Lib_IntVector_Intrinsics_vec256 v20 = k[2U];
          Lib_IntVector_Intrinsics_vec256 v30 = k[3U];
          Lib_IntVector_Intrinsics_vec256 v40 = k[4U];
          Lib_IntVector_Intrinsics_vec256 v50 = k[5U];
          Lib_IntVector_Intrinsics_vec256 v60 = k[6U];
          Lib_IntVector_Intrinsics_vec256 v70 = k[7U];
          Lib_IntVector_Intrinsics_vec256
          v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v16);
          Lib_IntVector_Intrinsics_vec256
          v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v20, v30);
          Lib_IntVector_Intrinsics_vec256
          v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v40, v50);
          Lib_IntVector_Intrinsics_vec256
          v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v60, v70);
          Lib_IntVector_Intrinsics_vec256
          v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_, v2_);
          Lib_IntVector_Intrinsics_vec256
          v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_, v3_);
          Lib_IntVector_Intrinsics_vec256
          v4__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v5__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_, v6_);
          Lib_IntVector_Intrinsics_vec256
          v6__ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v7__ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_, v7_);
          Lib_IntVector_Intrinsics_vec256
          v0___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v1___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__, v4__);
          Lib_IntVector_Intrinsics_vec256
          v2___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v3___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__, v5__);
          Lib_IntVector_Intrinsics_vec256
          v4___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v5___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__, v6__);
          Lib_IntVector_Intrinsics_vec256
          v6___ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256
          v7___ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__, v7__);
          Lib_IntVector_Intrinsics_vec256 v0 = v0___;
          Lib_IntVector_Intrinsics_vec256 v1 = v2___;
          Lib_IntVector_Intrinsics_vec256 v2 = v4___;
          Lib_IntVector_Intrinsics_vec256 v3 = v6___;
          Lib_IntVector_Intrinsics_vec256 v4 = v1___;
          Lib_IntVector_Intrinsics_vec256 v5 = v3___;
          Lib_IntVector_Intrinsics_vec256 v6 = v5___;
          Lib_IntVector_Intrinsics_vec256 v7 = v7___;
          Lib_IntVector_Intrinsics_vec256 v01 = k[8U];
          Lib_IntVector_Intrinsics_vec256 v110 = k[9U];
          Lib_IntVector_Intrinsics_vec256 v21 = k[10U];
          Lib_IntVector_Intrinsics_vec256 v31 = k[11U];
          Lib_IntVector_Intrinsics_vec256 v41 = k[12U];
          Lib_IntVector_Intrinsics_vec256 v51 = k[13U];
          Lib_IntVector_Intrinsics_vec256 v61 = k[14U];
          Lib_IntVector_Intrinsics_vec256 v71 = k[15U];
          Lib_IntVector_Intrinsics_vec256
          v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v01, v110);
          Lib_IntVector_Intrinsics_vec256
          v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v21, v31);
          Lib_IntVector_Intrinsics_vec256
          v4_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v5_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v41, v51);
          Lib_IntVector_Intrinsics_vec256
          v6_0 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v7_0 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v61, v71);
          Lib_IntVector_Intrinsics_vec256
          v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
          Lib_IntVector_Intrinsics_vec256
          v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
          Lib_IntVector_Intrinsics_vec256
          v4__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v5__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
          Lib_IntVector_Intrinsics_vec256
          v6__0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v7__0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
          Lib_IntVector_Intrinsics_vec256
          v0___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v1___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0__0, v4__0);
          Lib_IntVector_Intrinsics_vec256
          v2___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v3___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1__0, v5__0);
          Lib_IntVector_Intrinsics_vec256
          v4___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v5___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2__0, v6__0);
          Lib_IntVector_Intrinsics_vec256
          v6___0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256
          v7___0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3__0, v7__0);
          Lib_IntVector_Intrinsics_vec256 v8 = v0___0;
          Lib_IntVector_Intrinsics_vec256 v9 = v2___0;
          Lib_IntVector_Intrinsics_vec256 v10 = v4___0;
          Lib_IntVector_Intrinsics_vec256 v11 = v6___0;
          Lib_IntVector_Intrinsics_vec256 v12 = v1___0;
          Lib_IntVector_Intrinsics_vec256 v13 = v3___0;
          Lib_IntVector_Intrinsics_vec256 v14 = v5___0;
          Lib_IntVector_Intrinsics_vec256 v15 = v7___0;
          k[0U] = v0;
          k[1U] = v8;
          k[2U] = v1;
          k[3U] = v9;
          k[4U] = v2;
          k[5U] = v10;
          k[6U] = v3;
          k[7U] = v11;
          k[8U] = v4;
          k[9U] = v12;
          k[10U] = v5;
          k[11U] = v13;
          k[12U] = v6;
          k[13U] = v14;
          k[14U] = v7;
          k[15U] = v15;
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              Lib_IntVector_Intrinsics_vec256
              x = Lib_IntVector_Intrinsics_vec256_load_le(plain + i * (u32)32U);
              Lib_IntVector_Intrinsics_vec256 y = Lib_IntVector_Intrinsics_vec256_xor(x, k[i]);
              Lib_IntVector_Intrinsics_vec256_store_le(plain + i * (u32)32U, y);
            }
          }
          memcpy(uu____2, plain, rem * sizeof (u8));
        }
      }
    }
  }
}

