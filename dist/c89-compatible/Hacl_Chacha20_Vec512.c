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


#include "Hacl_Chacha20_Vec512.h"

static inline void double_round_512(Lib_IntVector_Intrinsics_vec512 *st)
{
  Lib_IntVector_Intrinsics_vec512 std0;
  Lib_IntVector_Intrinsics_vec512 std1;
  Lib_IntVector_Intrinsics_vec512 std2;
  Lib_IntVector_Intrinsics_vec512 std3;
  Lib_IntVector_Intrinsics_vec512 std4;
  Lib_IntVector_Intrinsics_vec512 std5;
  Lib_IntVector_Intrinsics_vec512 std6;
  Lib_IntVector_Intrinsics_vec512 std7;
  Lib_IntVector_Intrinsics_vec512 std8;
  Lib_IntVector_Intrinsics_vec512 std9;
  Lib_IntVector_Intrinsics_vec512 std10;
  Lib_IntVector_Intrinsics_vec512 std11;
  Lib_IntVector_Intrinsics_vec512 std12;
  Lib_IntVector_Intrinsics_vec512 std13;
  Lib_IntVector_Intrinsics_vec512 std14;
  Lib_IntVector_Intrinsics_vec512 std15;
  Lib_IntVector_Intrinsics_vec512 std16;
  Lib_IntVector_Intrinsics_vec512 std17;
  Lib_IntVector_Intrinsics_vec512 std18;
  Lib_IntVector_Intrinsics_vec512 std19;
  Lib_IntVector_Intrinsics_vec512 std20;
  Lib_IntVector_Intrinsics_vec512 std21;
  Lib_IntVector_Intrinsics_vec512 std22;
  Lib_IntVector_Intrinsics_vec512 std23;
  Lib_IntVector_Intrinsics_vec512 std24;
  Lib_IntVector_Intrinsics_vec512 std25;
  Lib_IntVector_Intrinsics_vec512 std26;
  Lib_IntVector_Intrinsics_vec512 std27;
  Lib_IntVector_Intrinsics_vec512 std28;
  Lib_IntVector_Intrinsics_vec512 std29;
  Lib_IntVector_Intrinsics_vec512 std30;
  Lib_IntVector_Intrinsics_vec512 std;
  st[0U] = Lib_IntVector_Intrinsics_vec512_add32(st[0U], st[4U]);
  std0 = Lib_IntVector_Intrinsics_vec512_xor(st[12U], st[0U]);
  st[12U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std0, (uint32_t)16U);
  st[8U] = Lib_IntVector_Intrinsics_vec512_add32(st[8U], st[12U]);
  std1 = Lib_IntVector_Intrinsics_vec512_xor(st[4U], st[8U]);
  st[4U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std1, (uint32_t)12U);
  st[0U] = Lib_IntVector_Intrinsics_vec512_add32(st[0U], st[4U]);
  std2 = Lib_IntVector_Intrinsics_vec512_xor(st[12U], st[0U]);
  st[12U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std2, (uint32_t)8U);
  st[8U] = Lib_IntVector_Intrinsics_vec512_add32(st[8U], st[12U]);
  std3 = Lib_IntVector_Intrinsics_vec512_xor(st[4U], st[8U]);
  st[4U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std3, (uint32_t)7U);
  st[1U] = Lib_IntVector_Intrinsics_vec512_add32(st[1U], st[5U]);
  std4 = Lib_IntVector_Intrinsics_vec512_xor(st[13U], st[1U]);
  st[13U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std4, (uint32_t)16U);
  st[9U] = Lib_IntVector_Intrinsics_vec512_add32(st[9U], st[13U]);
  std5 = Lib_IntVector_Intrinsics_vec512_xor(st[5U], st[9U]);
  st[5U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std5, (uint32_t)12U);
  st[1U] = Lib_IntVector_Intrinsics_vec512_add32(st[1U], st[5U]);
  std6 = Lib_IntVector_Intrinsics_vec512_xor(st[13U], st[1U]);
  st[13U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std6, (uint32_t)8U);
  st[9U] = Lib_IntVector_Intrinsics_vec512_add32(st[9U], st[13U]);
  std7 = Lib_IntVector_Intrinsics_vec512_xor(st[5U], st[9U]);
  st[5U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std7, (uint32_t)7U);
  st[2U] = Lib_IntVector_Intrinsics_vec512_add32(st[2U], st[6U]);
  std8 = Lib_IntVector_Intrinsics_vec512_xor(st[14U], st[2U]);
  st[14U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std8, (uint32_t)16U);
  st[10U] = Lib_IntVector_Intrinsics_vec512_add32(st[10U], st[14U]);
  std9 = Lib_IntVector_Intrinsics_vec512_xor(st[6U], st[10U]);
  st[6U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std9, (uint32_t)12U);
  st[2U] = Lib_IntVector_Intrinsics_vec512_add32(st[2U], st[6U]);
  std10 = Lib_IntVector_Intrinsics_vec512_xor(st[14U], st[2U]);
  st[14U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std10, (uint32_t)8U);
  st[10U] = Lib_IntVector_Intrinsics_vec512_add32(st[10U], st[14U]);
  std11 = Lib_IntVector_Intrinsics_vec512_xor(st[6U], st[10U]);
  st[6U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std11, (uint32_t)7U);
  st[3U] = Lib_IntVector_Intrinsics_vec512_add32(st[3U], st[7U]);
  std12 = Lib_IntVector_Intrinsics_vec512_xor(st[15U], st[3U]);
  st[15U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std12, (uint32_t)16U);
  st[11U] = Lib_IntVector_Intrinsics_vec512_add32(st[11U], st[15U]);
  std13 = Lib_IntVector_Intrinsics_vec512_xor(st[7U], st[11U]);
  st[7U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std13, (uint32_t)12U);
  st[3U] = Lib_IntVector_Intrinsics_vec512_add32(st[3U], st[7U]);
  std14 = Lib_IntVector_Intrinsics_vec512_xor(st[15U], st[3U]);
  st[15U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std14, (uint32_t)8U);
  st[11U] = Lib_IntVector_Intrinsics_vec512_add32(st[11U], st[15U]);
  std15 = Lib_IntVector_Intrinsics_vec512_xor(st[7U], st[11U]);
  st[7U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std15, (uint32_t)7U);
  st[0U] = Lib_IntVector_Intrinsics_vec512_add32(st[0U], st[5U]);
  std16 = Lib_IntVector_Intrinsics_vec512_xor(st[15U], st[0U]);
  st[15U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std16, (uint32_t)16U);
  st[10U] = Lib_IntVector_Intrinsics_vec512_add32(st[10U], st[15U]);
  std17 = Lib_IntVector_Intrinsics_vec512_xor(st[5U], st[10U]);
  st[5U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std17, (uint32_t)12U);
  st[0U] = Lib_IntVector_Intrinsics_vec512_add32(st[0U], st[5U]);
  std18 = Lib_IntVector_Intrinsics_vec512_xor(st[15U], st[0U]);
  st[15U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std18, (uint32_t)8U);
  st[10U] = Lib_IntVector_Intrinsics_vec512_add32(st[10U], st[15U]);
  std19 = Lib_IntVector_Intrinsics_vec512_xor(st[5U], st[10U]);
  st[5U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std19, (uint32_t)7U);
  st[1U] = Lib_IntVector_Intrinsics_vec512_add32(st[1U], st[6U]);
  std20 = Lib_IntVector_Intrinsics_vec512_xor(st[12U], st[1U]);
  st[12U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std20, (uint32_t)16U);
  st[11U] = Lib_IntVector_Intrinsics_vec512_add32(st[11U], st[12U]);
  std21 = Lib_IntVector_Intrinsics_vec512_xor(st[6U], st[11U]);
  st[6U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std21, (uint32_t)12U);
  st[1U] = Lib_IntVector_Intrinsics_vec512_add32(st[1U], st[6U]);
  std22 = Lib_IntVector_Intrinsics_vec512_xor(st[12U], st[1U]);
  st[12U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std22, (uint32_t)8U);
  st[11U] = Lib_IntVector_Intrinsics_vec512_add32(st[11U], st[12U]);
  std23 = Lib_IntVector_Intrinsics_vec512_xor(st[6U], st[11U]);
  st[6U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std23, (uint32_t)7U);
  st[2U] = Lib_IntVector_Intrinsics_vec512_add32(st[2U], st[7U]);
  std24 = Lib_IntVector_Intrinsics_vec512_xor(st[13U], st[2U]);
  st[13U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std24, (uint32_t)16U);
  st[8U] = Lib_IntVector_Intrinsics_vec512_add32(st[8U], st[13U]);
  std25 = Lib_IntVector_Intrinsics_vec512_xor(st[7U], st[8U]);
  st[7U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std25, (uint32_t)12U);
  st[2U] = Lib_IntVector_Intrinsics_vec512_add32(st[2U], st[7U]);
  std26 = Lib_IntVector_Intrinsics_vec512_xor(st[13U], st[2U]);
  st[13U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std26, (uint32_t)8U);
  st[8U] = Lib_IntVector_Intrinsics_vec512_add32(st[8U], st[13U]);
  std27 = Lib_IntVector_Intrinsics_vec512_xor(st[7U], st[8U]);
  st[7U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std27, (uint32_t)7U);
  st[3U] = Lib_IntVector_Intrinsics_vec512_add32(st[3U], st[4U]);
  std28 = Lib_IntVector_Intrinsics_vec512_xor(st[14U], st[3U]);
  st[14U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std28, (uint32_t)16U);
  st[9U] = Lib_IntVector_Intrinsics_vec512_add32(st[9U], st[14U]);
  std29 = Lib_IntVector_Intrinsics_vec512_xor(st[4U], st[9U]);
  st[4U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std29, (uint32_t)12U);
  st[3U] = Lib_IntVector_Intrinsics_vec512_add32(st[3U], st[4U]);
  std30 = Lib_IntVector_Intrinsics_vec512_xor(st[14U], st[3U]);
  st[14U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std30, (uint32_t)8U);
  st[9U] = Lib_IntVector_Intrinsics_vec512_add32(st[9U], st[14U]);
  std = Lib_IntVector_Intrinsics_vec512_xor(st[4U], st[9U]);
  st[4U] = Lib_IntVector_Intrinsics_vec512_rotate_left32(std, (uint32_t)7U);
}

static inline void
chacha20_core_512(
  Lib_IntVector_Intrinsics_vec512 *k,
  Lib_IntVector_Intrinsics_vec512 *ctx,
  uint32_t ctr
)
{
  uint32_t ctr_u32;
  Lib_IntVector_Intrinsics_vec512 cv;
  memcpy(k, ctx, (uint32_t)16U * sizeof (ctx[0U]));
  ctr_u32 = (uint32_t)16U * ctr;
  cv = Lib_IntVector_Intrinsics_vec512_load32(ctr_u32);
  k[12U] = Lib_IntVector_Intrinsics_vec512_add32(k[12U], cv);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  double_round_512(k);
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      Lib_IntVector_Intrinsics_vec512 *os = k;
      Lib_IntVector_Intrinsics_vec512 x = Lib_IntVector_Intrinsics_vec512_add32(k[i], ctx[i]);
      os[i] = x;
    }
  }
  k[12U] = Lib_IntVector_Intrinsics_vec512_add32(k[12U], cv);
}

static inline void
chacha20_init_512(Lib_IntVector_Intrinsics_vec512 *ctx, uint8_t *k, uint8_t *n, uint32_t ctr)
{
  uint32_t ctx1[16U] = { 0U };
  uint32_t *uu____0 = ctx1;
  uint32_t *uu____1;
  uint32_t *uu____2;
  Lib_IntVector_Intrinsics_vec512 ctr1;
  Lib_IntVector_Intrinsics_vec512 c12;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = uu____0;
      uint32_t x = Hacl_Impl_Chacha20_Vec_chacha20_constants[i];
      os[i] = x;
    }
  }
  uu____1 = ctx1 + (uint32_t)4U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
    {
      uint32_t *os = uu____1;
      uint8_t *bj = k + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
  }
  ctx1[12U] = ctr;
  uu____2 = ctx1 + (uint32_t)13U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)3U; i++)
    {
      uint32_t *os = uu____2;
      uint8_t *bj = n + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
  }
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      Lib_IntVector_Intrinsics_vec512 *os = ctx;
      uint32_t x = ctx1[i];
      Lib_IntVector_Intrinsics_vec512 x0 = Lib_IntVector_Intrinsics_vec512_load32(x);
      os[i] = x0;
    }
  }
  ctr1 =
    Lib_IntVector_Intrinsics_vec512_load32s((uint32_t)0U,
      (uint32_t)1U,
      (uint32_t)2U,
      (uint32_t)3U,
      (uint32_t)4U,
      (uint32_t)5U,
      (uint32_t)6U,
      (uint32_t)7U,
      (uint32_t)8U,
      (uint32_t)9U,
      (uint32_t)10U,
      (uint32_t)11U,
      (uint32_t)12U,
      (uint32_t)13U,
      (uint32_t)14U,
      (uint32_t)15U);
  c12 = ctx[12U];
  ctx[12U] = Lib_IntVector_Intrinsics_vec512_add32(c12, ctr1);
}

void
Hacl_Chacha20_Vec512_chacha20_encrypt_512(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
  {
    Lib_IntVector_Intrinsics_vec512 ctx[16U];
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)16U; ++_i)
        ctx[_i] = Lib_IntVector_Intrinsics_vec512_zero;
    }
    {
      uint32_t rem;
      uint32_t nb;
      uint32_t rem1;
      chacha20_init_512(ctx, key, n, ctr);
      rem = len % (uint32_t)1024U;
      nb = len / (uint32_t)1024U;
      rem1 = len % (uint32_t)1024U;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < nb; i++)
        {
          uint8_t *uu____0 = out + i * (uint32_t)1024U;
          uint8_t *uu____1 = text + i * (uint32_t)1024U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
          {
            Lib_IntVector_Intrinsics_vec512 k[16U];
            {
              uint32_t _i;
              for (_i = 0U; _i < (uint32_t)16U; ++_i)
                k[_i] = Lib_IntVector_Intrinsics_vec512_zero;
            }
            chacha20_core_512(k, ctx, i);
            {
              Lib_IntVector_Intrinsics_vec512 v0 = k[0U];
              Lib_IntVector_Intrinsics_vec512 v1 = k[1U];
              Lib_IntVector_Intrinsics_vec512 v2 = k[2U];
              Lib_IntVector_Intrinsics_vec512 v3 = k[3U];
              Lib_IntVector_Intrinsics_vec512 v4 = k[4U];
              Lib_IntVector_Intrinsics_vec512 v5 = k[5U];
              Lib_IntVector_Intrinsics_vec512 v6 = k[6U];
              Lib_IntVector_Intrinsics_vec512 v7 = k[7U];
              Lib_IntVector_Intrinsics_vec512 v8 = k[8U];
              Lib_IntVector_Intrinsics_vec512 v9 = k[9U];
              Lib_IntVector_Intrinsics_vec512 v10 = k[10U];
              Lib_IntVector_Intrinsics_vec512 v11 = k[11U];
              Lib_IntVector_Intrinsics_vec512 v12 = k[12U];
              Lib_IntVector_Intrinsics_vec512 v13 = k[13U];
              Lib_IntVector_Intrinsics_vec512 v14 = k[14U];
              Lib_IntVector_Intrinsics_vec512 v15 = k[15U];
              Lib_IntVector_Intrinsics_vec512 v01 = v0;
              Lib_IntVector_Intrinsics_vec512 v16 = v1;
              Lib_IntVector_Intrinsics_vec512 v21 = v2;
              Lib_IntVector_Intrinsics_vec512 v31 = v3;
              Lib_IntVector_Intrinsics_vec512 v41 = v4;
              Lib_IntVector_Intrinsics_vec512 v51 = v5;
              Lib_IntVector_Intrinsics_vec512 v61 = v6;
              Lib_IntVector_Intrinsics_vec512 v71 = v7;
              Lib_IntVector_Intrinsics_vec512 v81 = v8;
              Lib_IntVector_Intrinsics_vec512 v91 = v9;
              Lib_IntVector_Intrinsics_vec512 v101 = v10;
              Lib_IntVector_Intrinsics_vec512 v111 = v11;
              Lib_IntVector_Intrinsics_vec512 v121 = v12;
              Lib_IntVector_Intrinsics_vec512 v131 = v13;
              Lib_IntVector_Intrinsics_vec512 v141 = v14;
              Lib_IntVector_Intrinsics_vec512 v151 = v15;
              Lib_IntVector_Intrinsics_vec512 v020 = v01;
              Lib_IntVector_Intrinsics_vec512 v170 = v16;
              Lib_IntVector_Intrinsics_vec512 v220 = v21;
              Lib_IntVector_Intrinsics_vec512 v320 = v31;
              Lib_IntVector_Intrinsics_vec512 v420 = v41;
              Lib_IntVector_Intrinsics_vec512 v520 = v51;
              Lib_IntVector_Intrinsics_vec512 v620 = v61;
              Lib_IntVector_Intrinsics_vec512 v720 = v71;
              Lib_IntVector_Intrinsics_vec512 v820 = v81;
              Lib_IntVector_Intrinsics_vec512 v920 = v91;
              Lib_IntVector_Intrinsics_vec512 v1020 = v101;
              Lib_IntVector_Intrinsics_vec512 v1120 = v111;
              Lib_IntVector_Intrinsics_vec512 v1220 = v121;
              Lib_IntVector_Intrinsics_vec512 v1320 = v131;
              Lib_IntVector_Intrinsics_vec512 v1420 = v141;
              Lib_IntVector_Intrinsics_vec512 v1520 = v151;
              Lib_IntVector_Intrinsics_vec512
              v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v020, v170);
              Lib_IntVector_Intrinsics_vec512
              v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v020, v170);
              Lib_IntVector_Intrinsics_vec512
              v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v220, v320);
              Lib_IntVector_Intrinsics_vec512
              v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v220, v320);
              Lib_IntVector_Intrinsics_vec512
              v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v420, v520);
              Lib_IntVector_Intrinsics_vec512
              v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v420, v520);
              Lib_IntVector_Intrinsics_vec512
              v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v620, v720);
              Lib_IntVector_Intrinsics_vec512
              v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v620, v720);
              Lib_IntVector_Intrinsics_vec512
              v8_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v820, v920);
              Lib_IntVector_Intrinsics_vec512
              v9_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v820, v920);
              Lib_IntVector_Intrinsics_vec512
              v10_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1020, v1120);
              Lib_IntVector_Intrinsics_vec512
              v11_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1020, v1120);
              Lib_IntVector_Intrinsics_vec512
              v12_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1220, v1320);
              Lib_IntVector_Intrinsics_vec512
              v13_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1220, v1320);
              Lib_IntVector_Intrinsics_vec512
              v14_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1420, v1520);
              Lib_IntVector_Intrinsics_vec512
              v15_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1420, v1520);
              Lib_IntVector_Intrinsics_vec512 v0_0 = v0_;
              Lib_IntVector_Intrinsics_vec512 v1_0 = v1_;
              Lib_IntVector_Intrinsics_vec512 v2_0 = v2_;
              Lib_IntVector_Intrinsics_vec512 v3_0 = v3_;
              Lib_IntVector_Intrinsics_vec512 v4_0 = v4_;
              Lib_IntVector_Intrinsics_vec512 v5_0 = v5_;
              Lib_IntVector_Intrinsics_vec512 v6_0 = v6_;
              Lib_IntVector_Intrinsics_vec512 v7_0 = v7_;
              Lib_IntVector_Intrinsics_vec512 v8_0 = v8_;
              Lib_IntVector_Intrinsics_vec512 v9_0 = v9_;
              Lib_IntVector_Intrinsics_vec512 v10_0 = v10_;
              Lib_IntVector_Intrinsics_vec512 v11_0 = v11_;
              Lib_IntVector_Intrinsics_vec512 v12_0 = v12_;
              Lib_IntVector_Intrinsics_vec512 v13_0 = v13_;
              Lib_IntVector_Intrinsics_vec512 v14_0 = v14_;
              Lib_IntVector_Intrinsics_vec512 v15_0 = v15_;
              Lib_IntVector_Intrinsics_vec512 v021 = v0_0;
              Lib_IntVector_Intrinsics_vec512 v171 = v1_0;
              Lib_IntVector_Intrinsics_vec512 v221 = v2_0;
              Lib_IntVector_Intrinsics_vec512 v321 = v3_0;
              Lib_IntVector_Intrinsics_vec512 v421 = v4_0;
              Lib_IntVector_Intrinsics_vec512 v521 = v5_0;
              Lib_IntVector_Intrinsics_vec512 v621 = v6_0;
              Lib_IntVector_Intrinsics_vec512 v721 = v7_0;
              Lib_IntVector_Intrinsics_vec512 v821 = v8_0;
              Lib_IntVector_Intrinsics_vec512 v921 = v9_0;
              Lib_IntVector_Intrinsics_vec512 v1021 = v10_0;
              Lib_IntVector_Intrinsics_vec512 v1121 = v11_0;
              Lib_IntVector_Intrinsics_vec512 v1221 = v12_0;
              Lib_IntVector_Intrinsics_vec512 v1321 = v13_0;
              Lib_IntVector_Intrinsics_vec512 v1421 = v14_0;
              Lib_IntVector_Intrinsics_vec512 v1521 = v15_0;
              Lib_IntVector_Intrinsics_vec512
              v0_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v021, v221);
              Lib_IntVector_Intrinsics_vec512
              v2_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v021, v221);
              Lib_IntVector_Intrinsics_vec512
              v1_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v171, v321);
              Lib_IntVector_Intrinsics_vec512
              v3_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v171, v321);
              Lib_IntVector_Intrinsics_vec512
              v4_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v421, v621);
              Lib_IntVector_Intrinsics_vec512
              v6_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v421, v621);
              Lib_IntVector_Intrinsics_vec512
              v5_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v521, v721);
              Lib_IntVector_Intrinsics_vec512
              v7_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v521, v721);
              Lib_IntVector_Intrinsics_vec512
              v8_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v821, v1021);
              Lib_IntVector_Intrinsics_vec512
              v10_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v821, v1021);
              Lib_IntVector_Intrinsics_vec512
              v9_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v921, v1121);
              Lib_IntVector_Intrinsics_vec512
              v11_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v921, v1121);
              Lib_IntVector_Intrinsics_vec512
              v12_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1221, v1421);
              Lib_IntVector_Intrinsics_vec512
              v14_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1221, v1421);
              Lib_IntVector_Intrinsics_vec512
              v13_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1321, v1521);
              Lib_IntVector_Intrinsics_vec512
              v15_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1321, v1521);
              Lib_IntVector_Intrinsics_vec512 v0_10 = v0_1;
              Lib_IntVector_Intrinsics_vec512 v1_10 = v1_1;
              Lib_IntVector_Intrinsics_vec512 v2_10 = v2_1;
              Lib_IntVector_Intrinsics_vec512 v3_10 = v3_1;
              Lib_IntVector_Intrinsics_vec512 v4_10 = v4_1;
              Lib_IntVector_Intrinsics_vec512 v5_10 = v5_1;
              Lib_IntVector_Intrinsics_vec512 v6_10 = v6_1;
              Lib_IntVector_Intrinsics_vec512 v7_10 = v7_1;
              Lib_IntVector_Intrinsics_vec512 v8_10 = v8_1;
              Lib_IntVector_Intrinsics_vec512 v9_10 = v9_1;
              Lib_IntVector_Intrinsics_vec512 v10_10 = v10_1;
              Lib_IntVector_Intrinsics_vec512 v11_10 = v11_1;
              Lib_IntVector_Intrinsics_vec512 v12_10 = v12_1;
              Lib_IntVector_Intrinsics_vec512 v13_10 = v13_1;
              Lib_IntVector_Intrinsics_vec512 v14_10 = v14_1;
              Lib_IntVector_Intrinsics_vec512 v15_10 = v15_1;
              Lib_IntVector_Intrinsics_vec512 v022 = v0_10;
              Lib_IntVector_Intrinsics_vec512 v172 = v1_10;
              Lib_IntVector_Intrinsics_vec512 v222 = v2_10;
              Lib_IntVector_Intrinsics_vec512 v322 = v3_10;
              Lib_IntVector_Intrinsics_vec512 v422 = v4_10;
              Lib_IntVector_Intrinsics_vec512 v522 = v5_10;
              Lib_IntVector_Intrinsics_vec512 v622 = v6_10;
              Lib_IntVector_Intrinsics_vec512 v722 = v7_10;
              Lib_IntVector_Intrinsics_vec512 v822 = v8_10;
              Lib_IntVector_Intrinsics_vec512 v922 = v9_10;
              Lib_IntVector_Intrinsics_vec512 v1022 = v10_10;
              Lib_IntVector_Intrinsics_vec512 v1122 = v11_10;
              Lib_IntVector_Intrinsics_vec512 v1222 = v12_10;
              Lib_IntVector_Intrinsics_vec512 v1322 = v13_10;
              Lib_IntVector_Intrinsics_vec512 v1422 = v14_10;
              Lib_IntVector_Intrinsics_vec512 v1522 = v15_10;
              Lib_IntVector_Intrinsics_vec512
              v0_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v022, v422);
              Lib_IntVector_Intrinsics_vec512
              v4_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v022, v422);
              Lib_IntVector_Intrinsics_vec512
              v1_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v172, v522);
              Lib_IntVector_Intrinsics_vec512
              v5_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v172, v522);
              Lib_IntVector_Intrinsics_vec512
              v2_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v222, v622);
              Lib_IntVector_Intrinsics_vec512
              v6_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v222, v622);
              Lib_IntVector_Intrinsics_vec512
              v3_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v322, v722);
              Lib_IntVector_Intrinsics_vec512
              v7_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v322, v722);
              Lib_IntVector_Intrinsics_vec512
              v8_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v822, v1222);
              Lib_IntVector_Intrinsics_vec512
              v12_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v822, v1222);
              Lib_IntVector_Intrinsics_vec512
              v9_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v922, v1322);
              Lib_IntVector_Intrinsics_vec512
              v13_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v922, v1322);
              Lib_IntVector_Intrinsics_vec512
              v10_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1022, v1422);
              Lib_IntVector_Intrinsics_vec512
              v14_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1022, v1422);
              Lib_IntVector_Intrinsics_vec512
              v11_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1122, v1522);
              Lib_IntVector_Intrinsics_vec512
              v15_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1122, v1522);
              Lib_IntVector_Intrinsics_vec512 v0_20 = v0_2;
              Lib_IntVector_Intrinsics_vec512 v1_20 = v1_2;
              Lib_IntVector_Intrinsics_vec512 v2_20 = v2_2;
              Lib_IntVector_Intrinsics_vec512 v3_20 = v3_2;
              Lib_IntVector_Intrinsics_vec512 v4_20 = v4_2;
              Lib_IntVector_Intrinsics_vec512 v5_20 = v5_2;
              Lib_IntVector_Intrinsics_vec512 v6_20 = v6_2;
              Lib_IntVector_Intrinsics_vec512 v7_20 = v7_2;
              Lib_IntVector_Intrinsics_vec512 v8_20 = v8_2;
              Lib_IntVector_Intrinsics_vec512 v9_20 = v9_2;
              Lib_IntVector_Intrinsics_vec512 v10_20 = v10_2;
              Lib_IntVector_Intrinsics_vec512 v11_20 = v11_2;
              Lib_IntVector_Intrinsics_vec512 v12_20 = v12_2;
              Lib_IntVector_Intrinsics_vec512 v13_20 = v13_2;
              Lib_IntVector_Intrinsics_vec512 v14_20 = v14_2;
              Lib_IntVector_Intrinsics_vec512 v15_20 = v15_2;
              Lib_IntVector_Intrinsics_vec512 v02 = v0_20;
              Lib_IntVector_Intrinsics_vec512 v17 = v1_20;
              Lib_IntVector_Intrinsics_vec512 v22 = v2_20;
              Lib_IntVector_Intrinsics_vec512 v32 = v3_20;
              Lib_IntVector_Intrinsics_vec512 v42 = v4_20;
              Lib_IntVector_Intrinsics_vec512 v52 = v5_20;
              Lib_IntVector_Intrinsics_vec512 v62 = v6_20;
              Lib_IntVector_Intrinsics_vec512 v72 = v7_20;
              Lib_IntVector_Intrinsics_vec512 v82 = v8_20;
              Lib_IntVector_Intrinsics_vec512 v92 = v9_20;
              Lib_IntVector_Intrinsics_vec512 v102 = v10_20;
              Lib_IntVector_Intrinsics_vec512 v112 = v11_20;
              Lib_IntVector_Intrinsics_vec512 v122 = v12_20;
              Lib_IntVector_Intrinsics_vec512 v132 = v13_20;
              Lib_IntVector_Intrinsics_vec512 v142 = v14_20;
              Lib_IntVector_Intrinsics_vec512 v152 = v15_20;
              Lib_IntVector_Intrinsics_vec512
              v0_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v02, v82);
              Lib_IntVector_Intrinsics_vec512
              v8_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v02, v82);
              Lib_IntVector_Intrinsics_vec512
              v1_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v17, v92);
              Lib_IntVector_Intrinsics_vec512
              v9_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v17, v92);
              Lib_IntVector_Intrinsics_vec512
              v2_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v22, v102);
              Lib_IntVector_Intrinsics_vec512
              v10_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v22, v102);
              Lib_IntVector_Intrinsics_vec512
              v3_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v32, v112);
              Lib_IntVector_Intrinsics_vec512
              v11_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v32, v112);
              Lib_IntVector_Intrinsics_vec512
              v4_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v42, v122);
              Lib_IntVector_Intrinsics_vec512
              v12_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v42, v122);
              Lib_IntVector_Intrinsics_vec512
              v5_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v52, v132);
              Lib_IntVector_Intrinsics_vec512
              v13_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v52, v132);
              Lib_IntVector_Intrinsics_vec512
              v6_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v62, v142);
              Lib_IntVector_Intrinsics_vec512
              v14_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v62, v142);
              Lib_IntVector_Intrinsics_vec512
              v7_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v72, v152);
              Lib_IntVector_Intrinsics_vec512
              v15_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v72, v152);
              Lib_IntVector_Intrinsics_vec512 v0_30 = v0_3;
              Lib_IntVector_Intrinsics_vec512 v1_30 = v1_3;
              Lib_IntVector_Intrinsics_vec512 v2_30 = v2_3;
              Lib_IntVector_Intrinsics_vec512 v3_30 = v3_3;
              Lib_IntVector_Intrinsics_vec512 v4_30 = v4_3;
              Lib_IntVector_Intrinsics_vec512 v5_30 = v5_3;
              Lib_IntVector_Intrinsics_vec512 v6_30 = v6_3;
              Lib_IntVector_Intrinsics_vec512 v7_30 = v7_3;
              Lib_IntVector_Intrinsics_vec512 v8_30 = v8_3;
              Lib_IntVector_Intrinsics_vec512 v9_30 = v9_3;
              Lib_IntVector_Intrinsics_vec512 v10_30 = v10_3;
              Lib_IntVector_Intrinsics_vec512 v11_30 = v11_3;
              Lib_IntVector_Intrinsics_vec512 v12_30 = v12_3;
              Lib_IntVector_Intrinsics_vec512 v13_30 = v13_3;
              Lib_IntVector_Intrinsics_vec512 v14_30 = v14_3;
              Lib_IntVector_Intrinsics_vec512 v15_30 = v15_3;
              Lib_IntVector_Intrinsics_vec512 r0 = v0_30;
              Lib_IntVector_Intrinsics_vec512 r1 = v2_30;
              Lib_IntVector_Intrinsics_vec512 r2 = v1_30;
              Lib_IntVector_Intrinsics_vec512 r3 = v3_30;
              Lib_IntVector_Intrinsics_vec512 r4 = v4_30;
              Lib_IntVector_Intrinsics_vec512 r5 = v6_30;
              Lib_IntVector_Intrinsics_vec512 r6 = v5_30;
              Lib_IntVector_Intrinsics_vec512 r7 = v7_30;
              Lib_IntVector_Intrinsics_vec512 r8 = v8_30;
              Lib_IntVector_Intrinsics_vec512 r9 = v10_30;
              Lib_IntVector_Intrinsics_vec512 r10 = v9_30;
              Lib_IntVector_Intrinsics_vec512 r11 = v11_30;
              Lib_IntVector_Intrinsics_vec512 r12 = v12_30;
              Lib_IntVector_Intrinsics_vec512 r13 = v14_30;
              Lib_IntVector_Intrinsics_vec512 r14 = v13_30;
              Lib_IntVector_Intrinsics_vec512 r15 = v15_30;
              k[0U] = r0;
              k[1U] = r1;
              k[2U] = r2;
              k[3U] = r3;
              k[4U] = r4;
              k[5U] = r5;
              k[6U] = r6;
              k[7U] = r7;
              k[8U] = r8;
              k[9U] = r9;
              k[10U] = r10;
              k[11U] = r11;
              k[12U] = r12;
              k[13U] = r13;
              k[14U] = r14;
              k[15U] = r15;
              {
                uint32_t i0;
                for (i0 = (uint32_t)0U; i0 < (uint32_t)16U; i0++)
                {
                  Lib_IntVector_Intrinsics_vec512
                  x = Lib_IntVector_Intrinsics_vec512_load_le(uu____1 + i0 * (uint32_t)64U);
                  Lib_IntVector_Intrinsics_vec512 y = Lib_IntVector_Intrinsics_vec512_xor(x, k[i0]);
                  Lib_IntVector_Intrinsics_vec512_store_le(uu____0 + i0 * (uint32_t)64U, y);
                }
              }
            }
          }
        }
      }
      if (rem1 > (uint32_t)0U)
      {
        uint8_t *uu____2 = out + nb * (uint32_t)1024U;
        uint8_t *uu____3 = text + nb * (uint32_t)1024U;
        uint8_t plain[1024U] = { 0U };
        memcpy(plain, uu____3, rem * sizeof (uu____3[0U]));
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
        {
          Lib_IntVector_Intrinsics_vec512 k[16U];
          {
            uint32_t _i;
            for (_i = 0U; _i < (uint32_t)16U; ++_i)
              k[_i] = Lib_IntVector_Intrinsics_vec512_zero;
          }
          chacha20_core_512(k, ctx, nb);
          {
            Lib_IntVector_Intrinsics_vec512 v0 = k[0U];
            Lib_IntVector_Intrinsics_vec512 v1 = k[1U];
            Lib_IntVector_Intrinsics_vec512 v2 = k[2U];
            Lib_IntVector_Intrinsics_vec512 v3 = k[3U];
            Lib_IntVector_Intrinsics_vec512 v4 = k[4U];
            Lib_IntVector_Intrinsics_vec512 v5 = k[5U];
            Lib_IntVector_Intrinsics_vec512 v6 = k[6U];
            Lib_IntVector_Intrinsics_vec512 v7 = k[7U];
            Lib_IntVector_Intrinsics_vec512 v8 = k[8U];
            Lib_IntVector_Intrinsics_vec512 v9 = k[9U];
            Lib_IntVector_Intrinsics_vec512 v10 = k[10U];
            Lib_IntVector_Intrinsics_vec512 v11 = k[11U];
            Lib_IntVector_Intrinsics_vec512 v12 = k[12U];
            Lib_IntVector_Intrinsics_vec512 v13 = k[13U];
            Lib_IntVector_Intrinsics_vec512 v14 = k[14U];
            Lib_IntVector_Intrinsics_vec512 v15 = k[15U];
            Lib_IntVector_Intrinsics_vec512 v01 = v0;
            Lib_IntVector_Intrinsics_vec512 v16 = v1;
            Lib_IntVector_Intrinsics_vec512 v21 = v2;
            Lib_IntVector_Intrinsics_vec512 v31 = v3;
            Lib_IntVector_Intrinsics_vec512 v41 = v4;
            Lib_IntVector_Intrinsics_vec512 v51 = v5;
            Lib_IntVector_Intrinsics_vec512 v61 = v6;
            Lib_IntVector_Intrinsics_vec512 v71 = v7;
            Lib_IntVector_Intrinsics_vec512 v81 = v8;
            Lib_IntVector_Intrinsics_vec512 v91 = v9;
            Lib_IntVector_Intrinsics_vec512 v101 = v10;
            Lib_IntVector_Intrinsics_vec512 v111 = v11;
            Lib_IntVector_Intrinsics_vec512 v121 = v12;
            Lib_IntVector_Intrinsics_vec512 v131 = v13;
            Lib_IntVector_Intrinsics_vec512 v141 = v14;
            Lib_IntVector_Intrinsics_vec512 v151 = v15;
            Lib_IntVector_Intrinsics_vec512 v020 = v01;
            Lib_IntVector_Intrinsics_vec512 v170 = v16;
            Lib_IntVector_Intrinsics_vec512 v220 = v21;
            Lib_IntVector_Intrinsics_vec512 v320 = v31;
            Lib_IntVector_Intrinsics_vec512 v420 = v41;
            Lib_IntVector_Intrinsics_vec512 v520 = v51;
            Lib_IntVector_Intrinsics_vec512 v620 = v61;
            Lib_IntVector_Intrinsics_vec512 v720 = v71;
            Lib_IntVector_Intrinsics_vec512 v820 = v81;
            Lib_IntVector_Intrinsics_vec512 v920 = v91;
            Lib_IntVector_Intrinsics_vec512 v1020 = v101;
            Lib_IntVector_Intrinsics_vec512 v1120 = v111;
            Lib_IntVector_Intrinsics_vec512 v1220 = v121;
            Lib_IntVector_Intrinsics_vec512 v1320 = v131;
            Lib_IntVector_Intrinsics_vec512 v1420 = v141;
            Lib_IntVector_Intrinsics_vec512 v1520 = v151;
            Lib_IntVector_Intrinsics_vec512
            v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v020, v170);
            Lib_IntVector_Intrinsics_vec512
            v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v020, v170);
            Lib_IntVector_Intrinsics_vec512
            v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v220, v320);
            Lib_IntVector_Intrinsics_vec512
            v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v220, v320);
            Lib_IntVector_Intrinsics_vec512
            v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v420, v520);
            Lib_IntVector_Intrinsics_vec512
            v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v420, v520);
            Lib_IntVector_Intrinsics_vec512
            v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v620, v720);
            Lib_IntVector_Intrinsics_vec512
            v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v620, v720);
            Lib_IntVector_Intrinsics_vec512
            v8_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v820, v920);
            Lib_IntVector_Intrinsics_vec512
            v9_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v820, v920);
            Lib_IntVector_Intrinsics_vec512
            v10_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1020, v1120);
            Lib_IntVector_Intrinsics_vec512
            v11_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1020, v1120);
            Lib_IntVector_Intrinsics_vec512
            v12_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1220, v1320);
            Lib_IntVector_Intrinsics_vec512
            v13_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1220, v1320);
            Lib_IntVector_Intrinsics_vec512
            v14_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1420, v1520);
            Lib_IntVector_Intrinsics_vec512
            v15_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1420, v1520);
            Lib_IntVector_Intrinsics_vec512 v0_0 = v0_;
            Lib_IntVector_Intrinsics_vec512 v1_0 = v1_;
            Lib_IntVector_Intrinsics_vec512 v2_0 = v2_;
            Lib_IntVector_Intrinsics_vec512 v3_0 = v3_;
            Lib_IntVector_Intrinsics_vec512 v4_0 = v4_;
            Lib_IntVector_Intrinsics_vec512 v5_0 = v5_;
            Lib_IntVector_Intrinsics_vec512 v6_0 = v6_;
            Lib_IntVector_Intrinsics_vec512 v7_0 = v7_;
            Lib_IntVector_Intrinsics_vec512 v8_0 = v8_;
            Lib_IntVector_Intrinsics_vec512 v9_0 = v9_;
            Lib_IntVector_Intrinsics_vec512 v10_0 = v10_;
            Lib_IntVector_Intrinsics_vec512 v11_0 = v11_;
            Lib_IntVector_Intrinsics_vec512 v12_0 = v12_;
            Lib_IntVector_Intrinsics_vec512 v13_0 = v13_;
            Lib_IntVector_Intrinsics_vec512 v14_0 = v14_;
            Lib_IntVector_Intrinsics_vec512 v15_0 = v15_;
            Lib_IntVector_Intrinsics_vec512 v021 = v0_0;
            Lib_IntVector_Intrinsics_vec512 v171 = v1_0;
            Lib_IntVector_Intrinsics_vec512 v221 = v2_0;
            Lib_IntVector_Intrinsics_vec512 v321 = v3_0;
            Lib_IntVector_Intrinsics_vec512 v421 = v4_0;
            Lib_IntVector_Intrinsics_vec512 v521 = v5_0;
            Lib_IntVector_Intrinsics_vec512 v621 = v6_0;
            Lib_IntVector_Intrinsics_vec512 v721 = v7_0;
            Lib_IntVector_Intrinsics_vec512 v821 = v8_0;
            Lib_IntVector_Intrinsics_vec512 v921 = v9_0;
            Lib_IntVector_Intrinsics_vec512 v1021 = v10_0;
            Lib_IntVector_Intrinsics_vec512 v1121 = v11_0;
            Lib_IntVector_Intrinsics_vec512 v1221 = v12_0;
            Lib_IntVector_Intrinsics_vec512 v1321 = v13_0;
            Lib_IntVector_Intrinsics_vec512 v1421 = v14_0;
            Lib_IntVector_Intrinsics_vec512 v1521 = v15_0;
            Lib_IntVector_Intrinsics_vec512
            v0_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v021, v221);
            Lib_IntVector_Intrinsics_vec512
            v2_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v021, v221);
            Lib_IntVector_Intrinsics_vec512
            v1_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v171, v321);
            Lib_IntVector_Intrinsics_vec512
            v3_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v171, v321);
            Lib_IntVector_Intrinsics_vec512
            v4_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v421, v621);
            Lib_IntVector_Intrinsics_vec512
            v6_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v421, v621);
            Lib_IntVector_Intrinsics_vec512
            v5_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v521, v721);
            Lib_IntVector_Intrinsics_vec512
            v7_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v521, v721);
            Lib_IntVector_Intrinsics_vec512
            v8_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v821, v1021);
            Lib_IntVector_Intrinsics_vec512
            v10_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v821, v1021);
            Lib_IntVector_Intrinsics_vec512
            v9_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v921, v1121);
            Lib_IntVector_Intrinsics_vec512
            v11_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v921, v1121);
            Lib_IntVector_Intrinsics_vec512
            v12_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1221, v1421);
            Lib_IntVector_Intrinsics_vec512
            v14_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1221, v1421);
            Lib_IntVector_Intrinsics_vec512
            v13_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1321, v1521);
            Lib_IntVector_Intrinsics_vec512
            v15_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1321, v1521);
            Lib_IntVector_Intrinsics_vec512 v0_10 = v0_1;
            Lib_IntVector_Intrinsics_vec512 v1_10 = v1_1;
            Lib_IntVector_Intrinsics_vec512 v2_10 = v2_1;
            Lib_IntVector_Intrinsics_vec512 v3_10 = v3_1;
            Lib_IntVector_Intrinsics_vec512 v4_10 = v4_1;
            Lib_IntVector_Intrinsics_vec512 v5_10 = v5_1;
            Lib_IntVector_Intrinsics_vec512 v6_10 = v6_1;
            Lib_IntVector_Intrinsics_vec512 v7_10 = v7_1;
            Lib_IntVector_Intrinsics_vec512 v8_10 = v8_1;
            Lib_IntVector_Intrinsics_vec512 v9_10 = v9_1;
            Lib_IntVector_Intrinsics_vec512 v10_10 = v10_1;
            Lib_IntVector_Intrinsics_vec512 v11_10 = v11_1;
            Lib_IntVector_Intrinsics_vec512 v12_10 = v12_1;
            Lib_IntVector_Intrinsics_vec512 v13_10 = v13_1;
            Lib_IntVector_Intrinsics_vec512 v14_10 = v14_1;
            Lib_IntVector_Intrinsics_vec512 v15_10 = v15_1;
            Lib_IntVector_Intrinsics_vec512 v022 = v0_10;
            Lib_IntVector_Intrinsics_vec512 v172 = v1_10;
            Lib_IntVector_Intrinsics_vec512 v222 = v2_10;
            Lib_IntVector_Intrinsics_vec512 v322 = v3_10;
            Lib_IntVector_Intrinsics_vec512 v422 = v4_10;
            Lib_IntVector_Intrinsics_vec512 v522 = v5_10;
            Lib_IntVector_Intrinsics_vec512 v622 = v6_10;
            Lib_IntVector_Intrinsics_vec512 v722 = v7_10;
            Lib_IntVector_Intrinsics_vec512 v822 = v8_10;
            Lib_IntVector_Intrinsics_vec512 v922 = v9_10;
            Lib_IntVector_Intrinsics_vec512 v1022 = v10_10;
            Lib_IntVector_Intrinsics_vec512 v1122 = v11_10;
            Lib_IntVector_Intrinsics_vec512 v1222 = v12_10;
            Lib_IntVector_Intrinsics_vec512 v1322 = v13_10;
            Lib_IntVector_Intrinsics_vec512 v1422 = v14_10;
            Lib_IntVector_Intrinsics_vec512 v1522 = v15_10;
            Lib_IntVector_Intrinsics_vec512
            v0_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v022, v422);
            Lib_IntVector_Intrinsics_vec512
            v4_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v022, v422);
            Lib_IntVector_Intrinsics_vec512
            v1_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v172, v522);
            Lib_IntVector_Intrinsics_vec512
            v5_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v172, v522);
            Lib_IntVector_Intrinsics_vec512
            v2_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v222, v622);
            Lib_IntVector_Intrinsics_vec512
            v6_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v222, v622);
            Lib_IntVector_Intrinsics_vec512
            v3_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v322, v722);
            Lib_IntVector_Intrinsics_vec512
            v7_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v322, v722);
            Lib_IntVector_Intrinsics_vec512
            v8_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v822, v1222);
            Lib_IntVector_Intrinsics_vec512
            v12_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v822, v1222);
            Lib_IntVector_Intrinsics_vec512
            v9_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v922, v1322);
            Lib_IntVector_Intrinsics_vec512
            v13_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v922, v1322);
            Lib_IntVector_Intrinsics_vec512
            v10_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1022, v1422);
            Lib_IntVector_Intrinsics_vec512
            v14_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1022, v1422);
            Lib_IntVector_Intrinsics_vec512
            v11_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1122, v1522);
            Lib_IntVector_Intrinsics_vec512
            v15_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1122, v1522);
            Lib_IntVector_Intrinsics_vec512 v0_20 = v0_2;
            Lib_IntVector_Intrinsics_vec512 v1_20 = v1_2;
            Lib_IntVector_Intrinsics_vec512 v2_20 = v2_2;
            Lib_IntVector_Intrinsics_vec512 v3_20 = v3_2;
            Lib_IntVector_Intrinsics_vec512 v4_20 = v4_2;
            Lib_IntVector_Intrinsics_vec512 v5_20 = v5_2;
            Lib_IntVector_Intrinsics_vec512 v6_20 = v6_2;
            Lib_IntVector_Intrinsics_vec512 v7_20 = v7_2;
            Lib_IntVector_Intrinsics_vec512 v8_20 = v8_2;
            Lib_IntVector_Intrinsics_vec512 v9_20 = v9_2;
            Lib_IntVector_Intrinsics_vec512 v10_20 = v10_2;
            Lib_IntVector_Intrinsics_vec512 v11_20 = v11_2;
            Lib_IntVector_Intrinsics_vec512 v12_20 = v12_2;
            Lib_IntVector_Intrinsics_vec512 v13_20 = v13_2;
            Lib_IntVector_Intrinsics_vec512 v14_20 = v14_2;
            Lib_IntVector_Intrinsics_vec512 v15_20 = v15_2;
            Lib_IntVector_Intrinsics_vec512 v02 = v0_20;
            Lib_IntVector_Intrinsics_vec512 v17 = v1_20;
            Lib_IntVector_Intrinsics_vec512 v22 = v2_20;
            Lib_IntVector_Intrinsics_vec512 v32 = v3_20;
            Lib_IntVector_Intrinsics_vec512 v42 = v4_20;
            Lib_IntVector_Intrinsics_vec512 v52 = v5_20;
            Lib_IntVector_Intrinsics_vec512 v62 = v6_20;
            Lib_IntVector_Intrinsics_vec512 v72 = v7_20;
            Lib_IntVector_Intrinsics_vec512 v82 = v8_20;
            Lib_IntVector_Intrinsics_vec512 v92 = v9_20;
            Lib_IntVector_Intrinsics_vec512 v102 = v10_20;
            Lib_IntVector_Intrinsics_vec512 v112 = v11_20;
            Lib_IntVector_Intrinsics_vec512 v122 = v12_20;
            Lib_IntVector_Intrinsics_vec512 v132 = v13_20;
            Lib_IntVector_Intrinsics_vec512 v142 = v14_20;
            Lib_IntVector_Intrinsics_vec512 v152 = v15_20;
            Lib_IntVector_Intrinsics_vec512
            v0_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v02, v82);
            Lib_IntVector_Intrinsics_vec512
            v8_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v02, v82);
            Lib_IntVector_Intrinsics_vec512
            v1_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v17, v92);
            Lib_IntVector_Intrinsics_vec512
            v9_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v17, v92);
            Lib_IntVector_Intrinsics_vec512
            v2_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v22, v102);
            Lib_IntVector_Intrinsics_vec512
            v10_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v22, v102);
            Lib_IntVector_Intrinsics_vec512
            v3_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v32, v112);
            Lib_IntVector_Intrinsics_vec512
            v11_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v32, v112);
            Lib_IntVector_Intrinsics_vec512
            v4_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v42, v122);
            Lib_IntVector_Intrinsics_vec512
            v12_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v42, v122);
            Lib_IntVector_Intrinsics_vec512
            v5_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v52, v132);
            Lib_IntVector_Intrinsics_vec512
            v13_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v52, v132);
            Lib_IntVector_Intrinsics_vec512
            v6_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v62, v142);
            Lib_IntVector_Intrinsics_vec512
            v14_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v62, v142);
            Lib_IntVector_Intrinsics_vec512
            v7_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v72, v152);
            Lib_IntVector_Intrinsics_vec512
            v15_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v72, v152);
            Lib_IntVector_Intrinsics_vec512 v0_30 = v0_3;
            Lib_IntVector_Intrinsics_vec512 v1_30 = v1_3;
            Lib_IntVector_Intrinsics_vec512 v2_30 = v2_3;
            Lib_IntVector_Intrinsics_vec512 v3_30 = v3_3;
            Lib_IntVector_Intrinsics_vec512 v4_30 = v4_3;
            Lib_IntVector_Intrinsics_vec512 v5_30 = v5_3;
            Lib_IntVector_Intrinsics_vec512 v6_30 = v6_3;
            Lib_IntVector_Intrinsics_vec512 v7_30 = v7_3;
            Lib_IntVector_Intrinsics_vec512 v8_30 = v8_3;
            Lib_IntVector_Intrinsics_vec512 v9_30 = v9_3;
            Lib_IntVector_Intrinsics_vec512 v10_30 = v10_3;
            Lib_IntVector_Intrinsics_vec512 v11_30 = v11_3;
            Lib_IntVector_Intrinsics_vec512 v12_30 = v12_3;
            Lib_IntVector_Intrinsics_vec512 v13_30 = v13_3;
            Lib_IntVector_Intrinsics_vec512 v14_30 = v14_3;
            Lib_IntVector_Intrinsics_vec512 v15_30 = v15_3;
            Lib_IntVector_Intrinsics_vec512 r0 = v0_30;
            Lib_IntVector_Intrinsics_vec512 r1 = v2_30;
            Lib_IntVector_Intrinsics_vec512 r2 = v1_30;
            Lib_IntVector_Intrinsics_vec512 r3 = v3_30;
            Lib_IntVector_Intrinsics_vec512 r4 = v4_30;
            Lib_IntVector_Intrinsics_vec512 r5 = v6_30;
            Lib_IntVector_Intrinsics_vec512 r6 = v5_30;
            Lib_IntVector_Intrinsics_vec512 r7 = v7_30;
            Lib_IntVector_Intrinsics_vec512 r8 = v8_30;
            Lib_IntVector_Intrinsics_vec512 r9 = v10_30;
            Lib_IntVector_Intrinsics_vec512 r10 = v9_30;
            Lib_IntVector_Intrinsics_vec512 r11 = v11_30;
            Lib_IntVector_Intrinsics_vec512 r12 = v12_30;
            Lib_IntVector_Intrinsics_vec512 r13 = v14_30;
            Lib_IntVector_Intrinsics_vec512 r14 = v13_30;
            Lib_IntVector_Intrinsics_vec512 r15 = v15_30;
            k[0U] = r0;
            k[1U] = r1;
            k[2U] = r2;
            k[3U] = r3;
            k[4U] = r4;
            k[5U] = r5;
            k[6U] = r6;
            k[7U] = r7;
            k[8U] = r8;
            k[9U] = r9;
            k[10U] = r10;
            k[11U] = r11;
            k[12U] = r12;
            k[13U] = r13;
            k[14U] = r14;
            k[15U] = r15;
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                Lib_IntVector_Intrinsics_vec512
                x = Lib_IntVector_Intrinsics_vec512_load_le(plain + i * (uint32_t)64U);
                Lib_IntVector_Intrinsics_vec512 y = Lib_IntVector_Intrinsics_vec512_xor(x, k[i]);
                Lib_IntVector_Intrinsics_vec512_store_le(plain + i * (uint32_t)64U, y);
              }
            }
            memcpy(uu____2, plain, rem * sizeof (plain[0U]));
          }
        }
      }
    }
  }
}

void
Hacl_Chacha20_Vec512_chacha20_decrypt_512(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
  {
    Lib_IntVector_Intrinsics_vec512 ctx[16U];
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)16U; ++_i)
        ctx[_i] = Lib_IntVector_Intrinsics_vec512_zero;
    }
    {
      uint32_t rem;
      uint32_t nb;
      uint32_t rem1;
      chacha20_init_512(ctx, key, n, ctr);
      rem = len % (uint32_t)1024U;
      nb = len / (uint32_t)1024U;
      rem1 = len % (uint32_t)1024U;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < nb; i++)
        {
          uint8_t *uu____0 = out + i * (uint32_t)1024U;
          uint8_t *uu____1 = cipher + i * (uint32_t)1024U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
          {
            Lib_IntVector_Intrinsics_vec512 k[16U];
            {
              uint32_t _i;
              for (_i = 0U; _i < (uint32_t)16U; ++_i)
                k[_i] = Lib_IntVector_Intrinsics_vec512_zero;
            }
            chacha20_core_512(k, ctx, i);
            {
              Lib_IntVector_Intrinsics_vec512 v0 = k[0U];
              Lib_IntVector_Intrinsics_vec512 v1 = k[1U];
              Lib_IntVector_Intrinsics_vec512 v2 = k[2U];
              Lib_IntVector_Intrinsics_vec512 v3 = k[3U];
              Lib_IntVector_Intrinsics_vec512 v4 = k[4U];
              Lib_IntVector_Intrinsics_vec512 v5 = k[5U];
              Lib_IntVector_Intrinsics_vec512 v6 = k[6U];
              Lib_IntVector_Intrinsics_vec512 v7 = k[7U];
              Lib_IntVector_Intrinsics_vec512 v8 = k[8U];
              Lib_IntVector_Intrinsics_vec512 v9 = k[9U];
              Lib_IntVector_Intrinsics_vec512 v10 = k[10U];
              Lib_IntVector_Intrinsics_vec512 v11 = k[11U];
              Lib_IntVector_Intrinsics_vec512 v12 = k[12U];
              Lib_IntVector_Intrinsics_vec512 v13 = k[13U];
              Lib_IntVector_Intrinsics_vec512 v14 = k[14U];
              Lib_IntVector_Intrinsics_vec512 v15 = k[15U];
              Lib_IntVector_Intrinsics_vec512 v01 = v0;
              Lib_IntVector_Intrinsics_vec512 v16 = v1;
              Lib_IntVector_Intrinsics_vec512 v21 = v2;
              Lib_IntVector_Intrinsics_vec512 v31 = v3;
              Lib_IntVector_Intrinsics_vec512 v41 = v4;
              Lib_IntVector_Intrinsics_vec512 v51 = v5;
              Lib_IntVector_Intrinsics_vec512 v61 = v6;
              Lib_IntVector_Intrinsics_vec512 v71 = v7;
              Lib_IntVector_Intrinsics_vec512 v81 = v8;
              Lib_IntVector_Intrinsics_vec512 v91 = v9;
              Lib_IntVector_Intrinsics_vec512 v101 = v10;
              Lib_IntVector_Intrinsics_vec512 v111 = v11;
              Lib_IntVector_Intrinsics_vec512 v121 = v12;
              Lib_IntVector_Intrinsics_vec512 v131 = v13;
              Lib_IntVector_Intrinsics_vec512 v141 = v14;
              Lib_IntVector_Intrinsics_vec512 v151 = v15;
              Lib_IntVector_Intrinsics_vec512 v020 = v01;
              Lib_IntVector_Intrinsics_vec512 v170 = v16;
              Lib_IntVector_Intrinsics_vec512 v220 = v21;
              Lib_IntVector_Intrinsics_vec512 v320 = v31;
              Lib_IntVector_Intrinsics_vec512 v420 = v41;
              Lib_IntVector_Intrinsics_vec512 v520 = v51;
              Lib_IntVector_Intrinsics_vec512 v620 = v61;
              Lib_IntVector_Intrinsics_vec512 v720 = v71;
              Lib_IntVector_Intrinsics_vec512 v820 = v81;
              Lib_IntVector_Intrinsics_vec512 v920 = v91;
              Lib_IntVector_Intrinsics_vec512 v1020 = v101;
              Lib_IntVector_Intrinsics_vec512 v1120 = v111;
              Lib_IntVector_Intrinsics_vec512 v1220 = v121;
              Lib_IntVector_Intrinsics_vec512 v1320 = v131;
              Lib_IntVector_Intrinsics_vec512 v1420 = v141;
              Lib_IntVector_Intrinsics_vec512 v1520 = v151;
              Lib_IntVector_Intrinsics_vec512
              v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v020, v170);
              Lib_IntVector_Intrinsics_vec512
              v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v020, v170);
              Lib_IntVector_Intrinsics_vec512
              v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v220, v320);
              Lib_IntVector_Intrinsics_vec512
              v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v220, v320);
              Lib_IntVector_Intrinsics_vec512
              v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v420, v520);
              Lib_IntVector_Intrinsics_vec512
              v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v420, v520);
              Lib_IntVector_Intrinsics_vec512
              v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v620, v720);
              Lib_IntVector_Intrinsics_vec512
              v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v620, v720);
              Lib_IntVector_Intrinsics_vec512
              v8_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v820, v920);
              Lib_IntVector_Intrinsics_vec512
              v9_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v820, v920);
              Lib_IntVector_Intrinsics_vec512
              v10_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1020, v1120);
              Lib_IntVector_Intrinsics_vec512
              v11_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1020, v1120);
              Lib_IntVector_Intrinsics_vec512
              v12_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1220, v1320);
              Lib_IntVector_Intrinsics_vec512
              v13_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1220, v1320);
              Lib_IntVector_Intrinsics_vec512
              v14_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1420, v1520);
              Lib_IntVector_Intrinsics_vec512
              v15_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1420, v1520);
              Lib_IntVector_Intrinsics_vec512 v0_0 = v0_;
              Lib_IntVector_Intrinsics_vec512 v1_0 = v1_;
              Lib_IntVector_Intrinsics_vec512 v2_0 = v2_;
              Lib_IntVector_Intrinsics_vec512 v3_0 = v3_;
              Lib_IntVector_Intrinsics_vec512 v4_0 = v4_;
              Lib_IntVector_Intrinsics_vec512 v5_0 = v5_;
              Lib_IntVector_Intrinsics_vec512 v6_0 = v6_;
              Lib_IntVector_Intrinsics_vec512 v7_0 = v7_;
              Lib_IntVector_Intrinsics_vec512 v8_0 = v8_;
              Lib_IntVector_Intrinsics_vec512 v9_0 = v9_;
              Lib_IntVector_Intrinsics_vec512 v10_0 = v10_;
              Lib_IntVector_Intrinsics_vec512 v11_0 = v11_;
              Lib_IntVector_Intrinsics_vec512 v12_0 = v12_;
              Lib_IntVector_Intrinsics_vec512 v13_0 = v13_;
              Lib_IntVector_Intrinsics_vec512 v14_0 = v14_;
              Lib_IntVector_Intrinsics_vec512 v15_0 = v15_;
              Lib_IntVector_Intrinsics_vec512 v021 = v0_0;
              Lib_IntVector_Intrinsics_vec512 v171 = v1_0;
              Lib_IntVector_Intrinsics_vec512 v221 = v2_0;
              Lib_IntVector_Intrinsics_vec512 v321 = v3_0;
              Lib_IntVector_Intrinsics_vec512 v421 = v4_0;
              Lib_IntVector_Intrinsics_vec512 v521 = v5_0;
              Lib_IntVector_Intrinsics_vec512 v621 = v6_0;
              Lib_IntVector_Intrinsics_vec512 v721 = v7_0;
              Lib_IntVector_Intrinsics_vec512 v821 = v8_0;
              Lib_IntVector_Intrinsics_vec512 v921 = v9_0;
              Lib_IntVector_Intrinsics_vec512 v1021 = v10_0;
              Lib_IntVector_Intrinsics_vec512 v1121 = v11_0;
              Lib_IntVector_Intrinsics_vec512 v1221 = v12_0;
              Lib_IntVector_Intrinsics_vec512 v1321 = v13_0;
              Lib_IntVector_Intrinsics_vec512 v1421 = v14_0;
              Lib_IntVector_Intrinsics_vec512 v1521 = v15_0;
              Lib_IntVector_Intrinsics_vec512
              v0_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v021, v221);
              Lib_IntVector_Intrinsics_vec512
              v2_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v021, v221);
              Lib_IntVector_Intrinsics_vec512
              v1_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v171, v321);
              Lib_IntVector_Intrinsics_vec512
              v3_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v171, v321);
              Lib_IntVector_Intrinsics_vec512
              v4_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v421, v621);
              Lib_IntVector_Intrinsics_vec512
              v6_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v421, v621);
              Lib_IntVector_Intrinsics_vec512
              v5_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v521, v721);
              Lib_IntVector_Intrinsics_vec512
              v7_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v521, v721);
              Lib_IntVector_Intrinsics_vec512
              v8_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v821, v1021);
              Lib_IntVector_Intrinsics_vec512
              v10_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v821, v1021);
              Lib_IntVector_Intrinsics_vec512
              v9_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v921, v1121);
              Lib_IntVector_Intrinsics_vec512
              v11_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v921, v1121);
              Lib_IntVector_Intrinsics_vec512
              v12_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1221, v1421);
              Lib_IntVector_Intrinsics_vec512
              v14_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1221, v1421);
              Lib_IntVector_Intrinsics_vec512
              v13_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1321, v1521);
              Lib_IntVector_Intrinsics_vec512
              v15_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1321, v1521);
              Lib_IntVector_Intrinsics_vec512 v0_10 = v0_1;
              Lib_IntVector_Intrinsics_vec512 v1_10 = v1_1;
              Lib_IntVector_Intrinsics_vec512 v2_10 = v2_1;
              Lib_IntVector_Intrinsics_vec512 v3_10 = v3_1;
              Lib_IntVector_Intrinsics_vec512 v4_10 = v4_1;
              Lib_IntVector_Intrinsics_vec512 v5_10 = v5_1;
              Lib_IntVector_Intrinsics_vec512 v6_10 = v6_1;
              Lib_IntVector_Intrinsics_vec512 v7_10 = v7_1;
              Lib_IntVector_Intrinsics_vec512 v8_10 = v8_1;
              Lib_IntVector_Intrinsics_vec512 v9_10 = v9_1;
              Lib_IntVector_Intrinsics_vec512 v10_10 = v10_1;
              Lib_IntVector_Intrinsics_vec512 v11_10 = v11_1;
              Lib_IntVector_Intrinsics_vec512 v12_10 = v12_1;
              Lib_IntVector_Intrinsics_vec512 v13_10 = v13_1;
              Lib_IntVector_Intrinsics_vec512 v14_10 = v14_1;
              Lib_IntVector_Intrinsics_vec512 v15_10 = v15_1;
              Lib_IntVector_Intrinsics_vec512 v022 = v0_10;
              Lib_IntVector_Intrinsics_vec512 v172 = v1_10;
              Lib_IntVector_Intrinsics_vec512 v222 = v2_10;
              Lib_IntVector_Intrinsics_vec512 v322 = v3_10;
              Lib_IntVector_Intrinsics_vec512 v422 = v4_10;
              Lib_IntVector_Intrinsics_vec512 v522 = v5_10;
              Lib_IntVector_Intrinsics_vec512 v622 = v6_10;
              Lib_IntVector_Intrinsics_vec512 v722 = v7_10;
              Lib_IntVector_Intrinsics_vec512 v822 = v8_10;
              Lib_IntVector_Intrinsics_vec512 v922 = v9_10;
              Lib_IntVector_Intrinsics_vec512 v1022 = v10_10;
              Lib_IntVector_Intrinsics_vec512 v1122 = v11_10;
              Lib_IntVector_Intrinsics_vec512 v1222 = v12_10;
              Lib_IntVector_Intrinsics_vec512 v1322 = v13_10;
              Lib_IntVector_Intrinsics_vec512 v1422 = v14_10;
              Lib_IntVector_Intrinsics_vec512 v1522 = v15_10;
              Lib_IntVector_Intrinsics_vec512
              v0_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v022, v422);
              Lib_IntVector_Intrinsics_vec512
              v4_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v022, v422);
              Lib_IntVector_Intrinsics_vec512
              v1_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v172, v522);
              Lib_IntVector_Intrinsics_vec512
              v5_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v172, v522);
              Lib_IntVector_Intrinsics_vec512
              v2_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v222, v622);
              Lib_IntVector_Intrinsics_vec512
              v6_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v222, v622);
              Lib_IntVector_Intrinsics_vec512
              v3_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v322, v722);
              Lib_IntVector_Intrinsics_vec512
              v7_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v322, v722);
              Lib_IntVector_Intrinsics_vec512
              v8_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v822, v1222);
              Lib_IntVector_Intrinsics_vec512
              v12_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v822, v1222);
              Lib_IntVector_Intrinsics_vec512
              v9_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v922, v1322);
              Lib_IntVector_Intrinsics_vec512
              v13_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v922, v1322);
              Lib_IntVector_Intrinsics_vec512
              v10_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1022, v1422);
              Lib_IntVector_Intrinsics_vec512
              v14_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1022, v1422);
              Lib_IntVector_Intrinsics_vec512
              v11_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1122, v1522);
              Lib_IntVector_Intrinsics_vec512
              v15_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1122, v1522);
              Lib_IntVector_Intrinsics_vec512 v0_20 = v0_2;
              Lib_IntVector_Intrinsics_vec512 v1_20 = v1_2;
              Lib_IntVector_Intrinsics_vec512 v2_20 = v2_2;
              Lib_IntVector_Intrinsics_vec512 v3_20 = v3_2;
              Lib_IntVector_Intrinsics_vec512 v4_20 = v4_2;
              Lib_IntVector_Intrinsics_vec512 v5_20 = v5_2;
              Lib_IntVector_Intrinsics_vec512 v6_20 = v6_2;
              Lib_IntVector_Intrinsics_vec512 v7_20 = v7_2;
              Lib_IntVector_Intrinsics_vec512 v8_20 = v8_2;
              Lib_IntVector_Intrinsics_vec512 v9_20 = v9_2;
              Lib_IntVector_Intrinsics_vec512 v10_20 = v10_2;
              Lib_IntVector_Intrinsics_vec512 v11_20 = v11_2;
              Lib_IntVector_Intrinsics_vec512 v12_20 = v12_2;
              Lib_IntVector_Intrinsics_vec512 v13_20 = v13_2;
              Lib_IntVector_Intrinsics_vec512 v14_20 = v14_2;
              Lib_IntVector_Intrinsics_vec512 v15_20 = v15_2;
              Lib_IntVector_Intrinsics_vec512 v02 = v0_20;
              Lib_IntVector_Intrinsics_vec512 v17 = v1_20;
              Lib_IntVector_Intrinsics_vec512 v22 = v2_20;
              Lib_IntVector_Intrinsics_vec512 v32 = v3_20;
              Lib_IntVector_Intrinsics_vec512 v42 = v4_20;
              Lib_IntVector_Intrinsics_vec512 v52 = v5_20;
              Lib_IntVector_Intrinsics_vec512 v62 = v6_20;
              Lib_IntVector_Intrinsics_vec512 v72 = v7_20;
              Lib_IntVector_Intrinsics_vec512 v82 = v8_20;
              Lib_IntVector_Intrinsics_vec512 v92 = v9_20;
              Lib_IntVector_Intrinsics_vec512 v102 = v10_20;
              Lib_IntVector_Intrinsics_vec512 v112 = v11_20;
              Lib_IntVector_Intrinsics_vec512 v122 = v12_20;
              Lib_IntVector_Intrinsics_vec512 v132 = v13_20;
              Lib_IntVector_Intrinsics_vec512 v142 = v14_20;
              Lib_IntVector_Intrinsics_vec512 v152 = v15_20;
              Lib_IntVector_Intrinsics_vec512
              v0_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v02, v82);
              Lib_IntVector_Intrinsics_vec512
              v8_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v02, v82);
              Lib_IntVector_Intrinsics_vec512
              v1_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v17, v92);
              Lib_IntVector_Intrinsics_vec512
              v9_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v17, v92);
              Lib_IntVector_Intrinsics_vec512
              v2_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v22, v102);
              Lib_IntVector_Intrinsics_vec512
              v10_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v22, v102);
              Lib_IntVector_Intrinsics_vec512
              v3_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v32, v112);
              Lib_IntVector_Intrinsics_vec512
              v11_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v32, v112);
              Lib_IntVector_Intrinsics_vec512
              v4_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v42, v122);
              Lib_IntVector_Intrinsics_vec512
              v12_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v42, v122);
              Lib_IntVector_Intrinsics_vec512
              v5_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v52, v132);
              Lib_IntVector_Intrinsics_vec512
              v13_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v52, v132);
              Lib_IntVector_Intrinsics_vec512
              v6_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v62, v142);
              Lib_IntVector_Intrinsics_vec512
              v14_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v62, v142);
              Lib_IntVector_Intrinsics_vec512
              v7_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v72, v152);
              Lib_IntVector_Intrinsics_vec512
              v15_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v72, v152);
              Lib_IntVector_Intrinsics_vec512 v0_30 = v0_3;
              Lib_IntVector_Intrinsics_vec512 v1_30 = v1_3;
              Lib_IntVector_Intrinsics_vec512 v2_30 = v2_3;
              Lib_IntVector_Intrinsics_vec512 v3_30 = v3_3;
              Lib_IntVector_Intrinsics_vec512 v4_30 = v4_3;
              Lib_IntVector_Intrinsics_vec512 v5_30 = v5_3;
              Lib_IntVector_Intrinsics_vec512 v6_30 = v6_3;
              Lib_IntVector_Intrinsics_vec512 v7_30 = v7_3;
              Lib_IntVector_Intrinsics_vec512 v8_30 = v8_3;
              Lib_IntVector_Intrinsics_vec512 v9_30 = v9_3;
              Lib_IntVector_Intrinsics_vec512 v10_30 = v10_3;
              Lib_IntVector_Intrinsics_vec512 v11_30 = v11_3;
              Lib_IntVector_Intrinsics_vec512 v12_30 = v12_3;
              Lib_IntVector_Intrinsics_vec512 v13_30 = v13_3;
              Lib_IntVector_Intrinsics_vec512 v14_30 = v14_3;
              Lib_IntVector_Intrinsics_vec512 v15_30 = v15_3;
              Lib_IntVector_Intrinsics_vec512 r0 = v0_30;
              Lib_IntVector_Intrinsics_vec512 r1 = v2_30;
              Lib_IntVector_Intrinsics_vec512 r2 = v1_30;
              Lib_IntVector_Intrinsics_vec512 r3 = v3_30;
              Lib_IntVector_Intrinsics_vec512 r4 = v4_30;
              Lib_IntVector_Intrinsics_vec512 r5 = v6_30;
              Lib_IntVector_Intrinsics_vec512 r6 = v5_30;
              Lib_IntVector_Intrinsics_vec512 r7 = v7_30;
              Lib_IntVector_Intrinsics_vec512 r8 = v8_30;
              Lib_IntVector_Intrinsics_vec512 r9 = v10_30;
              Lib_IntVector_Intrinsics_vec512 r10 = v9_30;
              Lib_IntVector_Intrinsics_vec512 r11 = v11_30;
              Lib_IntVector_Intrinsics_vec512 r12 = v12_30;
              Lib_IntVector_Intrinsics_vec512 r13 = v14_30;
              Lib_IntVector_Intrinsics_vec512 r14 = v13_30;
              Lib_IntVector_Intrinsics_vec512 r15 = v15_30;
              k[0U] = r0;
              k[1U] = r1;
              k[2U] = r2;
              k[3U] = r3;
              k[4U] = r4;
              k[5U] = r5;
              k[6U] = r6;
              k[7U] = r7;
              k[8U] = r8;
              k[9U] = r9;
              k[10U] = r10;
              k[11U] = r11;
              k[12U] = r12;
              k[13U] = r13;
              k[14U] = r14;
              k[15U] = r15;
              {
                uint32_t i0;
                for (i0 = (uint32_t)0U; i0 < (uint32_t)16U; i0++)
                {
                  Lib_IntVector_Intrinsics_vec512
                  x = Lib_IntVector_Intrinsics_vec512_load_le(uu____1 + i0 * (uint32_t)64U);
                  Lib_IntVector_Intrinsics_vec512 y = Lib_IntVector_Intrinsics_vec512_xor(x, k[i0]);
                  Lib_IntVector_Intrinsics_vec512_store_le(uu____0 + i0 * (uint32_t)64U, y);
                }
              }
            }
          }
        }
      }
      if (rem1 > (uint32_t)0U)
      {
        uint8_t *uu____2 = out + nb * (uint32_t)1024U;
        uint8_t *uu____3 = cipher + nb * (uint32_t)1024U;
        uint8_t plain[1024U] = { 0U };
        memcpy(plain, uu____3, rem * sizeof (uu____3[0U]));
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
        {
          Lib_IntVector_Intrinsics_vec512 k[16U];
          {
            uint32_t _i;
            for (_i = 0U; _i < (uint32_t)16U; ++_i)
              k[_i] = Lib_IntVector_Intrinsics_vec512_zero;
          }
          chacha20_core_512(k, ctx, nb);
          {
            Lib_IntVector_Intrinsics_vec512 v0 = k[0U];
            Lib_IntVector_Intrinsics_vec512 v1 = k[1U];
            Lib_IntVector_Intrinsics_vec512 v2 = k[2U];
            Lib_IntVector_Intrinsics_vec512 v3 = k[3U];
            Lib_IntVector_Intrinsics_vec512 v4 = k[4U];
            Lib_IntVector_Intrinsics_vec512 v5 = k[5U];
            Lib_IntVector_Intrinsics_vec512 v6 = k[6U];
            Lib_IntVector_Intrinsics_vec512 v7 = k[7U];
            Lib_IntVector_Intrinsics_vec512 v8 = k[8U];
            Lib_IntVector_Intrinsics_vec512 v9 = k[9U];
            Lib_IntVector_Intrinsics_vec512 v10 = k[10U];
            Lib_IntVector_Intrinsics_vec512 v11 = k[11U];
            Lib_IntVector_Intrinsics_vec512 v12 = k[12U];
            Lib_IntVector_Intrinsics_vec512 v13 = k[13U];
            Lib_IntVector_Intrinsics_vec512 v14 = k[14U];
            Lib_IntVector_Intrinsics_vec512 v15 = k[15U];
            Lib_IntVector_Intrinsics_vec512 v01 = v0;
            Lib_IntVector_Intrinsics_vec512 v16 = v1;
            Lib_IntVector_Intrinsics_vec512 v21 = v2;
            Lib_IntVector_Intrinsics_vec512 v31 = v3;
            Lib_IntVector_Intrinsics_vec512 v41 = v4;
            Lib_IntVector_Intrinsics_vec512 v51 = v5;
            Lib_IntVector_Intrinsics_vec512 v61 = v6;
            Lib_IntVector_Intrinsics_vec512 v71 = v7;
            Lib_IntVector_Intrinsics_vec512 v81 = v8;
            Lib_IntVector_Intrinsics_vec512 v91 = v9;
            Lib_IntVector_Intrinsics_vec512 v101 = v10;
            Lib_IntVector_Intrinsics_vec512 v111 = v11;
            Lib_IntVector_Intrinsics_vec512 v121 = v12;
            Lib_IntVector_Intrinsics_vec512 v131 = v13;
            Lib_IntVector_Intrinsics_vec512 v141 = v14;
            Lib_IntVector_Intrinsics_vec512 v151 = v15;
            Lib_IntVector_Intrinsics_vec512 v020 = v01;
            Lib_IntVector_Intrinsics_vec512 v170 = v16;
            Lib_IntVector_Intrinsics_vec512 v220 = v21;
            Lib_IntVector_Intrinsics_vec512 v320 = v31;
            Lib_IntVector_Intrinsics_vec512 v420 = v41;
            Lib_IntVector_Intrinsics_vec512 v520 = v51;
            Lib_IntVector_Intrinsics_vec512 v620 = v61;
            Lib_IntVector_Intrinsics_vec512 v720 = v71;
            Lib_IntVector_Intrinsics_vec512 v820 = v81;
            Lib_IntVector_Intrinsics_vec512 v920 = v91;
            Lib_IntVector_Intrinsics_vec512 v1020 = v101;
            Lib_IntVector_Intrinsics_vec512 v1120 = v111;
            Lib_IntVector_Intrinsics_vec512 v1220 = v121;
            Lib_IntVector_Intrinsics_vec512 v1320 = v131;
            Lib_IntVector_Intrinsics_vec512 v1420 = v141;
            Lib_IntVector_Intrinsics_vec512 v1520 = v151;
            Lib_IntVector_Intrinsics_vec512
            v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v020, v170);
            Lib_IntVector_Intrinsics_vec512
            v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v020, v170);
            Lib_IntVector_Intrinsics_vec512
            v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v220, v320);
            Lib_IntVector_Intrinsics_vec512
            v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v220, v320);
            Lib_IntVector_Intrinsics_vec512
            v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v420, v520);
            Lib_IntVector_Intrinsics_vec512
            v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v420, v520);
            Lib_IntVector_Intrinsics_vec512
            v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v620, v720);
            Lib_IntVector_Intrinsics_vec512
            v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v620, v720);
            Lib_IntVector_Intrinsics_vec512
            v8_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v820, v920);
            Lib_IntVector_Intrinsics_vec512
            v9_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v820, v920);
            Lib_IntVector_Intrinsics_vec512
            v10_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1020, v1120);
            Lib_IntVector_Intrinsics_vec512
            v11_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1020, v1120);
            Lib_IntVector_Intrinsics_vec512
            v12_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1220, v1320);
            Lib_IntVector_Intrinsics_vec512
            v13_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1220, v1320);
            Lib_IntVector_Intrinsics_vec512
            v14_ = Lib_IntVector_Intrinsics_vec512_interleave_low32(v1420, v1520);
            Lib_IntVector_Intrinsics_vec512
            v15_ = Lib_IntVector_Intrinsics_vec512_interleave_high32(v1420, v1520);
            Lib_IntVector_Intrinsics_vec512 v0_0 = v0_;
            Lib_IntVector_Intrinsics_vec512 v1_0 = v1_;
            Lib_IntVector_Intrinsics_vec512 v2_0 = v2_;
            Lib_IntVector_Intrinsics_vec512 v3_0 = v3_;
            Lib_IntVector_Intrinsics_vec512 v4_0 = v4_;
            Lib_IntVector_Intrinsics_vec512 v5_0 = v5_;
            Lib_IntVector_Intrinsics_vec512 v6_0 = v6_;
            Lib_IntVector_Intrinsics_vec512 v7_0 = v7_;
            Lib_IntVector_Intrinsics_vec512 v8_0 = v8_;
            Lib_IntVector_Intrinsics_vec512 v9_0 = v9_;
            Lib_IntVector_Intrinsics_vec512 v10_0 = v10_;
            Lib_IntVector_Intrinsics_vec512 v11_0 = v11_;
            Lib_IntVector_Intrinsics_vec512 v12_0 = v12_;
            Lib_IntVector_Intrinsics_vec512 v13_0 = v13_;
            Lib_IntVector_Intrinsics_vec512 v14_0 = v14_;
            Lib_IntVector_Intrinsics_vec512 v15_0 = v15_;
            Lib_IntVector_Intrinsics_vec512 v021 = v0_0;
            Lib_IntVector_Intrinsics_vec512 v171 = v1_0;
            Lib_IntVector_Intrinsics_vec512 v221 = v2_0;
            Lib_IntVector_Intrinsics_vec512 v321 = v3_0;
            Lib_IntVector_Intrinsics_vec512 v421 = v4_0;
            Lib_IntVector_Intrinsics_vec512 v521 = v5_0;
            Lib_IntVector_Intrinsics_vec512 v621 = v6_0;
            Lib_IntVector_Intrinsics_vec512 v721 = v7_0;
            Lib_IntVector_Intrinsics_vec512 v821 = v8_0;
            Lib_IntVector_Intrinsics_vec512 v921 = v9_0;
            Lib_IntVector_Intrinsics_vec512 v1021 = v10_0;
            Lib_IntVector_Intrinsics_vec512 v1121 = v11_0;
            Lib_IntVector_Intrinsics_vec512 v1221 = v12_0;
            Lib_IntVector_Intrinsics_vec512 v1321 = v13_0;
            Lib_IntVector_Intrinsics_vec512 v1421 = v14_0;
            Lib_IntVector_Intrinsics_vec512 v1521 = v15_0;
            Lib_IntVector_Intrinsics_vec512
            v0_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v021, v221);
            Lib_IntVector_Intrinsics_vec512
            v2_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v021, v221);
            Lib_IntVector_Intrinsics_vec512
            v1_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v171, v321);
            Lib_IntVector_Intrinsics_vec512
            v3_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v171, v321);
            Lib_IntVector_Intrinsics_vec512
            v4_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v421, v621);
            Lib_IntVector_Intrinsics_vec512
            v6_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v421, v621);
            Lib_IntVector_Intrinsics_vec512
            v5_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v521, v721);
            Lib_IntVector_Intrinsics_vec512
            v7_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v521, v721);
            Lib_IntVector_Intrinsics_vec512
            v8_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v821, v1021);
            Lib_IntVector_Intrinsics_vec512
            v10_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v821, v1021);
            Lib_IntVector_Intrinsics_vec512
            v9_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v921, v1121);
            Lib_IntVector_Intrinsics_vec512
            v11_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v921, v1121);
            Lib_IntVector_Intrinsics_vec512
            v12_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1221, v1421);
            Lib_IntVector_Intrinsics_vec512
            v14_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1221, v1421);
            Lib_IntVector_Intrinsics_vec512
            v13_1 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v1321, v1521);
            Lib_IntVector_Intrinsics_vec512
            v15_1 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v1321, v1521);
            Lib_IntVector_Intrinsics_vec512 v0_10 = v0_1;
            Lib_IntVector_Intrinsics_vec512 v1_10 = v1_1;
            Lib_IntVector_Intrinsics_vec512 v2_10 = v2_1;
            Lib_IntVector_Intrinsics_vec512 v3_10 = v3_1;
            Lib_IntVector_Intrinsics_vec512 v4_10 = v4_1;
            Lib_IntVector_Intrinsics_vec512 v5_10 = v5_1;
            Lib_IntVector_Intrinsics_vec512 v6_10 = v6_1;
            Lib_IntVector_Intrinsics_vec512 v7_10 = v7_1;
            Lib_IntVector_Intrinsics_vec512 v8_10 = v8_1;
            Lib_IntVector_Intrinsics_vec512 v9_10 = v9_1;
            Lib_IntVector_Intrinsics_vec512 v10_10 = v10_1;
            Lib_IntVector_Intrinsics_vec512 v11_10 = v11_1;
            Lib_IntVector_Intrinsics_vec512 v12_10 = v12_1;
            Lib_IntVector_Intrinsics_vec512 v13_10 = v13_1;
            Lib_IntVector_Intrinsics_vec512 v14_10 = v14_1;
            Lib_IntVector_Intrinsics_vec512 v15_10 = v15_1;
            Lib_IntVector_Intrinsics_vec512 v022 = v0_10;
            Lib_IntVector_Intrinsics_vec512 v172 = v1_10;
            Lib_IntVector_Intrinsics_vec512 v222 = v2_10;
            Lib_IntVector_Intrinsics_vec512 v322 = v3_10;
            Lib_IntVector_Intrinsics_vec512 v422 = v4_10;
            Lib_IntVector_Intrinsics_vec512 v522 = v5_10;
            Lib_IntVector_Intrinsics_vec512 v622 = v6_10;
            Lib_IntVector_Intrinsics_vec512 v722 = v7_10;
            Lib_IntVector_Intrinsics_vec512 v822 = v8_10;
            Lib_IntVector_Intrinsics_vec512 v922 = v9_10;
            Lib_IntVector_Intrinsics_vec512 v1022 = v10_10;
            Lib_IntVector_Intrinsics_vec512 v1122 = v11_10;
            Lib_IntVector_Intrinsics_vec512 v1222 = v12_10;
            Lib_IntVector_Intrinsics_vec512 v1322 = v13_10;
            Lib_IntVector_Intrinsics_vec512 v1422 = v14_10;
            Lib_IntVector_Intrinsics_vec512 v1522 = v15_10;
            Lib_IntVector_Intrinsics_vec512
            v0_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v022, v422);
            Lib_IntVector_Intrinsics_vec512
            v4_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v022, v422);
            Lib_IntVector_Intrinsics_vec512
            v1_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v172, v522);
            Lib_IntVector_Intrinsics_vec512
            v5_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v172, v522);
            Lib_IntVector_Intrinsics_vec512
            v2_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v222, v622);
            Lib_IntVector_Intrinsics_vec512
            v6_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v222, v622);
            Lib_IntVector_Intrinsics_vec512
            v3_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v322, v722);
            Lib_IntVector_Intrinsics_vec512
            v7_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v322, v722);
            Lib_IntVector_Intrinsics_vec512
            v8_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v822, v1222);
            Lib_IntVector_Intrinsics_vec512
            v12_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v822, v1222);
            Lib_IntVector_Intrinsics_vec512
            v9_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v922, v1322);
            Lib_IntVector_Intrinsics_vec512
            v13_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v922, v1322);
            Lib_IntVector_Intrinsics_vec512
            v10_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1022, v1422);
            Lib_IntVector_Intrinsics_vec512
            v14_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1022, v1422);
            Lib_IntVector_Intrinsics_vec512
            v11_2 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1122, v1522);
            Lib_IntVector_Intrinsics_vec512
            v15_2 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1122, v1522);
            Lib_IntVector_Intrinsics_vec512 v0_20 = v0_2;
            Lib_IntVector_Intrinsics_vec512 v1_20 = v1_2;
            Lib_IntVector_Intrinsics_vec512 v2_20 = v2_2;
            Lib_IntVector_Intrinsics_vec512 v3_20 = v3_2;
            Lib_IntVector_Intrinsics_vec512 v4_20 = v4_2;
            Lib_IntVector_Intrinsics_vec512 v5_20 = v5_2;
            Lib_IntVector_Intrinsics_vec512 v6_20 = v6_2;
            Lib_IntVector_Intrinsics_vec512 v7_20 = v7_2;
            Lib_IntVector_Intrinsics_vec512 v8_20 = v8_2;
            Lib_IntVector_Intrinsics_vec512 v9_20 = v9_2;
            Lib_IntVector_Intrinsics_vec512 v10_20 = v10_2;
            Lib_IntVector_Intrinsics_vec512 v11_20 = v11_2;
            Lib_IntVector_Intrinsics_vec512 v12_20 = v12_2;
            Lib_IntVector_Intrinsics_vec512 v13_20 = v13_2;
            Lib_IntVector_Intrinsics_vec512 v14_20 = v14_2;
            Lib_IntVector_Intrinsics_vec512 v15_20 = v15_2;
            Lib_IntVector_Intrinsics_vec512 v02 = v0_20;
            Lib_IntVector_Intrinsics_vec512 v17 = v1_20;
            Lib_IntVector_Intrinsics_vec512 v22 = v2_20;
            Lib_IntVector_Intrinsics_vec512 v32 = v3_20;
            Lib_IntVector_Intrinsics_vec512 v42 = v4_20;
            Lib_IntVector_Intrinsics_vec512 v52 = v5_20;
            Lib_IntVector_Intrinsics_vec512 v62 = v6_20;
            Lib_IntVector_Intrinsics_vec512 v72 = v7_20;
            Lib_IntVector_Intrinsics_vec512 v82 = v8_20;
            Lib_IntVector_Intrinsics_vec512 v92 = v9_20;
            Lib_IntVector_Intrinsics_vec512 v102 = v10_20;
            Lib_IntVector_Intrinsics_vec512 v112 = v11_20;
            Lib_IntVector_Intrinsics_vec512 v122 = v12_20;
            Lib_IntVector_Intrinsics_vec512 v132 = v13_20;
            Lib_IntVector_Intrinsics_vec512 v142 = v14_20;
            Lib_IntVector_Intrinsics_vec512 v152 = v15_20;
            Lib_IntVector_Intrinsics_vec512
            v0_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v02, v82);
            Lib_IntVector_Intrinsics_vec512
            v8_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v02, v82);
            Lib_IntVector_Intrinsics_vec512
            v1_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v17, v92);
            Lib_IntVector_Intrinsics_vec512
            v9_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v17, v92);
            Lib_IntVector_Intrinsics_vec512
            v2_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v22, v102);
            Lib_IntVector_Intrinsics_vec512
            v10_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v22, v102);
            Lib_IntVector_Intrinsics_vec512
            v3_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v32, v112);
            Lib_IntVector_Intrinsics_vec512
            v11_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v32, v112);
            Lib_IntVector_Intrinsics_vec512
            v4_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v42, v122);
            Lib_IntVector_Intrinsics_vec512
            v12_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v42, v122);
            Lib_IntVector_Intrinsics_vec512
            v5_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v52, v132);
            Lib_IntVector_Intrinsics_vec512
            v13_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v52, v132);
            Lib_IntVector_Intrinsics_vec512
            v6_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v62, v142);
            Lib_IntVector_Intrinsics_vec512
            v14_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v62, v142);
            Lib_IntVector_Intrinsics_vec512
            v7_3 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v72, v152);
            Lib_IntVector_Intrinsics_vec512
            v15_3 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v72, v152);
            Lib_IntVector_Intrinsics_vec512 v0_30 = v0_3;
            Lib_IntVector_Intrinsics_vec512 v1_30 = v1_3;
            Lib_IntVector_Intrinsics_vec512 v2_30 = v2_3;
            Lib_IntVector_Intrinsics_vec512 v3_30 = v3_3;
            Lib_IntVector_Intrinsics_vec512 v4_30 = v4_3;
            Lib_IntVector_Intrinsics_vec512 v5_30 = v5_3;
            Lib_IntVector_Intrinsics_vec512 v6_30 = v6_3;
            Lib_IntVector_Intrinsics_vec512 v7_30 = v7_3;
            Lib_IntVector_Intrinsics_vec512 v8_30 = v8_3;
            Lib_IntVector_Intrinsics_vec512 v9_30 = v9_3;
            Lib_IntVector_Intrinsics_vec512 v10_30 = v10_3;
            Lib_IntVector_Intrinsics_vec512 v11_30 = v11_3;
            Lib_IntVector_Intrinsics_vec512 v12_30 = v12_3;
            Lib_IntVector_Intrinsics_vec512 v13_30 = v13_3;
            Lib_IntVector_Intrinsics_vec512 v14_30 = v14_3;
            Lib_IntVector_Intrinsics_vec512 v15_30 = v15_3;
            Lib_IntVector_Intrinsics_vec512 r0 = v0_30;
            Lib_IntVector_Intrinsics_vec512 r1 = v2_30;
            Lib_IntVector_Intrinsics_vec512 r2 = v1_30;
            Lib_IntVector_Intrinsics_vec512 r3 = v3_30;
            Lib_IntVector_Intrinsics_vec512 r4 = v4_30;
            Lib_IntVector_Intrinsics_vec512 r5 = v6_30;
            Lib_IntVector_Intrinsics_vec512 r6 = v5_30;
            Lib_IntVector_Intrinsics_vec512 r7 = v7_30;
            Lib_IntVector_Intrinsics_vec512 r8 = v8_30;
            Lib_IntVector_Intrinsics_vec512 r9 = v10_30;
            Lib_IntVector_Intrinsics_vec512 r10 = v9_30;
            Lib_IntVector_Intrinsics_vec512 r11 = v11_30;
            Lib_IntVector_Intrinsics_vec512 r12 = v12_30;
            Lib_IntVector_Intrinsics_vec512 r13 = v14_30;
            Lib_IntVector_Intrinsics_vec512 r14 = v13_30;
            Lib_IntVector_Intrinsics_vec512 r15 = v15_30;
            k[0U] = r0;
            k[1U] = r1;
            k[2U] = r2;
            k[3U] = r3;
            k[4U] = r4;
            k[5U] = r5;
            k[6U] = r6;
            k[7U] = r7;
            k[8U] = r8;
            k[9U] = r9;
            k[10U] = r10;
            k[11U] = r11;
            k[12U] = r12;
            k[13U] = r13;
            k[14U] = r14;
            k[15U] = r15;
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                Lib_IntVector_Intrinsics_vec512
                x = Lib_IntVector_Intrinsics_vec512_load_le(plain + i * (uint32_t)64U);
                Lib_IntVector_Intrinsics_vec512 y = Lib_IntVector_Intrinsics_vec512_xor(x, k[i]);
                Lib_IntVector_Intrinsics_vec512_store_le(plain + i * (uint32_t)64U, y);
              }
            }
            memcpy(uu____2, plain, rem * sizeof (plain[0U]));
          }
        }
      }
    }
  }
}

