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


#include "internal/Hacl_SHA2_Vec256.h"



typedef struct ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ snd;
}
___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_;

typedef struct ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ snd;
}
___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_;

typedef struct
___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ snd;
}
___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_;

typedef struct
___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__s
{
  uint8_t *fst;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  snd;
}
___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_;

static inline void
sha224_update8(
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  block,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  Lib_IntVector_Intrinsics_vec256 hash_old[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    hash_old[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  Lib_IntVector_Intrinsics_vec256 ws[16U];
  for (uint32_t _i = 0U; _i < (uint32_t)16U; ++_i)
    ws[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (Lib_IntVector_Intrinsics_vec256));
  uint8_t *b7 = block.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b6 = block.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b5 = block.snd.snd.snd.snd.snd.fst;
  uint8_t *b4 = block.snd.snd.snd.snd.fst;
  uint8_t *b3 = block.snd.snd.snd.fst;
  uint8_t *b2 = block.snd.snd.fst;
  uint8_t *b10 = block.snd.fst;
  uint8_t *b00 = block.fst;
  ws[0U] = Lib_IntVector_Intrinsics_vec256_load32_be(b00);
  ws[1U] = Lib_IntVector_Intrinsics_vec256_load32_be(b10);
  ws[2U] = Lib_IntVector_Intrinsics_vec256_load32_be(b2);
  ws[3U] = Lib_IntVector_Intrinsics_vec256_load32_be(b3);
  ws[4U] = Lib_IntVector_Intrinsics_vec256_load32_be(b4);
  ws[5U] = Lib_IntVector_Intrinsics_vec256_load32_be(b5);
  ws[6U] = Lib_IntVector_Intrinsics_vec256_load32_be(b6);
  ws[7U] = Lib_IntVector_Intrinsics_vec256_load32_be(b7);
  ws[8U] = Lib_IntVector_Intrinsics_vec256_load32_be(b00 + (uint32_t)32U);
  ws[9U] = Lib_IntVector_Intrinsics_vec256_load32_be(b10 + (uint32_t)32U);
  ws[10U] = Lib_IntVector_Intrinsics_vec256_load32_be(b2 + (uint32_t)32U);
  ws[11U] = Lib_IntVector_Intrinsics_vec256_load32_be(b3 + (uint32_t)32U);
  ws[12U] = Lib_IntVector_Intrinsics_vec256_load32_be(b4 + (uint32_t)32U);
  ws[13U] = Lib_IntVector_Intrinsics_vec256_load32_be(b5 + (uint32_t)32U);
  ws[14U] = Lib_IntVector_Intrinsics_vec256_load32_be(b6 + (uint32_t)32U);
  ws[15U] = Lib_IntVector_Intrinsics_vec256_load32_be(b7 + (uint32_t)32U);
  Lib_IntVector_Intrinsics_vec256 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec256 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec256 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec256 v30 = ws[3U];
  Lib_IntVector_Intrinsics_vec256 v40 = ws[4U];
  Lib_IntVector_Intrinsics_vec256 v50 = ws[5U];
  Lib_IntVector_Intrinsics_vec256 v60 = ws[6U];
  Lib_IntVector_Intrinsics_vec256 v70 = ws[7U];
  Lib_IntVector_Intrinsics_vec256
  v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v10);
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
  Lib_IntVector_Intrinsics_vec256 v0_0 = v0_;
  Lib_IntVector_Intrinsics_vec256 v1_0 = v1_;
  Lib_IntVector_Intrinsics_vec256 v2_0 = v2_;
  Lib_IntVector_Intrinsics_vec256 v3_0 = v3_;
  Lib_IntVector_Intrinsics_vec256 v4_0 = v4_;
  Lib_IntVector_Intrinsics_vec256 v5_0 = v5_;
  Lib_IntVector_Intrinsics_vec256 v6_0 = v6_;
  Lib_IntVector_Intrinsics_vec256 v7_0 = v7_;
  Lib_IntVector_Intrinsics_vec256
  v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v4_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v6_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v5_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256
  v7_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256 v0_10 = v0_1;
  Lib_IntVector_Intrinsics_vec256 v1_10 = v1_1;
  Lib_IntVector_Intrinsics_vec256 v2_10 = v2_1;
  Lib_IntVector_Intrinsics_vec256 v3_10 = v3_1;
  Lib_IntVector_Intrinsics_vec256 v4_10 = v4_1;
  Lib_IntVector_Intrinsics_vec256 v5_10 = v5_1;
  Lib_IntVector_Intrinsics_vec256 v6_10 = v6_1;
  Lib_IntVector_Intrinsics_vec256 v7_10 = v7_1;
  Lib_IntVector_Intrinsics_vec256
  v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v4_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v5_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v6_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256
  v7_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256 v0_20 = v0_2;
  Lib_IntVector_Intrinsics_vec256 v1_20 = v1_2;
  Lib_IntVector_Intrinsics_vec256 v2_20 = v2_2;
  Lib_IntVector_Intrinsics_vec256 v3_20 = v3_2;
  Lib_IntVector_Intrinsics_vec256 v4_20 = v4_2;
  Lib_IntVector_Intrinsics_vec256 v5_20 = v5_2;
  Lib_IntVector_Intrinsics_vec256 v6_20 = v6_2;
  Lib_IntVector_Intrinsics_vec256 v7_20 = v7_2;
  Lib_IntVector_Intrinsics_vec256 v0_3 = v0_20;
  Lib_IntVector_Intrinsics_vec256 v1_3 = v1_20;
  Lib_IntVector_Intrinsics_vec256 v2_3 = v2_20;
  Lib_IntVector_Intrinsics_vec256 v3_3 = v3_20;
  Lib_IntVector_Intrinsics_vec256 v4_3 = v4_20;
  Lib_IntVector_Intrinsics_vec256 v5_3 = v5_20;
  Lib_IntVector_Intrinsics_vec256 v6_3 = v6_20;
  Lib_IntVector_Intrinsics_vec256 v7_3 = v7_20;
  Lib_IntVector_Intrinsics_vec256 ws0 = v0_3;
  Lib_IntVector_Intrinsics_vec256 ws1 = v2_3;
  Lib_IntVector_Intrinsics_vec256 ws2 = v1_3;
  Lib_IntVector_Intrinsics_vec256 ws3 = v3_3;
  Lib_IntVector_Intrinsics_vec256 ws4 = v4_3;
  Lib_IntVector_Intrinsics_vec256 ws5 = v6_3;
  Lib_IntVector_Intrinsics_vec256 ws6 = v5_3;
  Lib_IntVector_Intrinsics_vec256 ws7 = v7_3;
  Lib_IntVector_Intrinsics_vec256 v0 = ws[8U];
  Lib_IntVector_Intrinsics_vec256 v1 = ws[9U];
  Lib_IntVector_Intrinsics_vec256 v2 = ws[10U];
  Lib_IntVector_Intrinsics_vec256 v3 = ws[11U];
  Lib_IntVector_Intrinsics_vec256 v4 = ws[12U];
  Lib_IntVector_Intrinsics_vec256 v5 = ws[13U];
  Lib_IntVector_Intrinsics_vec256 v6 = ws[14U];
  Lib_IntVector_Intrinsics_vec256 v7 = ws[15U];
  Lib_IntVector_Intrinsics_vec256
  v0_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v2_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v4_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v4, v5);
  Lib_IntVector_Intrinsics_vec256
  v5_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v4, v5);
  Lib_IntVector_Intrinsics_vec256
  v6_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v6, v7);
  Lib_IntVector_Intrinsics_vec256
  v7_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v6, v7);
  Lib_IntVector_Intrinsics_vec256 v0_5 = v0_4;
  Lib_IntVector_Intrinsics_vec256 v1_5 = v1_4;
  Lib_IntVector_Intrinsics_vec256 v2_5 = v2_4;
  Lib_IntVector_Intrinsics_vec256 v3_5 = v3_4;
  Lib_IntVector_Intrinsics_vec256 v4_5 = v4_4;
  Lib_IntVector_Intrinsics_vec256 v5_5 = v5_4;
  Lib_IntVector_Intrinsics_vec256 v6_5 = v6_4;
  Lib_IntVector_Intrinsics_vec256 v7_5 = v7_4;
  Lib_IntVector_Intrinsics_vec256
  v0_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_5, v2_5);
  Lib_IntVector_Intrinsics_vec256
  v2_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_5, v2_5);
  Lib_IntVector_Intrinsics_vec256
  v1_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_5, v3_5);
  Lib_IntVector_Intrinsics_vec256
  v3_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_5, v3_5);
  Lib_IntVector_Intrinsics_vec256
  v4_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_5, v6_5);
  Lib_IntVector_Intrinsics_vec256
  v6_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_5, v6_5);
  Lib_IntVector_Intrinsics_vec256
  v5_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_5, v7_5);
  Lib_IntVector_Intrinsics_vec256
  v7_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_5, v7_5);
  Lib_IntVector_Intrinsics_vec256 v0_12 = v0_11;
  Lib_IntVector_Intrinsics_vec256 v1_12 = v1_11;
  Lib_IntVector_Intrinsics_vec256 v2_12 = v2_11;
  Lib_IntVector_Intrinsics_vec256 v3_12 = v3_11;
  Lib_IntVector_Intrinsics_vec256 v4_12 = v4_11;
  Lib_IntVector_Intrinsics_vec256 v5_12 = v5_11;
  Lib_IntVector_Intrinsics_vec256 v6_12 = v6_11;
  Lib_IntVector_Intrinsics_vec256 v7_12 = v7_11;
  Lib_IntVector_Intrinsics_vec256
  v0_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_12, v4_12);
  Lib_IntVector_Intrinsics_vec256
  v4_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_12, v4_12);
  Lib_IntVector_Intrinsics_vec256
  v1_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_12, v5_12);
  Lib_IntVector_Intrinsics_vec256
  v5_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_12, v5_12);
  Lib_IntVector_Intrinsics_vec256
  v2_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_12, v6_12);
  Lib_IntVector_Intrinsics_vec256
  v6_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_12, v6_12);
  Lib_IntVector_Intrinsics_vec256
  v3_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_12, v7_12);
  Lib_IntVector_Intrinsics_vec256
  v7_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_12, v7_12);
  Lib_IntVector_Intrinsics_vec256 v0_22 = v0_21;
  Lib_IntVector_Intrinsics_vec256 v1_22 = v1_21;
  Lib_IntVector_Intrinsics_vec256 v2_22 = v2_21;
  Lib_IntVector_Intrinsics_vec256 v3_22 = v3_21;
  Lib_IntVector_Intrinsics_vec256 v4_22 = v4_21;
  Lib_IntVector_Intrinsics_vec256 v5_22 = v5_21;
  Lib_IntVector_Intrinsics_vec256 v6_22 = v6_21;
  Lib_IntVector_Intrinsics_vec256 v7_22 = v7_21;
  Lib_IntVector_Intrinsics_vec256 v0_6 = v0_22;
  Lib_IntVector_Intrinsics_vec256 v1_6 = v1_22;
  Lib_IntVector_Intrinsics_vec256 v2_6 = v2_22;
  Lib_IntVector_Intrinsics_vec256 v3_6 = v3_22;
  Lib_IntVector_Intrinsics_vec256 v4_6 = v4_22;
  Lib_IntVector_Intrinsics_vec256 v5_6 = v5_22;
  Lib_IntVector_Intrinsics_vec256 v6_6 = v6_22;
  Lib_IntVector_Intrinsics_vec256 v7_6 = v7_22;
  Lib_IntVector_Intrinsics_vec256 ws8 = v0_6;
  Lib_IntVector_Intrinsics_vec256 ws9 = v2_6;
  Lib_IntVector_Intrinsics_vec256 ws10 = v1_6;
  Lib_IntVector_Intrinsics_vec256 ws11 = v3_6;
  Lib_IntVector_Intrinsics_vec256 ws12 = v4_6;
  Lib_IntVector_Intrinsics_vec256 ws13 = v6_6;
  Lib_IntVector_Intrinsics_vec256 ws14 = v5_6;
  Lib_IntVector_Intrinsics_vec256 ws15 = v7_6;
  ws[0U] = ws0;
  ws[1U] = ws1;
  ws[2U] = ws2;
  ws[3U] = ws3;
  ws[4U] = ws4;
  ws[5U] = ws5;
  ws[6U] = ws6;
  ws[7U] = ws7;
  ws[8U] = ws8;
  ws[9U] = ws9;
  ws[10U] = ws10;
  ws[11U] = ws11;
  ws[12U] = ws12;
  ws[13U] = ws13;
  ws[14U] = ws14;
  ws[15U] = ws15;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
      Lib_IntVector_Intrinsics_vec256 ws_t = ws[i];
      Lib_IntVector_Intrinsics_vec256 a0 = hash[0U];
      Lib_IntVector_Intrinsics_vec256 b0 = hash[1U];
      Lib_IntVector_Intrinsics_vec256 c0 = hash[2U];
      Lib_IntVector_Intrinsics_vec256 d0 = hash[3U];
      Lib_IntVector_Intrinsics_vec256 e0 = hash[4U];
      Lib_IntVector_Intrinsics_vec256 f0 = hash[5U];
      Lib_IntVector_Intrinsics_vec256 g0 = hash[6U];
      Lib_IntVector_Intrinsics_vec256 h02 = hash[7U];
      Lib_IntVector_Intrinsics_vec256 k_e_t = Lib_IntVector_Intrinsics_vec256_load32(k_t);
      Lib_IntVector_Intrinsics_vec256
      t1 =
        Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(h02,
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(e0,
                    (uint32_t)6U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(e0,
                      (uint32_t)11U),
                    Lib_IntVector_Intrinsics_vec256_rotate_right32(e0, (uint32_t)25U)))),
              Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(e0, f0),
                Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_lognot(e0), g0))),
            k_e_t),
          ws_t);
      Lib_IntVector_Intrinsics_vec256
      t2 =
        Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(a0,
              (uint32_t)2U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(a0,
                (uint32_t)13U),
              Lib_IntVector_Intrinsics_vec256_rotate_right32(a0, (uint32_t)22U))),
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, b0),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, c0),
              Lib_IntVector_Intrinsics_vec256_and(b0, c0))));
      Lib_IntVector_Intrinsics_vec256 a1 = Lib_IntVector_Intrinsics_vec256_add32(t1, t2);
      Lib_IntVector_Intrinsics_vec256 b1 = a0;
      Lib_IntVector_Intrinsics_vec256 c1 = b0;
      Lib_IntVector_Intrinsics_vec256 d1 = c0;
      Lib_IntVector_Intrinsics_vec256 e1 = Lib_IntVector_Intrinsics_vec256_add32(d0, t1);
      Lib_IntVector_Intrinsics_vec256 f1 = e0;
      Lib_IntVector_Intrinsics_vec256 g1 = f0;
      Lib_IntVector_Intrinsics_vec256 h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)4U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        Lib_IntVector_Intrinsics_vec256 t16 = ws[i];
        Lib_IntVector_Intrinsics_vec256 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256
        s1 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t2,
              (uint32_t)17U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t2,
                (uint32_t)19U),
              Lib_IntVector_Intrinsics_vec256_shift_right32(t2, (uint32_t)10U)));
        Lib_IntVector_Intrinsics_vec256
        s0 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t15,
              (uint32_t)7U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t15,
                (uint32_t)18U),
              Lib_IntVector_Intrinsics_vec256_shift_right32(t15, (uint32_t)3U)));
        ws[i] =
          Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(s1,
                t7),
              s0),
            t16);
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = hash;
    Lib_IntVector_Intrinsics_vec256
    x = Lib_IntVector_Intrinsics_vec256_add32(hash[i], hash_old[i]);
    os[i] = x;
  }
}

typedef struct
__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__s
{
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  fst;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  snd;
}
__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_;

void
Hacl_SHA2_Vec256_sha224_8(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint8_t *dst4,
  uint8_t *dst5,
  uint8_t *dst6,
  uint8_t *dst7,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *input4,
  uint8_t *input5,
  uint8_t *input6,
  uint8_t *input7
)
{
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  ib =
    {
      .fst = input0,
      .snd = {
        .fst = input1,
        .snd = {
          .fst = input2,
          .snd = {
            .fst = input3,
            .snd = {
              .fst = input4,
              .snd = { .fst = input5, .snd = { .fst = input6, .snd = input7 } }
            }
          }
        }
      }
    };
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  rb =
    {
      .fst = dst0,
      .snd = {
        .fst = dst1,
        .snd = {
          .fst = dst2,
          .snd = {
            .fst = dst3,
            .snd = { .fst = dst4, .snd = { .fst = dst5, .snd = { .fst = dst6, .snd = dst7 } } }
          }
        }
      }
    };
  Lib_IntVector_Intrinsics_vec256 st[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = st;
    uint32_t hi = Hacl_Impl_SHA2_Generic_h224[i];
    Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_load32(hi);
    os[i] = x;
  }
  uint32_t rem = input_len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)input_len;
  uint32_t blocks0 = input_len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b7 = ib.snd.snd.snd.snd.snd.snd.snd;
    uint8_t *b6 = ib.snd.snd.snd.snd.snd.snd.fst;
    uint8_t *b5 = ib.snd.snd.snd.snd.snd.fst;
    uint8_t *b4 = ib.snd.snd.snd.snd.fst;
    uint8_t *b3 = ib.snd.snd.snd.fst;
    uint8_t *b2 = ib.snd.snd.fst;
    uint8_t *b1 = ib.snd.fst;
    uint8_t *b0 = ib.fst;
    uint8_t *bl0 = b0 + i * (uint32_t)64U;
    uint8_t *bl1 = b1 + i * (uint32_t)64U;
    uint8_t *bl2 = b2 + i * (uint32_t)64U;
    uint8_t *bl3 = b3 + i * (uint32_t)64U;
    uint8_t *bl4 = b4 + i * (uint32_t)64U;
    uint8_t *bl5 = b5 + i * (uint32_t)64U;
    uint8_t *bl6 = b6 + i * (uint32_t)64U;
    uint8_t *bl7 = b7 + i * (uint32_t)64U;
    ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
    mb =
      {
        .fst = bl0,
        .snd = {
          .fst = bl1,
          .snd = {
            .fst = bl2,
            .snd = {
              .fst = bl3,
              .snd = { .fst = bl4, .snd = { .fst = bl5, .snd = { .fst = bl6, .snd = bl7 } } }
            }
          }
        }
      };
    sha224_update8(mb, st);
  }
  uint32_t rem1 = input_len % (uint32_t)64U;
  uint8_t *b7 = ib.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b60 = ib.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b50 = ib.snd.snd.snd.snd.snd.fst;
  uint8_t *b40 = ib.snd.snd.snd.snd.fst;
  uint8_t *b30 = ib.snd.snd.snd.fst;
  uint8_t *b20 = ib.snd.snd.fst;
  uint8_t *b10 = ib.snd.fst;
  uint8_t *b00 = ib.fst;
  uint8_t *bl0 = b00 + input_len - rem1;
  uint8_t *bl1 = b10 + input_len - rem1;
  uint8_t *bl2 = b20 + input_len - rem1;
  uint8_t *bl3 = b30 + input_len - rem1;
  uint8_t *bl4 = b40 + input_len - rem1;
  uint8_t *bl5 = b50 + input_len - rem1;
  uint8_t *bl6 = b60 + input_len - rem1;
  uint8_t *bl7 = b7 + input_len - rem1;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  lb =
    {
      .fst = bl0,
      .snd = {
        .fst = bl1,
        .snd = {
          .fst = bl2,
          .snd = {
            .fst = bl3,
            .snd = { .fst = bl4, .snd = { .fst = bl5, .snd = { .fst = bl6, .snd = bl7 } } }
          }
        }
      }
    };
  uint32_t blocks;
  if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)64U;
  uint8_t last[1024U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = len_ << (uint32_t)3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b70 = lb.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b61 = lb.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b51 = lb.snd.snd.snd.snd.snd.fst;
  uint8_t *b41 = lb.snd.snd.snd.snd.fst;
  uint8_t *b31 = lb.snd.snd.snd.fst;
  uint8_t *b21 = lb.snd.snd.fst;
  uint8_t *b11 = lb.snd.fst;
  uint8_t *b01 = lb.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)128U;
  uint8_t *last2 = last + (uint32_t)256U;
  uint8_t *last3 = last + (uint32_t)384U;
  uint8_t *last4 = last + (uint32_t)512U;
  uint8_t *last5 = last + (uint32_t)640U;
  uint8_t *last6 = last + (uint32_t)768U;
  uint8_t *last7 = last + (uint32_t)896U;
  memcpy(last00, b01, rem * sizeof (uint8_t));
  last00[rem] = (uint8_t)0x80U;
  memcpy(last00 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut = { .fst = last010, .snd = last110 };
  uint8_t *l00 = scrut.fst;
  uint8_t *l01 = scrut.snd;
  memcpy(last10, b11, rem * sizeof (uint8_t));
  last10[rem] = (uint8_t)0x80U;
  memcpy(last10 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut0 = { .fst = last011, .snd = last111 };
  uint8_t *l10 = scrut0.fst;
  uint8_t *l11 = scrut0.snd;
  memcpy(last2, b21, rem * sizeof (uint8_t));
  last2[rem] = (uint8_t)0x80U;
  memcpy(last2 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut1 = { .fst = last012, .snd = last112 };
  uint8_t *l20 = scrut1.fst;
  uint8_t *l21 = scrut1.snd;
  memcpy(last3, b31, rem * sizeof (uint8_t));
  last3[rem] = (uint8_t)0x80U;
  memcpy(last3 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last013 = last3;
  uint8_t *last113 = last3 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut2 = { .fst = last013, .snd = last113 };
  uint8_t *l30 = scrut2.fst;
  uint8_t *l31 = scrut2.snd;
  memcpy(last4, b41, rem * sizeof (uint8_t));
  last4[rem] = (uint8_t)0x80U;
  memcpy(last4 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last014 = last4;
  uint8_t *last114 = last4 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut3 = { .fst = last014, .snd = last114 };
  uint8_t *l40 = scrut3.fst;
  uint8_t *l41 = scrut3.snd;
  memcpy(last5, b51, rem * sizeof (uint8_t));
  last5[rem] = (uint8_t)0x80U;
  memcpy(last5 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last015 = last5;
  uint8_t *last115 = last5 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut4 = { .fst = last015, .snd = last115 };
  uint8_t *l50 = scrut4.fst;
  uint8_t *l51 = scrut4.snd;
  memcpy(last6, b61, rem * sizeof (uint8_t));
  last6[rem] = (uint8_t)0x80U;
  memcpy(last6 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last016 = last6;
  uint8_t *last116 = last6 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut5 = { .fst = last016, .snd = last116 };
  uint8_t *l60 = scrut5.fst;
  uint8_t *l61 = scrut5.snd;
  memcpy(last7, b70, rem * sizeof (uint8_t));
  last7[rem] = (uint8_t)0x80U;
  memcpy(last7 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last01 = last7;
  uint8_t *last11 = last7 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut6 = { .fst = last01, .snd = last11 };
  uint8_t *l70 = scrut6.fst;
  uint8_t *l71 = scrut6.snd;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb0 =
    {
      .fst = l00,
      .snd = {
        .fst = l10,
        .snd = {
          .fst = l20,
          .snd = {
            .fst = l30,
            .snd = { .fst = l40, .snd = { .fst = l50, .snd = { .fst = l60, .snd = l70 } } }
          }
        }
      }
    };
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb1 =
    {
      .fst = l01,
      .snd = {
        .fst = l11,
        .snd = {
          .fst = l21,
          .snd = {
            .fst = l31,
            .snd = { .fst = l41, .snd = { .fst = l51, .snd = { .fst = l61, .snd = l71 } } }
          }
        }
      }
    };
  __K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  scrut7 = { .fst = mb0, .snd = mb1 };
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  last0 = scrut7.fst;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  last1 = scrut7.snd;
  sha224_update8(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha224_update8(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)8U * (uint32_t)8U * (uint32_t)4U);
  uint8_t hbuf[(uint32_t)8U * (uint32_t)8U * (uint32_t)4U];
  memset(hbuf, 0U, (uint32_t)8U * (uint32_t)8U * (uint32_t)4U * sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256 v0 = st[0U];
  Lib_IntVector_Intrinsics_vec256 v1 = st[1U];
  Lib_IntVector_Intrinsics_vec256 v2 = st[2U];
  Lib_IntVector_Intrinsics_vec256 v3 = st[3U];
  Lib_IntVector_Intrinsics_vec256 v4 = st[4U];
  Lib_IntVector_Intrinsics_vec256 v5 = st[5U];
  Lib_IntVector_Intrinsics_vec256 v6 = st[6U];
  Lib_IntVector_Intrinsics_vec256 v7 = st[7U];
  Lib_IntVector_Intrinsics_vec256 v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v0, v1);
  Lib_IntVector_Intrinsics_vec256 v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v2, v3);
  Lib_IntVector_Intrinsics_vec256 v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v4, v5);
  Lib_IntVector_Intrinsics_vec256
  v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v4, v5);
  Lib_IntVector_Intrinsics_vec256 v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v6, v7);
  Lib_IntVector_Intrinsics_vec256
  v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v6, v7);
  Lib_IntVector_Intrinsics_vec256 v0_0 = v0_;
  Lib_IntVector_Intrinsics_vec256 v1_0 = v1_;
  Lib_IntVector_Intrinsics_vec256 v2_0 = v2_;
  Lib_IntVector_Intrinsics_vec256 v3_0 = v3_;
  Lib_IntVector_Intrinsics_vec256 v4_0 = v4_;
  Lib_IntVector_Intrinsics_vec256 v5_0 = v5_;
  Lib_IntVector_Intrinsics_vec256 v6_0 = v6_;
  Lib_IntVector_Intrinsics_vec256 v7_0 = v7_;
  Lib_IntVector_Intrinsics_vec256
  v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v4_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v6_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v5_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256
  v7_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256 v0_10 = v0_1;
  Lib_IntVector_Intrinsics_vec256 v1_10 = v1_1;
  Lib_IntVector_Intrinsics_vec256 v2_10 = v2_1;
  Lib_IntVector_Intrinsics_vec256 v3_10 = v3_1;
  Lib_IntVector_Intrinsics_vec256 v4_10 = v4_1;
  Lib_IntVector_Intrinsics_vec256 v5_10 = v5_1;
  Lib_IntVector_Intrinsics_vec256 v6_10 = v6_1;
  Lib_IntVector_Intrinsics_vec256 v7_10 = v7_1;
  Lib_IntVector_Intrinsics_vec256
  v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v4_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v5_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v6_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256
  v7_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256 v0_20 = v0_2;
  Lib_IntVector_Intrinsics_vec256 v1_20 = v1_2;
  Lib_IntVector_Intrinsics_vec256 v2_20 = v2_2;
  Lib_IntVector_Intrinsics_vec256 v3_20 = v3_2;
  Lib_IntVector_Intrinsics_vec256 v4_20 = v4_2;
  Lib_IntVector_Intrinsics_vec256 v5_20 = v5_2;
  Lib_IntVector_Intrinsics_vec256 v6_20 = v6_2;
  Lib_IntVector_Intrinsics_vec256 v7_20 = v7_2;
  Lib_IntVector_Intrinsics_vec256 v0_3 = v0_20;
  Lib_IntVector_Intrinsics_vec256 v1_3 = v1_20;
  Lib_IntVector_Intrinsics_vec256 v2_3 = v2_20;
  Lib_IntVector_Intrinsics_vec256 v3_3 = v3_20;
  Lib_IntVector_Intrinsics_vec256 v4_3 = v4_20;
  Lib_IntVector_Intrinsics_vec256 v5_3 = v5_20;
  Lib_IntVector_Intrinsics_vec256 v6_3 = v6_20;
  Lib_IntVector_Intrinsics_vec256 v7_3 = v7_20;
  Lib_IntVector_Intrinsics_vec256 st0_ = v0_3;
  Lib_IntVector_Intrinsics_vec256 st1_ = v2_3;
  Lib_IntVector_Intrinsics_vec256 st2_ = v1_3;
  Lib_IntVector_Intrinsics_vec256 st3_ = v3_3;
  Lib_IntVector_Intrinsics_vec256 st4_ = v4_3;
  Lib_IntVector_Intrinsics_vec256 st5_ = v6_3;
  Lib_IntVector_Intrinsics_vec256 st6_ = v5_3;
  Lib_IntVector_Intrinsics_vec256 st7_ = v7_3;
  st[0U] = st0_;
  st[1U] = st1_;
  st[2U] = st2_;
  st[3U] = st3_;
  st[4U] = st4_;
  st[5U] = st5_;
  st[6U] = st6_;
  st[7U] = st7_;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256_store32_be(hbuf + i * (uint32_t)32U, st[i]);
  }
  uint8_t *b71 = rb.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b6 = rb.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b5 = rb.snd.snd.snd.snd.snd.fst;
  uint8_t *b4 = rb.snd.snd.snd.snd.fst;
  uint8_t *b3 = rb.snd.snd.snd.fst;
  uint8_t *b2 = rb.snd.snd.fst;
  uint8_t *b1 = rb.snd.fst;
  uint8_t *b0 = rb.fst;
  memcpy(b0, hbuf, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b1, hbuf + (uint32_t)32U, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b2, hbuf + (uint32_t)64U, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b3, hbuf + (uint32_t)96U, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b4, hbuf + (uint32_t)128U, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b5, hbuf + (uint32_t)160U, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b6, hbuf + (uint32_t)192U, (uint32_t)28U * sizeof (uint8_t));
  memcpy(b71, hbuf + (uint32_t)224U, (uint32_t)28U * sizeof (uint8_t));
}

static inline void
sha256_update8(
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  block,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  Lib_IntVector_Intrinsics_vec256 hash_old[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    hash_old[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  Lib_IntVector_Intrinsics_vec256 ws[16U];
  for (uint32_t _i = 0U; _i < (uint32_t)16U; ++_i)
    ws[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (Lib_IntVector_Intrinsics_vec256));
  uint8_t *b7 = block.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b6 = block.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b5 = block.snd.snd.snd.snd.snd.fst;
  uint8_t *b4 = block.snd.snd.snd.snd.fst;
  uint8_t *b3 = block.snd.snd.snd.fst;
  uint8_t *b2 = block.snd.snd.fst;
  uint8_t *b10 = block.snd.fst;
  uint8_t *b00 = block.fst;
  ws[0U] = Lib_IntVector_Intrinsics_vec256_load32_be(b00);
  ws[1U] = Lib_IntVector_Intrinsics_vec256_load32_be(b10);
  ws[2U] = Lib_IntVector_Intrinsics_vec256_load32_be(b2);
  ws[3U] = Lib_IntVector_Intrinsics_vec256_load32_be(b3);
  ws[4U] = Lib_IntVector_Intrinsics_vec256_load32_be(b4);
  ws[5U] = Lib_IntVector_Intrinsics_vec256_load32_be(b5);
  ws[6U] = Lib_IntVector_Intrinsics_vec256_load32_be(b6);
  ws[7U] = Lib_IntVector_Intrinsics_vec256_load32_be(b7);
  ws[8U] = Lib_IntVector_Intrinsics_vec256_load32_be(b00 + (uint32_t)32U);
  ws[9U] = Lib_IntVector_Intrinsics_vec256_load32_be(b10 + (uint32_t)32U);
  ws[10U] = Lib_IntVector_Intrinsics_vec256_load32_be(b2 + (uint32_t)32U);
  ws[11U] = Lib_IntVector_Intrinsics_vec256_load32_be(b3 + (uint32_t)32U);
  ws[12U] = Lib_IntVector_Intrinsics_vec256_load32_be(b4 + (uint32_t)32U);
  ws[13U] = Lib_IntVector_Intrinsics_vec256_load32_be(b5 + (uint32_t)32U);
  ws[14U] = Lib_IntVector_Intrinsics_vec256_load32_be(b6 + (uint32_t)32U);
  ws[15U] = Lib_IntVector_Intrinsics_vec256_load32_be(b7 + (uint32_t)32U);
  Lib_IntVector_Intrinsics_vec256 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec256 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec256 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec256 v30 = ws[3U];
  Lib_IntVector_Intrinsics_vec256 v40 = ws[4U];
  Lib_IntVector_Intrinsics_vec256 v50 = ws[5U];
  Lib_IntVector_Intrinsics_vec256 v60 = ws[6U];
  Lib_IntVector_Intrinsics_vec256 v70 = ws[7U];
  Lib_IntVector_Intrinsics_vec256
  v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v10);
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
  Lib_IntVector_Intrinsics_vec256 v0_0 = v0_;
  Lib_IntVector_Intrinsics_vec256 v1_0 = v1_;
  Lib_IntVector_Intrinsics_vec256 v2_0 = v2_;
  Lib_IntVector_Intrinsics_vec256 v3_0 = v3_;
  Lib_IntVector_Intrinsics_vec256 v4_0 = v4_;
  Lib_IntVector_Intrinsics_vec256 v5_0 = v5_;
  Lib_IntVector_Intrinsics_vec256 v6_0 = v6_;
  Lib_IntVector_Intrinsics_vec256 v7_0 = v7_;
  Lib_IntVector_Intrinsics_vec256
  v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v4_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v6_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v5_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256
  v7_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256 v0_10 = v0_1;
  Lib_IntVector_Intrinsics_vec256 v1_10 = v1_1;
  Lib_IntVector_Intrinsics_vec256 v2_10 = v2_1;
  Lib_IntVector_Intrinsics_vec256 v3_10 = v3_1;
  Lib_IntVector_Intrinsics_vec256 v4_10 = v4_1;
  Lib_IntVector_Intrinsics_vec256 v5_10 = v5_1;
  Lib_IntVector_Intrinsics_vec256 v6_10 = v6_1;
  Lib_IntVector_Intrinsics_vec256 v7_10 = v7_1;
  Lib_IntVector_Intrinsics_vec256
  v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v4_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v5_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v6_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256
  v7_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256 v0_20 = v0_2;
  Lib_IntVector_Intrinsics_vec256 v1_20 = v1_2;
  Lib_IntVector_Intrinsics_vec256 v2_20 = v2_2;
  Lib_IntVector_Intrinsics_vec256 v3_20 = v3_2;
  Lib_IntVector_Intrinsics_vec256 v4_20 = v4_2;
  Lib_IntVector_Intrinsics_vec256 v5_20 = v5_2;
  Lib_IntVector_Intrinsics_vec256 v6_20 = v6_2;
  Lib_IntVector_Intrinsics_vec256 v7_20 = v7_2;
  Lib_IntVector_Intrinsics_vec256 v0_3 = v0_20;
  Lib_IntVector_Intrinsics_vec256 v1_3 = v1_20;
  Lib_IntVector_Intrinsics_vec256 v2_3 = v2_20;
  Lib_IntVector_Intrinsics_vec256 v3_3 = v3_20;
  Lib_IntVector_Intrinsics_vec256 v4_3 = v4_20;
  Lib_IntVector_Intrinsics_vec256 v5_3 = v5_20;
  Lib_IntVector_Intrinsics_vec256 v6_3 = v6_20;
  Lib_IntVector_Intrinsics_vec256 v7_3 = v7_20;
  Lib_IntVector_Intrinsics_vec256 ws0 = v0_3;
  Lib_IntVector_Intrinsics_vec256 ws1 = v2_3;
  Lib_IntVector_Intrinsics_vec256 ws2 = v1_3;
  Lib_IntVector_Intrinsics_vec256 ws3 = v3_3;
  Lib_IntVector_Intrinsics_vec256 ws4 = v4_3;
  Lib_IntVector_Intrinsics_vec256 ws5 = v6_3;
  Lib_IntVector_Intrinsics_vec256 ws6 = v5_3;
  Lib_IntVector_Intrinsics_vec256 ws7 = v7_3;
  Lib_IntVector_Intrinsics_vec256 v0 = ws[8U];
  Lib_IntVector_Intrinsics_vec256 v1 = ws[9U];
  Lib_IntVector_Intrinsics_vec256 v2 = ws[10U];
  Lib_IntVector_Intrinsics_vec256 v3 = ws[11U];
  Lib_IntVector_Intrinsics_vec256 v4 = ws[12U];
  Lib_IntVector_Intrinsics_vec256 v5 = ws[13U];
  Lib_IntVector_Intrinsics_vec256 v6 = ws[14U];
  Lib_IntVector_Intrinsics_vec256 v7 = ws[15U];
  Lib_IntVector_Intrinsics_vec256
  v0_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v2_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v4_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v4, v5);
  Lib_IntVector_Intrinsics_vec256
  v5_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v4, v5);
  Lib_IntVector_Intrinsics_vec256
  v6_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v6, v7);
  Lib_IntVector_Intrinsics_vec256
  v7_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v6, v7);
  Lib_IntVector_Intrinsics_vec256 v0_5 = v0_4;
  Lib_IntVector_Intrinsics_vec256 v1_5 = v1_4;
  Lib_IntVector_Intrinsics_vec256 v2_5 = v2_4;
  Lib_IntVector_Intrinsics_vec256 v3_5 = v3_4;
  Lib_IntVector_Intrinsics_vec256 v4_5 = v4_4;
  Lib_IntVector_Intrinsics_vec256 v5_5 = v5_4;
  Lib_IntVector_Intrinsics_vec256 v6_5 = v6_4;
  Lib_IntVector_Intrinsics_vec256 v7_5 = v7_4;
  Lib_IntVector_Intrinsics_vec256
  v0_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_5, v2_5);
  Lib_IntVector_Intrinsics_vec256
  v2_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_5, v2_5);
  Lib_IntVector_Intrinsics_vec256
  v1_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_5, v3_5);
  Lib_IntVector_Intrinsics_vec256
  v3_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_5, v3_5);
  Lib_IntVector_Intrinsics_vec256
  v4_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_5, v6_5);
  Lib_IntVector_Intrinsics_vec256
  v6_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_5, v6_5);
  Lib_IntVector_Intrinsics_vec256
  v5_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_5, v7_5);
  Lib_IntVector_Intrinsics_vec256
  v7_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_5, v7_5);
  Lib_IntVector_Intrinsics_vec256 v0_12 = v0_11;
  Lib_IntVector_Intrinsics_vec256 v1_12 = v1_11;
  Lib_IntVector_Intrinsics_vec256 v2_12 = v2_11;
  Lib_IntVector_Intrinsics_vec256 v3_12 = v3_11;
  Lib_IntVector_Intrinsics_vec256 v4_12 = v4_11;
  Lib_IntVector_Intrinsics_vec256 v5_12 = v5_11;
  Lib_IntVector_Intrinsics_vec256 v6_12 = v6_11;
  Lib_IntVector_Intrinsics_vec256 v7_12 = v7_11;
  Lib_IntVector_Intrinsics_vec256
  v0_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_12, v4_12);
  Lib_IntVector_Intrinsics_vec256
  v4_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_12, v4_12);
  Lib_IntVector_Intrinsics_vec256
  v1_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_12, v5_12);
  Lib_IntVector_Intrinsics_vec256
  v5_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_12, v5_12);
  Lib_IntVector_Intrinsics_vec256
  v2_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_12, v6_12);
  Lib_IntVector_Intrinsics_vec256
  v6_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_12, v6_12);
  Lib_IntVector_Intrinsics_vec256
  v3_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_12, v7_12);
  Lib_IntVector_Intrinsics_vec256
  v7_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_12, v7_12);
  Lib_IntVector_Intrinsics_vec256 v0_22 = v0_21;
  Lib_IntVector_Intrinsics_vec256 v1_22 = v1_21;
  Lib_IntVector_Intrinsics_vec256 v2_22 = v2_21;
  Lib_IntVector_Intrinsics_vec256 v3_22 = v3_21;
  Lib_IntVector_Intrinsics_vec256 v4_22 = v4_21;
  Lib_IntVector_Intrinsics_vec256 v5_22 = v5_21;
  Lib_IntVector_Intrinsics_vec256 v6_22 = v6_21;
  Lib_IntVector_Intrinsics_vec256 v7_22 = v7_21;
  Lib_IntVector_Intrinsics_vec256 v0_6 = v0_22;
  Lib_IntVector_Intrinsics_vec256 v1_6 = v1_22;
  Lib_IntVector_Intrinsics_vec256 v2_6 = v2_22;
  Lib_IntVector_Intrinsics_vec256 v3_6 = v3_22;
  Lib_IntVector_Intrinsics_vec256 v4_6 = v4_22;
  Lib_IntVector_Intrinsics_vec256 v5_6 = v5_22;
  Lib_IntVector_Intrinsics_vec256 v6_6 = v6_22;
  Lib_IntVector_Intrinsics_vec256 v7_6 = v7_22;
  Lib_IntVector_Intrinsics_vec256 ws8 = v0_6;
  Lib_IntVector_Intrinsics_vec256 ws9 = v2_6;
  Lib_IntVector_Intrinsics_vec256 ws10 = v1_6;
  Lib_IntVector_Intrinsics_vec256 ws11 = v3_6;
  Lib_IntVector_Intrinsics_vec256 ws12 = v4_6;
  Lib_IntVector_Intrinsics_vec256 ws13 = v6_6;
  Lib_IntVector_Intrinsics_vec256 ws14 = v5_6;
  Lib_IntVector_Intrinsics_vec256 ws15 = v7_6;
  ws[0U] = ws0;
  ws[1U] = ws1;
  ws[2U] = ws2;
  ws[3U] = ws3;
  ws[4U] = ws4;
  ws[5U] = ws5;
  ws[6U] = ws6;
  ws[7U] = ws7;
  ws[8U] = ws8;
  ws[9U] = ws9;
  ws[10U] = ws10;
  ws[11U] = ws11;
  ws[12U] = ws12;
  ws[13U] = ws13;
  ws[14U] = ws14;
  ws[15U] = ws15;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
      Lib_IntVector_Intrinsics_vec256 ws_t = ws[i];
      Lib_IntVector_Intrinsics_vec256 a0 = hash[0U];
      Lib_IntVector_Intrinsics_vec256 b0 = hash[1U];
      Lib_IntVector_Intrinsics_vec256 c0 = hash[2U];
      Lib_IntVector_Intrinsics_vec256 d0 = hash[3U];
      Lib_IntVector_Intrinsics_vec256 e0 = hash[4U];
      Lib_IntVector_Intrinsics_vec256 f0 = hash[5U];
      Lib_IntVector_Intrinsics_vec256 g0 = hash[6U];
      Lib_IntVector_Intrinsics_vec256 h02 = hash[7U];
      Lib_IntVector_Intrinsics_vec256 k_e_t = Lib_IntVector_Intrinsics_vec256_load32(k_t);
      Lib_IntVector_Intrinsics_vec256
      t1 =
        Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(h02,
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(e0,
                    (uint32_t)6U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(e0,
                      (uint32_t)11U),
                    Lib_IntVector_Intrinsics_vec256_rotate_right32(e0, (uint32_t)25U)))),
              Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(e0, f0),
                Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_lognot(e0), g0))),
            k_e_t),
          ws_t);
      Lib_IntVector_Intrinsics_vec256
      t2 =
        Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(a0,
              (uint32_t)2U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(a0,
                (uint32_t)13U),
              Lib_IntVector_Intrinsics_vec256_rotate_right32(a0, (uint32_t)22U))),
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, b0),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, c0),
              Lib_IntVector_Intrinsics_vec256_and(b0, c0))));
      Lib_IntVector_Intrinsics_vec256 a1 = Lib_IntVector_Intrinsics_vec256_add32(t1, t2);
      Lib_IntVector_Intrinsics_vec256 b1 = a0;
      Lib_IntVector_Intrinsics_vec256 c1 = b0;
      Lib_IntVector_Intrinsics_vec256 d1 = c0;
      Lib_IntVector_Intrinsics_vec256 e1 = Lib_IntVector_Intrinsics_vec256_add32(d0, t1);
      Lib_IntVector_Intrinsics_vec256 f1 = e0;
      Lib_IntVector_Intrinsics_vec256 g1 = f0;
      Lib_IntVector_Intrinsics_vec256 h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)4U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        Lib_IntVector_Intrinsics_vec256 t16 = ws[i];
        Lib_IntVector_Intrinsics_vec256 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256
        s1 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t2,
              (uint32_t)17U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t2,
                (uint32_t)19U),
              Lib_IntVector_Intrinsics_vec256_shift_right32(t2, (uint32_t)10U)));
        Lib_IntVector_Intrinsics_vec256
        s0 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t15,
              (uint32_t)7U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t15,
                (uint32_t)18U),
              Lib_IntVector_Intrinsics_vec256_shift_right32(t15, (uint32_t)3U)));
        ws[i] =
          Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(s1,
                t7),
              s0),
            t16);
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = hash;
    Lib_IntVector_Intrinsics_vec256
    x = Lib_IntVector_Intrinsics_vec256_add32(hash[i], hash_old[i]);
    os[i] = x;
  }
}

void
Hacl_SHA2_Vec256_sha256_8(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint8_t *dst4,
  uint8_t *dst5,
  uint8_t *dst6,
  uint8_t *dst7,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *input4,
  uint8_t *input5,
  uint8_t *input6,
  uint8_t *input7
)
{
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  ib =
    {
      .fst = input0,
      .snd = {
        .fst = input1,
        .snd = {
          .fst = input2,
          .snd = {
            .fst = input3,
            .snd = {
              .fst = input4,
              .snd = { .fst = input5, .snd = { .fst = input6, .snd = input7 } }
            }
          }
        }
      }
    };
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  rb =
    {
      .fst = dst0,
      .snd = {
        .fst = dst1,
        .snd = {
          .fst = dst2,
          .snd = {
            .fst = dst3,
            .snd = { .fst = dst4, .snd = { .fst = dst5, .snd = { .fst = dst6, .snd = dst7 } } }
          }
        }
      }
    };
  Lib_IntVector_Intrinsics_vec256 st[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = st;
    uint32_t hi = Hacl_Impl_SHA2_Generic_h256[i];
    Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_load32(hi);
    os[i] = x;
  }
  uint32_t rem = input_len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)input_len;
  uint32_t blocks0 = input_len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b7 = ib.snd.snd.snd.snd.snd.snd.snd;
    uint8_t *b6 = ib.snd.snd.snd.snd.snd.snd.fst;
    uint8_t *b5 = ib.snd.snd.snd.snd.snd.fst;
    uint8_t *b4 = ib.snd.snd.snd.snd.fst;
    uint8_t *b3 = ib.snd.snd.snd.fst;
    uint8_t *b2 = ib.snd.snd.fst;
    uint8_t *b1 = ib.snd.fst;
    uint8_t *b0 = ib.fst;
    uint8_t *bl0 = b0 + i * (uint32_t)64U;
    uint8_t *bl1 = b1 + i * (uint32_t)64U;
    uint8_t *bl2 = b2 + i * (uint32_t)64U;
    uint8_t *bl3 = b3 + i * (uint32_t)64U;
    uint8_t *bl4 = b4 + i * (uint32_t)64U;
    uint8_t *bl5 = b5 + i * (uint32_t)64U;
    uint8_t *bl6 = b6 + i * (uint32_t)64U;
    uint8_t *bl7 = b7 + i * (uint32_t)64U;
    ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
    mb =
      {
        .fst = bl0,
        .snd = {
          .fst = bl1,
          .snd = {
            .fst = bl2,
            .snd = {
              .fst = bl3,
              .snd = { .fst = bl4, .snd = { .fst = bl5, .snd = { .fst = bl6, .snd = bl7 } } }
            }
          }
        }
      };
    sha256_update8(mb, st);
  }
  uint32_t rem1 = input_len % (uint32_t)64U;
  uint8_t *b7 = ib.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b60 = ib.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b50 = ib.snd.snd.snd.snd.snd.fst;
  uint8_t *b40 = ib.snd.snd.snd.snd.fst;
  uint8_t *b30 = ib.snd.snd.snd.fst;
  uint8_t *b20 = ib.snd.snd.fst;
  uint8_t *b10 = ib.snd.fst;
  uint8_t *b00 = ib.fst;
  uint8_t *bl0 = b00 + input_len - rem1;
  uint8_t *bl1 = b10 + input_len - rem1;
  uint8_t *bl2 = b20 + input_len - rem1;
  uint8_t *bl3 = b30 + input_len - rem1;
  uint8_t *bl4 = b40 + input_len - rem1;
  uint8_t *bl5 = b50 + input_len - rem1;
  uint8_t *bl6 = b60 + input_len - rem1;
  uint8_t *bl7 = b7 + input_len - rem1;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  lb =
    {
      .fst = bl0,
      .snd = {
        .fst = bl1,
        .snd = {
          .fst = bl2,
          .snd = {
            .fst = bl3,
            .snd = { .fst = bl4, .snd = { .fst = bl5, .snd = { .fst = bl6, .snd = bl7 } } }
          }
        }
      }
    };
  uint32_t blocks;
  if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)64U;
  uint8_t last[1024U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = len_ << (uint32_t)3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b70 = lb.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b61 = lb.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b51 = lb.snd.snd.snd.snd.snd.fst;
  uint8_t *b41 = lb.snd.snd.snd.snd.fst;
  uint8_t *b31 = lb.snd.snd.snd.fst;
  uint8_t *b21 = lb.snd.snd.fst;
  uint8_t *b11 = lb.snd.fst;
  uint8_t *b01 = lb.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)128U;
  uint8_t *last2 = last + (uint32_t)256U;
  uint8_t *last3 = last + (uint32_t)384U;
  uint8_t *last4 = last + (uint32_t)512U;
  uint8_t *last5 = last + (uint32_t)640U;
  uint8_t *last6 = last + (uint32_t)768U;
  uint8_t *last7 = last + (uint32_t)896U;
  memcpy(last00, b01, rem * sizeof (uint8_t));
  last00[rem] = (uint8_t)0x80U;
  memcpy(last00 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut = { .fst = last010, .snd = last110 };
  uint8_t *l00 = scrut.fst;
  uint8_t *l01 = scrut.snd;
  memcpy(last10, b11, rem * sizeof (uint8_t));
  last10[rem] = (uint8_t)0x80U;
  memcpy(last10 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut0 = { .fst = last011, .snd = last111 };
  uint8_t *l10 = scrut0.fst;
  uint8_t *l11 = scrut0.snd;
  memcpy(last2, b21, rem * sizeof (uint8_t));
  last2[rem] = (uint8_t)0x80U;
  memcpy(last2 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut1 = { .fst = last012, .snd = last112 };
  uint8_t *l20 = scrut1.fst;
  uint8_t *l21 = scrut1.snd;
  memcpy(last3, b31, rem * sizeof (uint8_t));
  last3[rem] = (uint8_t)0x80U;
  memcpy(last3 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last013 = last3;
  uint8_t *last113 = last3 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut2 = { .fst = last013, .snd = last113 };
  uint8_t *l30 = scrut2.fst;
  uint8_t *l31 = scrut2.snd;
  memcpy(last4, b41, rem * sizeof (uint8_t));
  last4[rem] = (uint8_t)0x80U;
  memcpy(last4 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last014 = last4;
  uint8_t *last114 = last4 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut3 = { .fst = last014, .snd = last114 };
  uint8_t *l40 = scrut3.fst;
  uint8_t *l41 = scrut3.snd;
  memcpy(last5, b51, rem * sizeof (uint8_t));
  last5[rem] = (uint8_t)0x80U;
  memcpy(last5 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last015 = last5;
  uint8_t *last115 = last5 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut4 = { .fst = last015, .snd = last115 };
  uint8_t *l50 = scrut4.fst;
  uint8_t *l51 = scrut4.snd;
  memcpy(last6, b61, rem * sizeof (uint8_t));
  last6[rem] = (uint8_t)0x80U;
  memcpy(last6 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last016 = last6;
  uint8_t *last116 = last6 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut5 = { .fst = last016, .snd = last116 };
  uint8_t *l60 = scrut5.fst;
  uint8_t *l61 = scrut5.snd;
  memcpy(last7, b70, rem * sizeof (uint8_t));
  last7[rem] = (uint8_t)0x80U;
  memcpy(last7 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last01 = last7;
  uint8_t *last11 = last7 + (uint32_t)64U;
  K____uint8_t___uint8_t_ scrut6 = { .fst = last01, .snd = last11 };
  uint8_t *l70 = scrut6.fst;
  uint8_t *l71 = scrut6.snd;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb0 =
    {
      .fst = l00,
      .snd = {
        .fst = l10,
        .snd = {
          .fst = l20,
          .snd = {
            .fst = l30,
            .snd = { .fst = l40, .snd = { .fst = l50, .snd = { .fst = l60, .snd = l70 } } }
          }
        }
      }
    };
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb1 =
    {
      .fst = l01,
      .snd = {
        .fst = l11,
        .snd = {
          .fst = l21,
          .snd = {
            .fst = l31,
            .snd = { .fst = l41, .snd = { .fst = l51, .snd = { .fst = l61, .snd = l71 } } }
          }
        }
      }
    };
  __K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  scrut7 = { .fst = mb0, .snd = mb1 };
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  last0 = scrut7.fst;
  ___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  last1 = scrut7.snd;
  sha256_update8(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha256_update8(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)8U * (uint32_t)8U * (uint32_t)4U);
  uint8_t hbuf[(uint32_t)8U * (uint32_t)8U * (uint32_t)4U];
  memset(hbuf, 0U, (uint32_t)8U * (uint32_t)8U * (uint32_t)4U * sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256 v0 = st[0U];
  Lib_IntVector_Intrinsics_vec256 v1 = st[1U];
  Lib_IntVector_Intrinsics_vec256 v2 = st[2U];
  Lib_IntVector_Intrinsics_vec256 v3 = st[3U];
  Lib_IntVector_Intrinsics_vec256 v4 = st[4U];
  Lib_IntVector_Intrinsics_vec256 v5 = st[5U];
  Lib_IntVector_Intrinsics_vec256 v6 = st[6U];
  Lib_IntVector_Intrinsics_vec256 v7 = st[7U];
  Lib_IntVector_Intrinsics_vec256 v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v0, v1);
  Lib_IntVector_Intrinsics_vec256 v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v2, v3);
  Lib_IntVector_Intrinsics_vec256 v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v4, v5);
  Lib_IntVector_Intrinsics_vec256
  v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v4, v5);
  Lib_IntVector_Intrinsics_vec256 v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v6, v7);
  Lib_IntVector_Intrinsics_vec256
  v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v6, v7);
  Lib_IntVector_Intrinsics_vec256 v0_0 = v0_;
  Lib_IntVector_Intrinsics_vec256 v1_0 = v1_;
  Lib_IntVector_Intrinsics_vec256 v2_0 = v2_;
  Lib_IntVector_Intrinsics_vec256 v3_0 = v3_;
  Lib_IntVector_Intrinsics_vec256 v4_0 = v4_;
  Lib_IntVector_Intrinsics_vec256 v5_0 = v5_;
  Lib_IntVector_Intrinsics_vec256 v6_0 = v6_;
  Lib_IntVector_Intrinsics_vec256 v7_0 = v7_;
  Lib_IntVector_Intrinsics_vec256
  v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v4_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v6_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
  Lib_IntVector_Intrinsics_vec256
  v5_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256
  v7_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
  Lib_IntVector_Intrinsics_vec256 v0_10 = v0_1;
  Lib_IntVector_Intrinsics_vec256 v1_10 = v1_1;
  Lib_IntVector_Intrinsics_vec256 v2_10 = v2_1;
  Lib_IntVector_Intrinsics_vec256 v3_10 = v3_1;
  Lib_IntVector_Intrinsics_vec256 v4_10 = v4_1;
  Lib_IntVector_Intrinsics_vec256 v5_10 = v5_1;
  Lib_IntVector_Intrinsics_vec256 v6_10 = v6_1;
  Lib_IntVector_Intrinsics_vec256 v7_10 = v7_1;
  Lib_IntVector_Intrinsics_vec256
  v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v4_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_10, v4_10);
  Lib_IntVector_Intrinsics_vec256
  v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v5_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_10, v5_10);
  Lib_IntVector_Intrinsics_vec256
  v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v6_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_10, v6_10);
  Lib_IntVector_Intrinsics_vec256
  v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256
  v7_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_10, v7_10);
  Lib_IntVector_Intrinsics_vec256 v0_20 = v0_2;
  Lib_IntVector_Intrinsics_vec256 v1_20 = v1_2;
  Lib_IntVector_Intrinsics_vec256 v2_20 = v2_2;
  Lib_IntVector_Intrinsics_vec256 v3_20 = v3_2;
  Lib_IntVector_Intrinsics_vec256 v4_20 = v4_2;
  Lib_IntVector_Intrinsics_vec256 v5_20 = v5_2;
  Lib_IntVector_Intrinsics_vec256 v6_20 = v6_2;
  Lib_IntVector_Intrinsics_vec256 v7_20 = v7_2;
  Lib_IntVector_Intrinsics_vec256 v0_3 = v0_20;
  Lib_IntVector_Intrinsics_vec256 v1_3 = v1_20;
  Lib_IntVector_Intrinsics_vec256 v2_3 = v2_20;
  Lib_IntVector_Intrinsics_vec256 v3_3 = v3_20;
  Lib_IntVector_Intrinsics_vec256 v4_3 = v4_20;
  Lib_IntVector_Intrinsics_vec256 v5_3 = v5_20;
  Lib_IntVector_Intrinsics_vec256 v6_3 = v6_20;
  Lib_IntVector_Intrinsics_vec256 v7_3 = v7_20;
  Lib_IntVector_Intrinsics_vec256 st0_ = v0_3;
  Lib_IntVector_Intrinsics_vec256 st1_ = v2_3;
  Lib_IntVector_Intrinsics_vec256 st2_ = v1_3;
  Lib_IntVector_Intrinsics_vec256 st3_ = v3_3;
  Lib_IntVector_Intrinsics_vec256 st4_ = v4_3;
  Lib_IntVector_Intrinsics_vec256 st5_ = v6_3;
  Lib_IntVector_Intrinsics_vec256 st6_ = v5_3;
  Lib_IntVector_Intrinsics_vec256 st7_ = v7_3;
  st[0U] = st0_;
  st[1U] = st1_;
  st[2U] = st2_;
  st[3U] = st3_;
  st[4U] = st4_;
  st[5U] = st5_;
  st[6U] = st6_;
  st[7U] = st7_;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256_store32_be(hbuf + i * (uint32_t)32U, st[i]);
  }
  uint8_t *b71 = rb.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b6 = rb.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b5 = rb.snd.snd.snd.snd.snd.fst;
  uint8_t *b4 = rb.snd.snd.snd.snd.fst;
  uint8_t *b3 = rb.snd.snd.snd.fst;
  uint8_t *b2 = rb.snd.snd.fst;
  uint8_t *b1 = rb.snd.fst;
  uint8_t *b0 = rb.fst;
  memcpy(b0, hbuf, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b1, hbuf + (uint32_t)32U, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b2, hbuf + (uint32_t)64U, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b3, hbuf + (uint32_t)96U, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b4, hbuf + (uint32_t)128U, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b5, hbuf + (uint32_t)160U, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b6, hbuf + (uint32_t)192U, (uint32_t)32U * sizeof (uint8_t));
  memcpy(b71, hbuf + (uint32_t)224U, (uint32_t)32U * sizeof (uint8_t));
}

static inline void
sha384_update4(
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ block,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  Lib_IntVector_Intrinsics_vec256 hash_old[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    hash_old[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  Lib_IntVector_Intrinsics_vec256 ws[16U];
  for (uint32_t _i = 0U; _i < (uint32_t)16U; ++_i)
    ws[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (Lib_IntVector_Intrinsics_vec256));
  uint8_t *b3 = block.snd.snd.snd;
  uint8_t *b2 = block.snd.snd.fst;
  uint8_t *b10 = block.snd.fst;
  uint8_t *b00 = block.fst;
  ws[0U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00);
  ws[1U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10);
  ws[2U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2);
  ws[3U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3);
  ws[4U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (uint32_t)32U);
  ws[5U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (uint32_t)32U);
  ws[6U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (uint32_t)32U);
  ws[7U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (uint32_t)32U);
  ws[8U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (uint32_t)64U);
  ws[9U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (uint32_t)64U);
  ws[10U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (uint32_t)64U);
  ws[11U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (uint32_t)64U);
  ws[12U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (uint32_t)96U);
  ws[13U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (uint32_t)96U);
  ws[14U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (uint32_t)96U);
  ws[15U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (uint32_t)96U);
  Lib_IntVector_Intrinsics_vec256 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec256 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec256 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec256 v30 = ws[3U];
  Lib_IntVector_Intrinsics_vec256
  v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256
  v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256 ws0 = v0__;
  Lib_IntVector_Intrinsics_vec256 ws1 = v2__;
  Lib_IntVector_Intrinsics_vec256 ws2 = v1__;
  Lib_IntVector_Intrinsics_vec256 ws3 = v3__;
  Lib_IntVector_Intrinsics_vec256 v01 = ws[4U];
  Lib_IntVector_Intrinsics_vec256 v11 = ws[5U];
  Lib_IntVector_Intrinsics_vec256 v21 = ws[6U];
  Lib_IntVector_Intrinsics_vec256 v31 = ws[7U];
  Lib_IntVector_Intrinsics_vec256
  v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v01, v11);
  Lib_IntVector_Intrinsics_vec256
  v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v01, v11);
  Lib_IntVector_Intrinsics_vec256
  v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v21, v31);
  Lib_IntVector_Intrinsics_vec256
  v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v21, v31);
  Lib_IntVector_Intrinsics_vec256
  v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256 ws4 = v0__0;
  Lib_IntVector_Intrinsics_vec256 ws5 = v2__0;
  Lib_IntVector_Intrinsics_vec256 ws6 = v1__0;
  Lib_IntVector_Intrinsics_vec256 ws7 = v3__0;
  Lib_IntVector_Intrinsics_vec256 v02 = ws[8U];
  Lib_IntVector_Intrinsics_vec256 v12 = ws[9U];
  Lib_IntVector_Intrinsics_vec256 v22 = ws[10U];
  Lib_IntVector_Intrinsics_vec256 v32 = ws[11U];
  Lib_IntVector_Intrinsics_vec256
  v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v02, v12);
  Lib_IntVector_Intrinsics_vec256
  v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v02, v12);
  Lib_IntVector_Intrinsics_vec256
  v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v22, v32);
  Lib_IntVector_Intrinsics_vec256
  v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v22, v32);
  Lib_IntVector_Intrinsics_vec256
  v0__1 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec256
  v1__1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec256
  v2__1 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec256
  v3__1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec256 ws8 = v0__1;
  Lib_IntVector_Intrinsics_vec256 ws9 = v2__1;
  Lib_IntVector_Intrinsics_vec256 ws10 = v1__1;
  Lib_IntVector_Intrinsics_vec256 ws11 = v3__1;
  Lib_IntVector_Intrinsics_vec256 v0 = ws[12U];
  Lib_IntVector_Intrinsics_vec256 v1 = ws[13U];
  Lib_IntVector_Intrinsics_vec256 v2 = ws[14U];
  Lib_IntVector_Intrinsics_vec256 v3 = ws[15U];
  Lib_IntVector_Intrinsics_vec256
  v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v0__2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec256
  v1__2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec256
  v2__2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec256
  v3__2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec256 ws12 = v0__2;
  Lib_IntVector_Intrinsics_vec256 ws13 = v2__2;
  Lib_IntVector_Intrinsics_vec256 ws14 = v1__2;
  Lib_IntVector_Intrinsics_vec256 ws15 = v3__2;
  ws[0U] = ws0;
  ws[1U] = ws1;
  ws[2U] = ws2;
  ws[3U] = ws3;
  ws[4U] = ws4;
  ws[5U] = ws5;
  ws[6U] = ws6;
  ws[7U] = ws7;
  ws[8U] = ws8;
  ws[9U] = ws9;
  ws[10U] = ws10;
  ws[11U] = ws11;
  ws[12U] = ws12;
  ws[13U] = ws13;
  ws[14U] = ws14;
  ws[15U] = ws15;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[(uint32_t)16U * i0 + i];
      Lib_IntVector_Intrinsics_vec256 ws_t = ws[i];
      Lib_IntVector_Intrinsics_vec256 a0 = hash[0U];
      Lib_IntVector_Intrinsics_vec256 b0 = hash[1U];
      Lib_IntVector_Intrinsics_vec256 c0 = hash[2U];
      Lib_IntVector_Intrinsics_vec256 d0 = hash[3U];
      Lib_IntVector_Intrinsics_vec256 e0 = hash[4U];
      Lib_IntVector_Intrinsics_vec256 f0 = hash[5U];
      Lib_IntVector_Intrinsics_vec256 g0 = hash[6U];
      Lib_IntVector_Intrinsics_vec256 h02 = hash[7U];
      Lib_IntVector_Intrinsics_vec256 k_e_t = Lib_IntVector_Intrinsics_vec256_load64(k_t);
      Lib_IntVector_Intrinsics_vec256
      t1 =
        Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(h02,
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(e0,
                    (uint32_t)14U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(e0,
                      (uint32_t)18U),
                    Lib_IntVector_Intrinsics_vec256_rotate_right64(e0, (uint32_t)41U)))),
              Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(e0, f0),
                Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_lognot(e0), g0))),
            k_e_t),
          ws_t);
      Lib_IntVector_Intrinsics_vec256
      t2 =
        Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(a0,
              (uint32_t)28U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(a0,
                (uint32_t)34U),
              Lib_IntVector_Intrinsics_vec256_rotate_right64(a0, (uint32_t)39U))),
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, b0),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, c0),
              Lib_IntVector_Intrinsics_vec256_and(b0, c0))));
      Lib_IntVector_Intrinsics_vec256 a1 = Lib_IntVector_Intrinsics_vec256_add64(t1, t2);
      Lib_IntVector_Intrinsics_vec256 b1 = a0;
      Lib_IntVector_Intrinsics_vec256 c1 = b0;
      Lib_IntVector_Intrinsics_vec256 d1 = c0;
      Lib_IntVector_Intrinsics_vec256 e1 = Lib_IntVector_Intrinsics_vec256_add64(d0, t1);
      Lib_IntVector_Intrinsics_vec256 f1 = e0;
      Lib_IntVector_Intrinsics_vec256 g1 = f0;
      Lib_IntVector_Intrinsics_vec256 h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)5U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        Lib_IntVector_Intrinsics_vec256 t16 = ws[i];
        Lib_IntVector_Intrinsics_vec256 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256
        s1 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t2,
              (uint32_t)19U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t2,
                (uint32_t)61U),
              Lib_IntVector_Intrinsics_vec256_shift_right64(t2, (uint32_t)6U)));
        Lib_IntVector_Intrinsics_vec256
        s0 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t15,
              (uint32_t)1U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t15,
                (uint32_t)8U),
              Lib_IntVector_Intrinsics_vec256_shift_right64(t15, (uint32_t)7U)));
        ws[i] =
          Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(s1,
                t7),
              s0),
            t16);
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = hash;
    Lib_IntVector_Intrinsics_vec256
    x = Lib_IntVector_Intrinsics_vec256_add64(hash[i], hash_old[i]);
    os[i] = x;
  }
}

void
Hacl_SHA2_Vec256_sha384_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
)
{
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  ib = { .fst = input0, .snd = { .fst = input1, .snd = { .fst = input2, .snd = input3 } } };
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  rb = { .fst = dst0, .snd = { .fst = dst1, .snd = { .fst = dst2, .snd = dst3 } } };
  Lib_IntVector_Intrinsics_vec256 st[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = st;
    uint64_t hi = Hacl_Impl_SHA2_Generic_h384[i];
    Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_load64(hi);
    os[i] = x;
  }
  uint32_t rem = input_len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  uint32_t blocks0 = input_len / (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b3 = ib.snd.snd.snd;
    uint8_t *b2 = ib.snd.snd.fst;
    uint8_t *b1 = ib.snd.fst;
    uint8_t *b0 = ib.fst;
    uint8_t *bl0 = b0 + i * (uint32_t)128U;
    uint8_t *bl1 = b1 + i * (uint32_t)128U;
    uint8_t *bl2 = b2 + i * (uint32_t)128U;
    uint8_t *bl3 = b3 + i * (uint32_t)128U;
    K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
    mb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
    sha384_update4(mb, st);
  }
  uint32_t rem1 = input_len % (uint32_t)128U;
  uint8_t *b3 = ib.snd.snd.snd;
  uint8_t *b20 = ib.snd.snd.fst;
  uint8_t *b10 = ib.snd.fst;
  uint8_t *b00 = ib.fst;
  uint8_t *bl0 = b00 + input_len - rem1;
  uint8_t *bl1 = b10 + input_len - rem1;
  uint8_t *bl2 = b20 + input_len - rem1;
  uint8_t *bl3 = b3 + input_len - rem1;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  lb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
  uint32_t blocks;
  if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)128U;
  uint8_t last[1024U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(len_, (uint32_t)3U);
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b30 = lb.snd.snd.snd;
  uint8_t *b21 = lb.snd.snd.fst;
  uint8_t *b11 = lb.snd.fst;
  uint8_t *b01 = lb.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)256U;
  uint8_t *last2 = last + (uint32_t)512U;
  uint8_t *last3 = last + (uint32_t)768U;
  memcpy(last00, b01, rem * sizeof (uint8_t));
  last00[rem] = (uint8_t)0x80U;
  memcpy(last00 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut = { .fst = last010, .snd = last110 };
  uint8_t *l00 = scrut.fst;
  uint8_t *l01 = scrut.snd;
  memcpy(last10, b11, rem * sizeof (uint8_t));
  last10[rem] = (uint8_t)0x80U;
  memcpy(last10 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut0 = { .fst = last011, .snd = last111 };
  uint8_t *l10 = scrut0.fst;
  uint8_t *l11 = scrut0.snd;
  memcpy(last2, b21, rem * sizeof (uint8_t));
  last2[rem] = (uint8_t)0x80U;
  memcpy(last2 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut1 = { .fst = last012, .snd = last112 };
  uint8_t *l20 = scrut1.fst;
  uint8_t *l21 = scrut1.snd;
  memcpy(last3, b30, rem * sizeof (uint8_t));
  last3[rem] = (uint8_t)0x80U;
  memcpy(last3 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last01 = last3;
  uint8_t *last11 = last3 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut2 = { .fst = last01, .snd = last11 };
  uint8_t *l30 = scrut2.fst;
  uint8_t *l31 = scrut2.snd;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb0 = { .fst = l00, .snd = { .fst = l10, .snd = { .fst = l20, .snd = l30 } } };
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb1 = { .fst = l01, .snd = { .fst = l11, .snd = { .fst = l21, .snd = l31 } } };
  K___K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  scrut3 = { .fst = mb0, .snd = mb1 };
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last0 = scrut3.fst;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last1 = scrut3.snd;
  sha384_update4(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha384_update4(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)4U * (uint32_t)8U * (uint32_t)8U);
  uint8_t hbuf[(uint32_t)4U * (uint32_t)8U * (uint32_t)8U];
  memset(hbuf, 0U, (uint32_t)4U * (uint32_t)8U * (uint32_t)8U * sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256 v00 = st[0U];
  Lib_IntVector_Intrinsics_vec256 v10 = st[1U];
  Lib_IntVector_Intrinsics_vec256 v20 = st[2U];
  Lib_IntVector_Intrinsics_vec256 v30 = st[3U];
  Lib_IntVector_Intrinsics_vec256
  v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256
  v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256 st0_ = v0__;
  Lib_IntVector_Intrinsics_vec256 st1_ = v2__;
  Lib_IntVector_Intrinsics_vec256 st2_ = v1__;
  Lib_IntVector_Intrinsics_vec256 st3_ = v3__;
  Lib_IntVector_Intrinsics_vec256 v0 = st[4U];
  Lib_IntVector_Intrinsics_vec256 v1 = st[5U];
  Lib_IntVector_Intrinsics_vec256 v2 = st[6U];
  Lib_IntVector_Intrinsics_vec256 v3 = st[7U];
  Lib_IntVector_Intrinsics_vec256
  v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256 st4_ = v0__0;
  Lib_IntVector_Intrinsics_vec256 st5_ = v2__0;
  Lib_IntVector_Intrinsics_vec256 st6_ = v1__0;
  Lib_IntVector_Intrinsics_vec256 st7_ = v3__0;
  st[0U] = st0_;
  st[1U] = st4_;
  st[2U] = st1_;
  st[3U] = st5_;
  st[4U] = st2_;
  st[5U] = st6_;
  st[6U] = st3_;
  st[7U] = st7_;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256_store64_be(hbuf + i * (uint32_t)32U, st[i]);
  }
  uint8_t *b31 = rb.snd.snd.snd;
  uint8_t *b2 = rb.snd.snd.fst;
  uint8_t *b1 = rb.snd.fst;
  uint8_t *b0 = rb.fst;
  memcpy(b0, hbuf, (uint32_t)48U * sizeof (uint8_t));
  memcpy(b1, hbuf + (uint32_t)64U, (uint32_t)48U * sizeof (uint8_t));
  memcpy(b2, hbuf + (uint32_t)128U, (uint32_t)48U * sizeof (uint8_t));
  memcpy(b31, hbuf + (uint32_t)192U, (uint32_t)48U * sizeof (uint8_t));
}

static inline void
sha512_update4(
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ block,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  Lib_IntVector_Intrinsics_vec256 hash_old[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    hash_old[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  Lib_IntVector_Intrinsics_vec256 ws[16U];
  for (uint32_t _i = 0U; _i < (uint32_t)16U; ++_i)
    ws[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (Lib_IntVector_Intrinsics_vec256));
  uint8_t *b3 = block.snd.snd.snd;
  uint8_t *b2 = block.snd.snd.fst;
  uint8_t *b10 = block.snd.fst;
  uint8_t *b00 = block.fst;
  ws[0U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00);
  ws[1U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10);
  ws[2U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2);
  ws[3U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3);
  ws[4U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (uint32_t)32U);
  ws[5U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (uint32_t)32U);
  ws[6U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (uint32_t)32U);
  ws[7U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (uint32_t)32U);
  ws[8U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (uint32_t)64U);
  ws[9U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (uint32_t)64U);
  ws[10U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (uint32_t)64U);
  ws[11U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (uint32_t)64U);
  ws[12U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (uint32_t)96U);
  ws[13U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (uint32_t)96U);
  ws[14U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (uint32_t)96U);
  ws[15U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (uint32_t)96U);
  Lib_IntVector_Intrinsics_vec256 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec256 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec256 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec256 v30 = ws[3U];
  Lib_IntVector_Intrinsics_vec256
  v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256
  v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256 ws0 = v0__;
  Lib_IntVector_Intrinsics_vec256 ws1 = v2__;
  Lib_IntVector_Intrinsics_vec256 ws2 = v1__;
  Lib_IntVector_Intrinsics_vec256 ws3 = v3__;
  Lib_IntVector_Intrinsics_vec256 v01 = ws[4U];
  Lib_IntVector_Intrinsics_vec256 v11 = ws[5U];
  Lib_IntVector_Intrinsics_vec256 v21 = ws[6U];
  Lib_IntVector_Intrinsics_vec256 v31 = ws[7U];
  Lib_IntVector_Intrinsics_vec256
  v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v01, v11);
  Lib_IntVector_Intrinsics_vec256
  v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v01, v11);
  Lib_IntVector_Intrinsics_vec256
  v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v21, v31);
  Lib_IntVector_Intrinsics_vec256
  v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v21, v31);
  Lib_IntVector_Intrinsics_vec256
  v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256 ws4 = v0__0;
  Lib_IntVector_Intrinsics_vec256 ws5 = v2__0;
  Lib_IntVector_Intrinsics_vec256 ws6 = v1__0;
  Lib_IntVector_Intrinsics_vec256 ws7 = v3__0;
  Lib_IntVector_Intrinsics_vec256 v02 = ws[8U];
  Lib_IntVector_Intrinsics_vec256 v12 = ws[9U];
  Lib_IntVector_Intrinsics_vec256 v22 = ws[10U];
  Lib_IntVector_Intrinsics_vec256 v32 = ws[11U];
  Lib_IntVector_Intrinsics_vec256
  v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v02, v12);
  Lib_IntVector_Intrinsics_vec256
  v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v02, v12);
  Lib_IntVector_Intrinsics_vec256
  v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v22, v32);
  Lib_IntVector_Intrinsics_vec256
  v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v22, v32);
  Lib_IntVector_Intrinsics_vec256
  v0__1 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec256
  v1__1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec256
  v2__1 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec256
  v3__1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec256 ws8 = v0__1;
  Lib_IntVector_Intrinsics_vec256 ws9 = v2__1;
  Lib_IntVector_Intrinsics_vec256 ws10 = v1__1;
  Lib_IntVector_Intrinsics_vec256 ws11 = v3__1;
  Lib_IntVector_Intrinsics_vec256 v0 = ws[12U];
  Lib_IntVector_Intrinsics_vec256 v1 = ws[13U];
  Lib_IntVector_Intrinsics_vec256 v2 = ws[14U];
  Lib_IntVector_Intrinsics_vec256 v3 = ws[15U];
  Lib_IntVector_Intrinsics_vec256
  v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v0__2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec256
  v1__2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec256
  v2__2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec256
  v3__2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec256 ws12 = v0__2;
  Lib_IntVector_Intrinsics_vec256 ws13 = v2__2;
  Lib_IntVector_Intrinsics_vec256 ws14 = v1__2;
  Lib_IntVector_Intrinsics_vec256 ws15 = v3__2;
  ws[0U] = ws0;
  ws[1U] = ws1;
  ws[2U] = ws2;
  ws[3U] = ws3;
  ws[4U] = ws4;
  ws[5U] = ws5;
  ws[6U] = ws6;
  ws[7U] = ws7;
  ws[8U] = ws8;
  ws[9U] = ws9;
  ws[10U] = ws10;
  ws[11U] = ws11;
  ws[12U] = ws12;
  ws[13U] = ws13;
  ws[14U] = ws14;
  ws[15U] = ws15;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[(uint32_t)16U * i0 + i];
      Lib_IntVector_Intrinsics_vec256 ws_t = ws[i];
      Lib_IntVector_Intrinsics_vec256 a0 = hash[0U];
      Lib_IntVector_Intrinsics_vec256 b0 = hash[1U];
      Lib_IntVector_Intrinsics_vec256 c0 = hash[2U];
      Lib_IntVector_Intrinsics_vec256 d0 = hash[3U];
      Lib_IntVector_Intrinsics_vec256 e0 = hash[4U];
      Lib_IntVector_Intrinsics_vec256 f0 = hash[5U];
      Lib_IntVector_Intrinsics_vec256 g0 = hash[6U];
      Lib_IntVector_Intrinsics_vec256 h02 = hash[7U];
      Lib_IntVector_Intrinsics_vec256 k_e_t = Lib_IntVector_Intrinsics_vec256_load64(k_t);
      Lib_IntVector_Intrinsics_vec256
      t1 =
        Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(h02,
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(e0,
                    (uint32_t)14U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(e0,
                      (uint32_t)18U),
                    Lib_IntVector_Intrinsics_vec256_rotate_right64(e0, (uint32_t)41U)))),
              Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(e0, f0),
                Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_lognot(e0), g0))),
            k_e_t),
          ws_t);
      Lib_IntVector_Intrinsics_vec256
      t2 =
        Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(a0,
              (uint32_t)28U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(a0,
                (uint32_t)34U),
              Lib_IntVector_Intrinsics_vec256_rotate_right64(a0, (uint32_t)39U))),
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, b0),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(a0, c0),
              Lib_IntVector_Intrinsics_vec256_and(b0, c0))));
      Lib_IntVector_Intrinsics_vec256 a1 = Lib_IntVector_Intrinsics_vec256_add64(t1, t2);
      Lib_IntVector_Intrinsics_vec256 b1 = a0;
      Lib_IntVector_Intrinsics_vec256 c1 = b0;
      Lib_IntVector_Intrinsics_vec256 d1 = c0;
      Lib_IntVector_Intrinsics_vec256 e1 = Lib_IntVector_Intrinsics_vec256_add64(d0, t1);
      Lib_IntVector_Intrinsics_vec256 f1 = e0;
      Lib_IntVector_Intrinsics_vec256 g1 = f0;
      Lib_IntVector_Intrinsics_vec256 h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)5U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        Lib_IntVector_Intrinsics_vec256 t16 = ws[i];
        Lib_IntVector_Intrinsics_vec256 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        Lib_IntVector_Intrinsics_vec256
        s1 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t2,
              (uint32_t)19U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t2,
                (uint32_t)61U),
              Lib_IntVector_Intrinsics_vec256_shift_right64(t2, (uint32_t)6U)));
        Lib_IntVector_Intrinsics_vec256
        s0 =
          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t15,
              (uint32_t)1U),
            Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t15,
                (uint32_t)8U),
              Lib_IntVector_Intrinsics_vec256_shift_right64(t15, (uint32_t)7U)));
        ws[i] =
          Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(s1,
                t7),
              s0),
            t16);
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = hash;
    Lib_IntVector_Intrinsics_vec256
    x = Lib_IntVector_Intrinsics_vec256_add64(hash[i], hash_old[i]);
    os[i] = x;
  }
}

void
Hacl_SHA2_Vec256_sha512_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
)
{
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  ib = { .fst = input0, .snd = { .fst = input1, .snd = { .fst = input2, .snd = input3 } } };
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  rb = { .fst = dst0, .snd = { .fst = dst1, .snd = { .fst = dst2, .snd = dst3 } } };
  Lib_IntVector_Intrinsics_vec256 st[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256 *os = st;
    uint64_t hi = Hacl_Impl_SHA2_Generic_h512[i];
    Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_load64(hi);
    os[i] = x;
  }
  uint32_t rem = input_len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  uint32_t blocks0 = input_len / (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b3 = ib.snd.snd.snd;
    uint8_t *b2 = ib.snd.snd.fst;
    uint8_t *b1 = ib.snd.fst;
    uint8_t *b0 = ib.fst;
    uint8_t *bl0 = b0 + i * (uint32_t)128U;
    uint8_t *bl1 = b1 + i * (uint32_t)128U;
    uint8_t *bl2 = b2 + i * (uint32_t)128U;
    uint8_t *bl3 = b3 + i * (uint32_t)128U;
    K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
    mb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
    sha512_update4(mb, st);
  }
  uint32_t rem1 = input_len % (uint32_t)128U;
  uint8_t *b3 = ib.snd.snd.snd;
  uint8_t *b20 = ib.snd.snd.fst;
  uint8_t *b10 = ib.snd.fst;
  uint8_t *b00 = ib.fst;
  uint8_t *bl0 = b00 + input_len - rem1;
  uint8_t *bl1 = b10 + input_len - rem1;
  uint8_t *bl2 = b20 + input_len - rem1;
  uint8_t *bl3 = b3 + input_len - rem1;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  lb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
  uint32_t blocks;
  if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)128U;
  uint8_t last[1024U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(len_, (uint32_t)3U);
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b30 = lb.snd.snd.snd;
  uint8_t *b21 = lb.snd.snd.fst;
  uint8_t *b11 = lb.snd.fst;
  uint8_t *b01 = lb.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)256U;
  uint8_t *last2 = last + (uint32_t)512U;
  uint8_t *last3 = last + (uint32_t)768U;
  memcpy(last00, b01, rem * sizeof (uint8_t));
  last00[rem] = (uint8_t)0x80U;
  memcpy(last00 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut = { .fst = last010, .snd = last110 };
  uint8_t *l00 = scrut.fst;
  uint8_t *l01 = scrut.snd;
  memcpy(last10, b11, rem * sizeof (uint8_t));
  last10[rem] = (uint8_t)0x80U;
  memcpy(last10 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut0 = { .fst = last011, .snd = last111 };
  uint8_t *l10 = scrut0.fst;
  uint8_t *l11 = scrut0.snd;
  memcpy(last2, b21, rem * sizeof (uint8_t));
  last2[rem] = (uint8_t)0x80U;
  memcpy(last2 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut1 = { .fst = last012, .snd = last112 };
  uint8_t *l20 = scrut1.fst;
  uint8_t *l21 = scrut1.snd;
  memcpy(last3, b30, rem * sizeof (uint8_t));
  last3[rem] = (uint8_t)0x80U;
  memcpy(last3 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last01 = last3;
  uint8_t *last11 = last3 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut2 = { .fst = last01, .snd = last11 };
  uint8_t *l30 = scrut2.fst;
  uint8_t *l31 = scrut2.snd;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb0 = { .fst = l00, .snd = { .fst = l10, .snd = { .fst = l20, .snd = l30 } } };
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  mb1 = { .fst = l01, .snd = { .fst = l11, .snd = { .fst = l21, .snd = l31 } } };
  K___K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  scrut3 = { .fst = mb0, .snd = mb1 };
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last0 = scrut3.fst;
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last1 = scrut3.snd;
  sha512_update4(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha512_update4(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)4U * (uint32_t)8U * (uint32_t)8U);
  uint8_t hbuf[(uint32_t)4U * (uint32_t)8U * (uint32_t)8U];
  memset(hbuf, 0U, (uint32_t)4U * (uint32_t)8U * (uint32_t)8U * sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256 v00 = st[0U];
  Lib_IntVector_Intrinsics_vec256 v10 = st[1U];
  Lib_IntVector_Intrinsics_vec256 v20 = st[2U];
  Lib_IntVector_Intrinsics_vec256 v30 = st[3U];
  Lib_IntVector_Intrinsics_vec256
  v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v00, v10);
  Lib_IntVector_Intrinsics_vec256
  v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v20, v30);
  Lib_IntVector_Intrinsics_vec256
  v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_, v2_);
  Lib_IntVector_Intrinsics_vec256
  v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256
  v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_, v3_);
  Lib_IntVector_Intrinsics_vec256 st0_ = v0__;
  Lib_IntVector_Intrinsics_vec256 st1_ = v2__;
  Lib_IntVector_Intrinsics_vec256 st2_ = v1__;
  Lib_IntVector_Intrinsics_vec256 st3_ = v3__;
  Lib_IntVector_Intrinsics_vec256 v0 = st[4U];
  Lib_IntVector_Intrinsics_vec256 v1 = st[5U];
  Lib_IntVector_Intrinsics_vec256 v2 = st[6U];
  Lib_IntVector_Intrinsics_vec256 v3 = st[7U];
  Lib_IntVector_Intrinsics_vec256
  v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0, v1);
  Lib_IntVector_Intrinsics_vec256
  v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v2, v3);
  Lib_IntVector_Intrinsics_vec256
  v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec256
  v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256
  v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec256 st4_ = v0__0;
  Lib_IntVector_Intrinsics_vec256 st5_ = v2__0;
  Lib_IntVector_Intrinsics_vec256 st6_ = v1__0;
  Lib_IntVector_Intrinsics_vec256 st7_ = v3__0;
  st[0U] = st0_;
  st[1U] = st4_;
  st[2U] = st1_;
  st[3U] = st5_;
  st[4U] = st2_;
  st[5U] = st6_;
  st[6U] = st3_;
  st[7U] = st7_;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec256_store64_be(hbuf + i * (uint32_t)32U, st[i]);
  }
  uint8_t *b31 = rb.snd.snd.snd;
  uint8_t *b2 = rb.snd.snd.fst;
  uint8_t *b1 = rb.snd.fst;
  uint8_t *b0 = rb.fst;
  memcpy(b0, hbuf, (uint32_t)64U * sizeof (uint8_t));
  memcpy(b1, hbuf + (uint32_t)64U, (uint32_t)64U * sizeof (uint8_t));
  memcpy(b2, hbuf + (uint32_t)128U, (uint32_t)64U * sizeof (uint8_t));
  memcpy(b31, hbuf + (uint32_t)192U, (uint32_t)64U * sizeof (uint8_t));
}

