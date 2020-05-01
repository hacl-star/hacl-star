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


#include "Hacl_SHA2_Vec256.h"

static inline void
sha256_update8(
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ b,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  Lib_IntVector_Intrinsics_vec256 hash_old[8U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)8U; ++_i)
      hash_old[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec256 ws[16U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)16U; ++_i)
        ws[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    }
    {
      u8 *b7;
      u8 *b6;
      u8 *b5;
      u8 *b4;
      u8 *b3;
      u8 *b2;
      u8 *b10;
      u8 *b00;
      Lib_IntVector_Intrinsics_vec256 v00;
      Lib_IntVector_Intrinsics_vec256 v10;
      Lib_IntVector_Intrinsics_vec256 v20;
      Lib_IntVector_Intrinsics_vec256 v30;
      Lib_IntVector_Intrinsics_vec256 v40;
      Lib_IntVector_Intrinsics_vec256 v50;
      Lib_IntVector_Intrinsics_vec256 v60;
      Lib_IntVector_Intrinsics_vec256 v70;
      Lib_IntVector_Intrinsics_vec256 v0_;
      Lib_IntVector_Intrinsics_vec256 v1_;
      Lib_IntVector_Intrinsics_vec256 v2_;
      Lib_IntVector_Intrinsics_vec256 v3_;
      Lib_IntVector_Intrinsics_vec256 v4_;
      Lib_IntVector_Intrinsics_vec256 v5_;
      Lib_IntVector_Intrinsics_vec256 v6_;
      Lib_IntVector_Intrinsics_vec256 v7_;
      Lib_IntVector_Intrinsics_vec256 v0_0;
      Lib_IntVector_Intrinsics_vec256 v1_0;
      Lib_IntVector_Intrinsics_vec256 v2_0;
      Lib_IntVector_Intrinsics_vec256 v3_0;
      Lib_IntVector_Intrinsics_vec256 v4_0;
      Lib_IntVector_Intrinsics_vec256 v5_0;
      Lib_IntVector_Intrinsics_vec256 v6_0;
      Lib_IntVector_Intrinsics_vec256 v7_0;
      Lib_IntVector_Intrinsics_vec256 v0_1;
      Lib_IntVector_Intrinsics_vec256 v2_1;
      Lib_IntVector_Intrinsics_vec256 v1_1;
      Lib_IntVector_Intrinsics_vec256 v3_1;
      Lib_IntVector_Intrinsics_vec256 v4_1;
      Lib_IntVector_Intrinsics_vec256 v6_1;
      Lib_IntVector_Intrinsics_vec256 v5_1;
      Lib_IntVector_Intrinsics_vec256 v7_1;
      Lib_IntVector_Intrinsics_vec256 v0_10;
      Lib_IntVector_Intrinsics_vec256 v1_10;
      Lib_IntVector_Intrinsics_vec256 v2_10;
      Lib_IntVector_Intrinsics_vec256 v3_10;
      Lib_IntVector_Intrinsics_vec256 v4_10;
      Lib_IntVector_Intrinsics_vec256 v5_10;
      Lib_IntVector_Intrinsics_vec256 v6_10;
      Lib_IntVector_Intrinsics_vec256 v7_10;
      Lib_IntVector_Intrinsics_vec256 v0_2;
      Lib_IntVector_Intrinsics_vec256 v4_2;
      Lib_IntVector_Intrinsics_vec256 v1_2;
      Lib_IntVector_Intrinsics_vec256 v5_2;
      Lib_IntVector_Intrinsics_vec256 v2_2;
      Lib_IntVector_Intrinsics_vec256 v6_2;
      Lib_IntVector_Intrinsics_vec256 v3_2;
      Lib_IntVector_Intrinsics_vec256 v7_2;
      Lib_IntVector_Intrinsics_vec256 v0_20;
      Lib_IntVector_Intrinsics_vec256 v1_20;
      Lib_IntVector_Intrinsics_vec256 v2_20;
      Lib_IntVector_Intrinsics_vec256 v3_20;
      Lib_IntVector_Intrinsics_vec256 v4_20;
      Lib_IntVector_Intrinsics_vec256 v5_20;
      Lib_IntVector_Intrinsics_vec256 v6_20;
      Lib_IntVector_Intrinsics_vec256 v7_20;
      Lib_IntVector_Intrinsics_vec256 v0_3;
      Lib_IntVector_Intrinsics_vec256 v1_3;
      Lib_IntVector_Intrinsics_vec256 v2_3;
      Lib_IntVector_Intrinsics_vec256 v3_3;
      Lib_IntVector_Intrinsics_vec256 v4_3;
      Lib_IntVector_Intrinsics_vec256 v5_3;
      Lib_IntVector_Intrinsics_vec256 v6_3;
      Lib_IntVector_Intrinsics_vec256 v7_3;
      Lib_IntVector_Intrinsics_vec256 ws0;
      Lib_IntVector_Intrinsics_vec256 ws1;
      Lib_IntVector_Intrinsics_vec256 ws2;
      Lib_IntVector_Intrinsics_vec256 ws3;
      Lib_IntVector_Intrinsics_vec256 ws4;
      Lib_IntVector_Intrinsics_vec256 ws5;
      Lib_IntVector_Intrinsics_vec256 ws6;
      Lib_IntVector_Intrinsics_vec256 ws7;
      Lib_IntVector_Intrinsics_vec256 v0;
      Lib_IntVector_Intrinsics_vec256 v1;
      Lib_IntVector_Intrinsics_vec256 v2;
      Lib_IntVector_Intrinsics_vec256 v3;
      Lib_IntVector_Intrinsics_vec256 v4;
      Lib_IntVector_Intrinsics_vec256 v5;
      Lib_IntVector_Intrinsics_vec256 v6;
      Lib_IntVector_Intrinsics_vec256 v7;
      Lib_IntVector_Intrinsics_vec256 v0_4;
      Lib_IntVector_Intrinsics_vec256 v1_4;
      Lib_IntVector_Intrinsics_vec256 v2_4;
      Lib_IntVector_Intrinsics_vec256 v3_4;
      Lib_IntVector_Intrinsics_vec256 v4_4;
      Lib_IntVector_Intrinsics_vec256 v5_4;
      Lib_IntVector_Intrinsics_vec256 v6_4;
      Lib_IntVector_Intrinsics_vec256 v7_4;
      Lib_IntVector_Intrinsics_vec256 v0_5;
      Lib_IntVector_Intrinsics_vec256 v1_5;
      Lib_IntVector_Intrinsics_vec256 v2_5;
      Lib_IntVector_Intrinsics_vec256 v3_5;
      Lib_IntVector_Intrinsics_vec256 v4_5;
      Lib_IntVector_Intrinsics_vec256 v5_5;
      Lib_IntVector_Intrinsics_vec256 v6_5;
      Lib_IntVector_Intrinsics_vec256 v7_5;
      Lib_IntVector_Intrinsics_vec256 v0_11;
      Lib_IntVector_Intrinsics_vec256 v2_11;
      Lib_IntVector_Intrinsics_vec256 v1_11;
      Lib_IntVector_Intrinsics_vec256 v3_11;
      Lib_IntVector_Intrinsics_vec256 v4_11;
      Lib_IntVector_Intrinsics_vec256 v6_11;
      Lib_IntVector_Intrinsics_vec256 v5_11;
      Lib_IntVector_Intrinsics_vec256 v7_11;
      Lib_IntVector_Intrinsics_vec256 v0_12;
      Lib_IntVector_Intrinsics_vec256 v1_12;
      Lib_IntVector_Intrinsics_vec256 v2_12;
      Lib_IntVector_Intrinsics_vec256 v3_12;
      Lib_IntVector_Intrinsics_vec256 v4_12;
      Lib_IntVector_Intrinsics_vec256 v5_12;
      Lib_IntVector_Intrinsics_vec256 v6_12;
      Lib_IntVector_Intrinsics_vec256 v7_12;
      Lib_IntVector_Intrinsics_vec256 v0_21;
      Lib_IntVector_Intrinsics_vec256 v4_21;
      Lib_IntVector_Intrinsics_vec256 v1_21;
      Lib_IntVector_Intrinsics_vec256 v5_21;
      Lib_IntVector_Intrinsics_vec256 v2_21;
      Lib_IntVector_Intrinsics_vec256 v6_21;
      Lib_IntVector_Intrinsics_vec256 v3_21;
      Lib_IntVector_Intrinsics_vec256 v7_21;
      Lib_IntVector_Intrinsics_vec256 v0_22;
      Lib_IntVector_Intrinsics_vec256 v1_22;
      Lib_IntVector_Intrinsics_vec256 v2_22;
      Lib_IntVector_Intrinsics_vec256 v3_22;
      Lib_IntVector_Intrinsics_vec256 v4_22;
      Lib_IntVector_Intrinsics_vec256 v5_22;
      Lib_IntVector_Intrinsics_vec256 v6_22;
      Lib_IntVector_Intrinsics_vec256 v7_22;
      Lib_IntVector_Intrinsics_vec256 v0_6;
      Lib_IntVector_Intrinsics_vec256 v1_6;
      Lib_IntVector_Intrinsics_vec256 v2_6;
      Lib_IntVector_Intrinsics_vec256 v3_6;
      Lib_IntVector_Intrinsics_vec256 v4_6;
      Lib_IntVector_Intrinsics_vec256 v5_6;
      Lib_IntVector_Intrinsics_vec256 v6_6;
      Lib_IntVector_Intrinsics_vec256 v7_6;
      Lib_IntVector_Intrinsics_vec256 ws8;
      Lib_IntVector_Intrinsics_vec256 ws9;
      Lib_IntVector_Intrinsics_vec256 ws10;
      Lib_IntVector_Intrinsics_vec256 ws11;
      Lib_IntVector_Intrinsics_vec256 ws12;
      Lib_IntVector_Intrinsics_vec256 ws13;
      Lib_IntVector_Intrinsics_vec256 ws14;
      Lib_IntVector_Intrinsics_vec256 ws15;
      memcpy(hash_old, hash, (u32)8U * sizeof (hash[0U]));
      b7 = b.snd.snd.snd.snd.snd.snd.snd;
      b6 = b.snd.snd.snd.snd.snd.snd.fst;
      b5 = b.snd.snd.snd.snd.snd.fst;
      b4 = b.snd.snd.snd.snd.fst;
      b3 = b.snd.snd.snd.fst;
      b2 = b.snd.snd.fst;
      b10 = b.snd.fst;
      b00 = b.fst;
      ws[0U] = Lib_IntVector_Intrinsics_vec256_load32_be(b00);
      ws[1U] = Lib_IntVector_Intrinsics_vec256_load32_be(b10);
      ws[2U] = Lib_IntVector_Intrinsics_vec256_load32_be(b2);
      ws[3U] = Lib_IntVector_Intrinsics_vec256_load32_be(b3);
      ws[4U] = Lib_IntVector_Intrinsics_vec256_load32_be(b4);
      ws[5U] = Lib_IntVector_Intrinsics_vec256_load32_be(b5);
      ws[6U] = Lib_IntVector_Intrinsics_vec256_load32_be(b6);
      ws[7U] = Lib_IntVector_Intrinsics_vec256_load32_be(b7);
      ws[8U] = Lib_IntVector_Intrinsics_vec256_load32_be(b00 + (u32)32U);
      ws[9U] = Lib_IntVector_Intrinsics_vec256_load32_be(b10 + (u32)32U);
      ws[10U] = Lib_IntVector_Intrinsics_vec256_load32_be(b2 + (u32)32U);
      ws[11U] = Lib_IntVector_Intrinsics_vec256_load32_be(b3 + (u32)32U);
      ws[12U] = Lib_IntVector_Intrinsics_vec256_load32_be(b4 + (u32)32U);
      ws[13U] = Lib_IntVector_Intrinsics_vec256_load32_be(b5 + (u32)32U);
      ws[14U] = Lib_IntVector_Intrinsics_vec256_load32_be(b6 + (u32)32U);
      ws[15U] = Lib_IntVector_Intrinsics_vec256_load32_be(b7 + (u32)32U);
      v00 = ws[0U];
      v10 = ws[1U];
      v20 = ws[2U];
      v30 = ws[3U];
      v40 = ws[4U];
      v50 = ws[5U];
      v60 = ws[6U];
      v70 = ws[7U];
      v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v00, v10);
      v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v00, v10);
      v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v20, v30);
      v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v20, v30);
      v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v40, v50);
      v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v40, v50);
      v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v60, v70);
      v7_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v60, v70);
      v0_0 = v0_;
      v1_0 = v1_;
      v2_0 = v2_;
      v3_0 = v3_;
      v4_0 = v4_;
      v5_0 = v5_;
      v6_0 = v6_;
      v7_0 = v7_;
      v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_0, v2_0);
      v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_0, v2_0);
      v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_0, v3_0);
      v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_0, v3_0);
      v4_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_0, v6_0);
      v6_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_0, v6_0);
      v5_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_0, v7_0);
      v7_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_0, v7_0);
      v0_10 = v0_1;
      v1_10 = v1_1;
      v2_10 = v2_1;
      v3_10 = v3_1;
      v4_10 = v4_1;
      v5_10 = v5_1;
      v6_10 = v6_1;
      v7_10 = v7_1;
      v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_10, v4_10);
      v4_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_10, v4_10);
      v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_10, v5_10);
      v5_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_10, v5_10);
      v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_10, v6_10);
      v6_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_10, v6_10);
      v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_10, v7_10);
      v7_2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_10, v7_10);
      v0_20 = v0_2;
      v1_20 = v1_2;
      v2_20 = v2_2;
      v3_20 = v3_2;
      v4_20 = v4_2;
      v5_20 = v5_2;
      v6_20 = v6_2;
      v7_20 = v7_2;
      v0_3 = v0_20;
      v1_3 = v1_20;
      v2_3 = v2_20;
      v3_3 = v3_20;
      v4_3 = v4_20;
      v5_3 = v5_20;
      v6_3 = v6_20;
      v7_3 = v7_20;
      ws0 = v0_3;
      ws1 = v2_3;
      ws2 = v1_3;
      ws3 = v3_3;
      ws4 = v4_3;
      ws5 = v6_3;
      ws6 = v5_3;
      ws7 = v7_3;
      v0 = ws[8U];
      v1 = ws[9U];
      v2 = ws[10U];
      v3 = ws[11U];
      v4 = ws[12U];
      v5 = ws[13U];
      v6 = ws[14U];
      v7 = ws[15U];
      v0_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v0, v1);
      v1_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v0, v1);
      v2_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v2, v3);
      v3_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v2, v3);
      v4_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v4, v5);
      v5_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v4, v5);
      v6_4 = Lib_IntVector_Intrinsics_vec256_interleave_low32(v6, v7);
      v7_4 = Lib_IntVector_Intrinsics_vec256_interleave_high32(v6, v7);
      v0_5 = v0_4;
      v1_5 = v1_4;
      v2_5 = v2_4;
      v3_5 = v3_4;
      v4_5 = v4_4;
      v5_5 = v5_4;
      v6_5 = v6_4;
      v7_5 = v7_4;
      v0_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0_5, v2_5);
      v2_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0_5, v2_5);
      v1_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v1_5, v3_5);
      v3_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v1_5, v3_5);
      v4_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v4_5, v6_5);
      v6_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v4_5, v6_5);
      v5_11 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v5_5, v7_5);
      v7_11 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v5_5, v7_5);
      v0_12 = v0_11;
      v1_12 = v1_11;
      v2_12 = v2_11;
      v3_12 = v3_11;
      v4_12 = v4_11;
      v5_12 = v5_11;
      v6_12 = v6_11;
      v7_12 = v7_11;
      v0_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_12, v4_12);
      v4_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_12, v4_12);
      v1_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_12, v5_12);
      v5_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_12, v5_12);
      v2_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v2_12, v6_12);
      v6_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v2_12, v6_12);
      v3_21 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v3_12, v7_12);
      v7_21 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v3_12, v7_12);
      v0_22 = v0_21;
      v1_22 = v1_21;
      v2_22 = v2_21;
      v3_22 = v3_21;
      v4_22 = v4_21;
      v5_22 = v5_21;
      v6_22 = v6_21;
      v7_22 = v7_21;
      v0_6 = v0_22;
      v1_6 = v1_22;
      v2_6 = v2_22;
      v3_6 = v3_22;
      v4_6 = v4_22;
      v5_6 = v5_22;
      v6_6 = v6_22;
      v7_6 = v7_22;
      ws8 = v0_6;
      ws9 = v2_6;
      ws10 = v1_6;
      ws11 = v3_6;
      ws12 = v4_6;
      ws13 = v6_6;
      ws14 = v5_6;
      ws15 = v7_6;
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
      {
        u32 i0;
        for (i0 = (u32)0U; i0 < (u32)4U; i0++)
        {
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u32 k_t = Hacl_Impl_SHA2_Generic_k224_256[(u32)16U * i0 + i];
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
                            (u32)6U),
                          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(e0,
                              (u32)11U),
                            Lib_IntVector_Intrinsics_vec256_rotate_right32(e0, (u32)25U)))),
                      Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(e0,
                          f0),
                        Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_lognot(e0),
                          g0))),
                    k_e_t),
                  ws_t);
              Lib_IntVector_Intrinsics_vec256
              t2 =
                Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(a0,
                      (u32)2U),
                    Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(a0,
                        (u32)13U),
                      Lib_IntVector_Intrinsics_vec256_rotate_right32(a0, (u32)22U))),
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
          }
          if (i0 < (u32)4U - (u32)1U)
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              Lib_IntVector_Intrinsics_vec256 t16 = ws[i];
              Lib_IntVector_Intrinsics_vec256 t15 = ws[(i + (u32)1U) % (u32)16U];
              Lib_IntVector_Intrinsics_vec256 t7 = ws[(i + (u32)9U) % (u32)16U];
              Lib_IntVector_Intrinsics_vec256 t2 = ws[(i + (u32)14U) % (u32)16U];
              Lib_IntVector_Intrinsics_vec256
              s1 =
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t2,
                    (u32)17U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t2,
                      (u32)19U),
                    Lib_IntVector_Intrinsics_vec256_shift_right32(t2, (u32)10U)));
              Lib_IntVector_Intrinsics_vec256
              s0 =
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t15,
                    (u32)7U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right32(t15,
                      (u32)18U),
                    Lib_IntVector_Intrinsics_vec256_shift_right32(t15, (u32)3U)));
              ws[i] =
                Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(Lib_IntVector_Intrinsics_vec256_add32(s1,
                      t7),
                    s0),
                  t16);
            }
          }
        }
      }
      {
        u32 i;
        for (i = (u32)0U; i < (u32)8U; i++)
        {
          Lib_IntVector_Intrinsics_vec256 *os = hash;
          Lib_IntVector_Intrinsics_vec256
          x = Lib_IntVector_Intrinsics_vec256_add32(hash[i], hash_old[i]);
          os[i] = x;
        }
      }
    }
  }
}

void
Hacl_SHA2_Vec256_sha256_8(
  u8 *r0,
  u8 *r1,
  u8 *r2,
  u8 *r3,
  u8 *r4,
  u8 *r5,
  u8 *r6,
  u8 *r7,
  u32 len,
  u8 *b0,
  u8 *b1,
  u8 *b2,
  u8 *b3,
  u8 *b4,
  u8 *b5,
  u8 *b6,
  u8 *b7
)
{
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_
  ib =
    {
      .fst = b0,
      .snd = {
        .fst = b1,
        .snd = {
          .fst = b2,
          .snd = {
            .fst = b3,
            .snd = { .fst = b4, .snd = { .fst = b5, .snd = { .fst = b6, .snd = b7 } } }
          }
        }
      }
    };
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_
  rb =
    {
      .fst = r0,
      .snd = {
        .fst = r1,
        .snd = {
          .fst = r2,
          .snd = {
            .fst = r3,
            .snd = { .fst = r4, .snd = { .fst = r5, .snd = { .fst = r6, .snd = r7 } } }
          }
        }
      }
    };
  Lib_IntVector_Intrinsics_vec256 st[8U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)8U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    u32 rem;
    u64 len_;
    u32 blocks0;
    u32 rem1;
    u8 *b710;
    u8 *b610;
    u8 *b510;
    u8 *b410;
    u8 *b310;
    u8 *b210;
    u8 *b110;
    u8 *b010;
    u8 *bl0;
    u8 *bl10;
    u8 *bl20;
    u8 *bl30;
    u8 *bl40;
    u8 *bl50;
    u8 *bl60;
    u8 *bl70;
    K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ lb;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)8U; i++)
      {
        Lib_IntVector_Intrinsics_vec256 *os = st;
        u32 hi = Hacl_Impl_SHA2_Generic_h256[i];
        Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_load32(hi);
        os[i] = x;
      }
    }
    rem = len % (u32)64U;
    len_ = (u64)len;
    blocks0 = len / (u32)64U;
    {
      u32 i;
      for (i = (u32)0U; i < blocks0; i++)
      {
        u8 *b71 = ib.snd.snd.snd.snd.snd.snd.snd;
        u8 *b61 = ib.snd.snd.snd.snd.snd.snd.fst;
        u8 *b51 = ib.snd.snd.snd.snd.snd.fst;
        u8 *b41 = ib.snd.snd.snd.snd.fst;
        u8 *b31 = ib.snd.snd.snd.fst;
        u8 *b21 = ib.snd.snd.fst;
        u8 *b11 = ib.snd.fst;
        u8 *b01 = ib.fst;
        u8 *bl00 = b01 + i * (u32)64U;
        u8 *bl1 = b11 + i * (u32)64U;
        u8 *bl2 = b21 + i * (u32)64U;
        u8 *bl3 = b31 + i * (u32)64U;
        u8 *bl4 = b41 + i * (u32)64U;
        u8 *bl5 = b51 + i * (u32)64U;
        u8 *bl6 = b61 + i * (u32)64U;
        u8 *bl7 = b71 + i * (u32)64U;
        K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_
        mb =
          {
            .fst = bl00,
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
    }
    rem1 = len % (u32)64U;
    b710 = ib.snd.snd.snd.snd.snd.snd.snd;
    b610 = ib.snd.snd.snd.snd.snd.snd.fst;
    b510 = ib.snd.snd.snd.snd.snd.fst;
    b410 = ib.snd.snd.snd.snd.fst;
    b310 = ib.snd.snd.snd.fst;
    b210 = ib.snd.snd.fst;
    b110 = ib.snd.fst;
    b010 = ib.fst;
    bl0 = b010 + len - rem1;
    bl10 = b110 + len - rem1;
    bl20 = b210 + len - rem1;
    bl30 = b310 + len - rem1;
    bl40 = b410 + len - rem1;
    bl50 = b510 + len - rem1;
    bl60 = b610 + len - rem1;
    bl70 = b710 + len - rem1;
    lb =
      (
        (K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_){
          .fst = bl0,
          .snd = {
            .fst = bl10,
            .snd = {
              .fst = bl20,
              .snd = {
                .fst = bl30,
                .snd = { .fst = bl40, .snd = { .fst = bl50, .snd = { .fst = bl60, .snd = bl70 } } }
              }
            }
          }
        }
      );
    {
      u32 blocks;
      if (rem + (u32)8U + (u32)1U <= (u32)64U)
        blocks = (u32)1U;
      else
        blocks = (u32)2U;
      {
        u32 fin = blocks * (u32)64U;
        u8 last[1024U] = { 0U };
        u8 totlen_buf[8U] = { 0U };
        u64 total_len_bits = len_ << (u32)3U;
        u8 *b711;
        u8 *b611;
        u8 *b511;
        u8 *b411;
        u8 *b311;
        u8 *b211;
        u8 *b111;
        u8 *b011;
        u8 *last00;
        u8 *last10;
        u8 *last2;
        u8 *last3;
        u8 *last4;
        u8 *last5;
        u8 *last6;
        u8 *last7;
        u8 *last010;
        u8 *last110;
        K____u8___u8_ scrut0;
        u8 *l00;
        u8 *l01;
        u8 *last011;
        u8 *last111;
        K____u8___u8_ scrut1;
        u8 *l10;
        u8 *l11;
        u8 *last012;
        u8 *last112;
        K____u8___u8_ scrut2;
        u8 *l20;
        u8 *l21;
        u8 *last013;
        u8 *last113;
        K____u8___u8_ scrut3;
        u8 *l30;
        u8 *l31;
        u8 *last014;
        u8 *last114;
        K____u8___u8_ scrut4;
        u8 *l40;
        u8 *l41;
        u8 *last015;
        u8 *last115;
        K____u8___u8_ scrut5;
        u8 *l50;
        u8 *l51;
        u8 *last016;
        u8 *last116;
        K____u8___u8_ scrut6;
        u8 *l60;
        u8 *l61;
        u8 *last01;
        u8 *last11;
        K____u8___u8_ scrut7;
        u8 *l70;
        u8 *l71;
        K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ mb0;
        K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ mb1;
        K___K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_
        scrut;
        K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ last0;
        K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ last1;
        store64_be(totlen_buf, total_len_bits);
        b711 = lb.snd.snd.snd.snd.snd.snd.snd;
        b611 = lb.snd.snd.snd.snd.snd.snd.fst;
        b511 = lb.snd.snd.snd.snd.snd.fst;
        b411 = lb.snd.snd.snd.snd.fst;
        b311 = lb.snd.snd.snd.fst;
        b211 = lb.snd.snd.fst;
        b111 = lb.snd.fst;
        b011 = lb.fst;
        last00 = last;
        last10 = last + (u32)128U;
        last2 = last + (u32)256U;
        last3 = last + (u32)384U;
        last4 = last + (u32)512U;
        last5 = last + (u32)640U;
        last6 = last + (u32)768U;
        last7 = last + (u32)896U;
        memcpy(last00, b011, rem * sizeof (b011[0U]));
        last00[rem] = (u8)0x80U;
        memcpy(last00 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last010 = last00;
        last110 = last00 + (u32)64U;
        scrut0 = ((K____u8___u8_){ .fst = last010, .snd = last110 });
        l00 = scrut0.fst;
        l01 = scrut0.snd;
        memcpy(last10, b111, rem * sizeof (b111[0U]));
        last10[rem] = (u8)0x80U;
        memcpy(last10 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last011 = last10;
        last111 = last10 + (u32)64U;
        scrut1 = ((K____u8___u8_){ .fst = last011, .snd = last111 });
        l10 = scrut1.fst;
        l11 = scrut1.snd;
        memcpy(last2, b211, rem * sizeof (b211[0U]));
        last2[rem] = (u8)0x80U;
        memcpy(last2 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last012 = last2;
        last112 = last2 + (u32)64U;
        scrut2 = ((K____u8___u8_){ .fst = last012, .snd = last112 });
        l20 = scrut2.fst;
        l21 = scrut2.snd;
        memcpy(last3, b311, rem * sizeof (b311[0U]));
        last3[rem] = (u8)0x80U;
        memcpy(last3 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last013 = last3;
        last113 = last3 + (u32)64U;
        scrut3 = ((K____u8___u8_){ .fst = last013, .snd = last113 });
        l30 = scrut3.fst;
        l31 = scrut3.snd;
        memcpy(last4, b411, rem * sizeof (b411[0U]));
        last4[rem] = (u8)0x80U;
        memcpy(last4 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last014 = last4;
        last114 = last4 + (u32)64U;
        scrut4 = ((K____u8___u8_){ .fst = last014, .snd = last114 });
        l40 = scrut4.fst;
        l41 = scrut4.snd;
        memcpy(last5, b511, rem * sizeof (b511[0U]));
        last5[rem] = (u8)0x80U;
        memcpy(last5 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last015 = last5;
        last115 = last5 + (u32)64U;
        scrut5 = ((K____u8___u8_){ .fst = last015, .snd = last115 });
        l50 = scrut5.fst;
        l51 = scrut5.snd;
        memcpy(last6, b611, rem * sizeof (b611[0U]));
        last6[rem] = (u8)0x80U;
        memcpy(last6 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last016 = last6;
        last116 = last6 + (u32)64U;
        scrut6 = ((K____u8___u8_){ .fst = last016, .snd = last116 });
        l60 = scrut6.fst;
        l61 = scrut6.snd;
        memcpy(last7, b711, rem * sizeof (b711[0U]));
        last7[rem] = (u8)0x80U;
        memcpy(last7 + fin - (u32)8U, totlen_buf, (u32)8U * sizeof (totlen_buf[0U]));
        last01 = last7;
        last11 = last7 + (u32)64U;
        scrut7 = ((K____u8___u8_){ .fst = last01, .snd = last11 });
        l70 = scrut7.fst;
        l71 = scrut7.snd;
        mb0 =
          (
            (K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_){
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
            }
          );
        mb1 =
          (
            (K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_){
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
            }
          );
        scrut =
          (
            (K___K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_){
              .fst = mb0,
              .snd = mb1
            }
          );
        last0 = scrut.fst;
        last1 = scrut.snd;
        sha256_update8(last0, st);
        if (blocks > (u32)1U)
          sha256_update8(last1, st);
        KRML_CHECK_SIZE(sizeof (u8), (u32)8U * (u32)8U * (u32)4U);
        {
          u8 hbuf[(u32)8U * (u32)8U * (u32)4U];
          memset(hbuf, 0U, (u32)8U * (u32)8U * (u32)4U * sizeof (hbuf[0U]));
          {
            Lib_IntVector_Intrinsics_vec256 v0 = st[0U];
            Lib_IntVector_Intrinsics_vec256 v1 = st[1U];
            Lib_IntVector_Intrinsics_vec256 v2 = st[2U];
            Lib_IntVector_Intrinsics_vec256 v3 = st[3U];
            Lib_IntVector_Intrinsics_vec256 v4 = st[4U];
            Lib_IntVector_Intrinsics_vec256 v5 = st[5U];
            Lib_IntVector_Intrinsics_vec256 v6 = st[6U];
            Lib_IntVector_Intrinsics_vec256 v7 = st[7U];
            Lib_IntVector_Intrinsics_vec256
            v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v0, v1);
            Lib_IntVector_Intrinsics_vec256
            v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v0, v1);
            Lib_IntVector_Intrinsics_vec256
            v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v2, v3);
            Lib_IntVector_Intrinsics_vec256
            v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v2, v3);
            Lib_IntVector_Intrinsics_vec256
            v4_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v4, v5);
            Lib_IntVector_Intrinsics_vec256
            v5_ = Lib_IntVector_Intrinsics_vec256_interleave_high32(v4, v5);
            Lib_IntVector_Intrinsics_vec256
            v6_ = Lib_IntVector_Intrinsics_vec256_interleave_low32(v6, v7);
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
            u8 *b71;
            u8 *b61;
            u8 *b51;
            u8 *b41;
            u8 *b31;
            u8 *b21;
            u8 *b11;
            u8 *b01;
            st[0U] = st0_;
            st[1U] = st1_;
            st[2U] = st2_;
            st[3U] = st3_;
            st[4U] = st4_;
            st[5U] = st5_;
            st[6U] = st6_;
            st[7U] = st7_;
            {
              u32 i;
              for (i = (u32)0U; i < (u32)8U; i++)
                Lib_IntVector_Intrinsics_vec256_store32_be(hbuf + i * (u32)32U, st[i]);
            }
            b71 = rb.snd.snd.snd.snd.snd.snd.snd;
            b61 = rb.snd.snd.snd.snd.snd.snd.fst;
            b51 = rb.snd.snd.snd.snd.snd.fst;
            b41 = rb.snd.snd.snd.snd.fst;
            b31 = rb.snd.snd.snd.fst;
            b21 = rb.snd.snd.fst;
            b11 = rb.snd.fst;
            b01 = rb.fst;
            memcpy(b01, hbuf, (u32)32U * sizeof (hbuf[0U]));
            memcpy(b11, hbuf + (u32)32U, (u32)32U * sizeof ((hbuf + (u32)32U)[0U]));
            memcpy(b21, hbuf + (u32)64U, (u32)32U * sizeof ((hbuf + (u32)64U)[0U]));
            memcpy(b31, hbuf + (u32)96U, (u32)32U * sizeof ((hbuf + (u32)96U)[0U]));
            memcpy(b41, hbuf + (u32)128U, (u32)32U * sizeof ((hbuf + (u32)128U)[0U]));
            memcpy(b51, hbuf + (u32)160U, (u32)32U * sizeof ((hbuf + (u32)160U)[0U]));
            memcpy(b61, hbuf + (u32)192U, (u32)32U * sizeof ((hbuf + (u32)192U)[0U]));
            memcpy(b71, hbuf + (u32)224U, (u32)32U * sizeof ((hbuf + (u32)224U)[0U]));
          }
        }
      }
    }
  }
}

static inline void
sha512_update4(K____u8__K____u8__K____u8___u8_ b, Lib_IntVector_Intrinsics_vec256 *hash)
{
  Lib_IntVector_Intrinsics_vec256 hash_old[8U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)8U; ++_i)
      hash_old[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec256 ws[16U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)16U; ++_i)
        ws[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    }
    {
      u8 *b3;
      u8 *b2;
      u8 *b10;
      u8 *b00;
      Lib_IntVector_Intrinsics_vec256 v00;
      Lib_IntVector_Intrinsics_vec256 v10;
      Lib_IntVector_Intrinsics_vec256 v20;
      Lib_IntVector_Intrinsics_vec256 v30;
      Lib_IntVector_Intrinsics_vec256 v0_;
      Lib_IntVector_Intrinsics_vec256 v1_;
      Lib_IntVector_Intrinsics_vec256 v2_;
      Lib_IntVector_Intrinsics_vec256 v3_;
      Lib_IntVector_Intrinsics_vec256 v0__;
      Lib_IntVector_Intrinsics_vec256 v1__;
      Lib_IntVector_Intrinsics_vec256 v2__;
      Lib_IntVector_Intrinsics_vec256 v3__;
      Lib_IntVector_Intrinsics_vec256 ws0;
      Lib_IntVector_Intrinsics_vec256 ws1;
      Lib_IntVector_Intrinsics_vec256 ws2;
      Lib_IntVector_Intrinsics_vec256 ws3;
      Lib_IntVector_Intrinsics_vec256 v01;
      Lib_IntVector_Intrinsics_vec256 v11;
      Lib_IntVector_Intrinsics_vec256 v21;
      Lib_IntVector_Intrinsics_vec256 v31;
      Lib_IntVector_Intrinsics_vec256 v0_0;
      Lib_IntVector_Intrinsics_vec256 v1_0;
      Lib_IntVector_Intrinsics_vec256 v2_0;
      Lib_IntVector_Intrinsics_vec256 v3_0;
      Lib_IntVector_Intrinsics_vec256 v0__0;
      Lib_IntVector_Intrinsics_vec256 v1__0;
      Lib_IntVector_Intrinsics_vec256 v2__0;
      Lib_IntVector_Intrinsics_vec256 v3__0;
      Lib_IntVector_Intrinsics_vec256 ws4;
      Lib_IntVector_Intrinsics_vec256 ws5;
      Lib_IntVector_Intrinsics_vec256 ws6;
      Lib_IntVector_Intrinsics_vec256 ws7;
      Lib_IntVector_Intrinsics_vec256 v02;
      Lib_IntVector_Intrinsics_vec256 v12;
      Lib_IntVector_Intrinsics_vec256 v22;
      Lib_IntVector_Intrinsics_vec256 v32;
      Lib_IntVector_Intrinsics_vec256 v0_1;
      Lib_IntVector_Intrinsics_vec256 v1_1;
      Lib_IntVector_Intrinsics_vec256 v2_1;
      Lib_IntVector_Intrinsics_vec256 v3_1;
      Lib_IntVector_Intrinsics_vec256 v0__1;
      Lib_IntVector_Intrinsics_vec256 v1__1;
      Lib_IntVector_Intrinsics_vec256 v2__1;
      Lib_IntVector_Intrinsics_vec256 v3__1;
      Lib_IntVector_Intrinsics_vec256 ws8;
      Lib_IntVector_Intrinsics_vec256 ws9;
      Lib_IntVector_Intrinsics_vec256 ws10;
      Lib_IntVector_Intrinsics_vec256 ws11;
      Lib_IntVector_Intrinsics_vec256 v0;
      Lib_IntVector_Intrinsics_vec256 v1;
      Lib_IntVector_Intrinsics_vec256 v2;
      Lib_IntVector_Intrinsics_vec256 v3;
      Lib_IntVector_Intrinsics_vec256 v0_2;
      Lib_IntVector_Intrinsics_vec256 v1_2;
      Lib_IntVector_Intrinsics_vec256 v2_2;
      Lib_IntVector_Intrinsics_vec256 v3_2;
      Lib_IntVector_Intrinsics_vec256 v0__2;
      Lib_IntVector_Intrinsics_vec256 v1__2;
      Lib_IntVector_Intrinsics_vec256 v2__2;
      Lib_IntVector_Intrinsics_vec256 v3__2;
      Lib_IntVector_Intrinsics_vec256 ws12;
      Lib_IntVector_Intrinsics_vec256 ws13;
      Lib_IntVector_Intrinsics_vec256 ws14;
      Lib_IntVector_Intrinsics_vec256 ws15;
      memcpy(hash_old, hash, (u32)8U * sizeof (hash[0U]));
      b3 = b.snd.snd.snd;
      b2 = b.snd.snd.fst;
      b10 = b.snd.fst;
      b00 = b.fst;
      ws[0U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00);
      ws[1U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10);
      ws[2U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2);
      ws[3U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3);
      ws[4U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (u32)32U);
      ws[5U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (u32)32U);
      ws[6U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (u32)32U);
      ws[7U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (u32)32U);
      ws[8U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (u32)64U);
      ws[9U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (u32)64U);
      ws[10U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (u32)64U);
      ws[11U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (u32)64U);
      ws[12U] = Lib_IntVector_Intrinsics_vec256_load64_be(b00 + (u32)96U);
      ws[13U] = Lib_IntVector_Intrinsics_vec256_load64_be(b10 + (u32)96U);
      ws[14U] = Lib_IntVector_Intrinsics_vec256_load64_be(b2 + (u32)96U);
      ws[15U] = Lib_IntVector_Intrinsics_vec256_load64_be(b3 + (u32)96U);
      v00 = ws[0U];
      v10 = ws[1U];
      v20 = ws[2U];
      v30 = ws[3U];
      v0_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v00, v10);
      v1_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v00, v10);
      v2_ = Lib_IntVector_Intrinsics_vec256_interleave_low64(v20, v30);
      v3_ = Lib_IntVector_Intrinsics_vec256_interleave_high64(v20, v30);
      v0__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_, v2_);
      v1__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_, v2_);
      v2__ = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_, v3_);
      v3__ = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_, v3_);
      ws0 = v0__;
      ws1 = v2__;
      ws2 = v1__;
      ws3 = v3__;
      v01 = ws[4U];
      v11 = ws[5U];
      v21 = ws[6U];
      v31 = ws[7U];
      v0_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v01, v11);
      v1_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v01, v11);
      v2_0 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v21, v31);
      v3_0 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v21, v31);
      v0__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_0, v2_0);
      v1__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_0, v2_0);
      v2__0 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_0, v3_0);
      v3__0 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_0, v3_0);
      ws4 = v0__0;
      ws5 = v2__0;
      ws6 = v1__0;
      ws7 = v3__0;
      v02 = ws[8U];
      v12 = ws[9U];
      v22 = ws[10U];
      v32 = ws[11U];
      v0_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v02, v12);
      v1_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v02, v12);
      v2_1 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v22, v32);
      v3_1 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v22, v32);
      v0__1 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_1, v2_1);
      v1__1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_1, v2_1);
      v2__1 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_1, v3_1);
      v3__1 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_1, v3_1);
      ws8 = v0__1;
      ws9 = v2__1;
      ws10 = v1__1;
      ws11 = v3__1;
      v0 = ws[12U];
      v1 = ws[13U];
      v2 = ws[14U];
      v3 = ws[15U];
      v0_2 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v0, v1);
      v1_2 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v0, v1);
      v2_2 = Lib_IntVector_Intrinsics_vec256_interleave_low64(v2, v3);
      v3_2 = Lib_IntVector_Intrinsics_vec256_interleave_high64(v2, v3);
      v0__2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v0_2, v2_2);
      v1__2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v0_2, v2_2);
      v2__2 = Lib_IntVector_Intrinsics_vec256_interleave_low128(v1_2, v3_2);
      v3__2 = Lib_IntVector_Intrinsics_vec256_interleave_high128(v1_2, v3_2);
      ws12 = v0__2;
      ws13 = v2__2;
      ws14 = v1__2;
      ws15 = v3__2;
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
      {
        u32 i0;
        for (i0 = (u32)0U; i0 < (u32)5U; i0++)
        {
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              u64 k_t = Hacl_Impl_SHA2_Generic_k384_512[(u32)16U * i0 + i];
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
                            (u32)14U),
                          Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(e0,
                              (u32)18U),
                            Lib_IntVector_Intrinsics_vec256_rotate_right64(e0, (u32)41U)))),
                      Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_and(e0,
                          f0),
                        Lib_IntVector_Intrinsics_vec256_and(Lib_IntVector_Intrinsics_vec256_lognot(e0),
                          g0))),
                    k_e_t),
                  ws_t);
              Lib_IntVector_Intrinsics_vec256
              t2 =
                Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(a0,
                      (u32)28U),
                    Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(a0,
                        (u32)34U),
                      Lib_IntVector_Intrinsics_vec256_rotate_right64(a0, (u32)39U))),
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
          }
          if (i0 < (u32)5U - (u32)1U)
          {
            u32 i;
            for (i = (u32)0U; i < (u32)16U; i++)
            {
              Lib_IntVector_Intrinsics_vec256 t16 = ws[i];
              Lib_IntVector_Intrinsics_vec256 t15 = ws[(i + (u32)1U) % (u32)16U];
              Lib_IntVector_Intrinsics_vec256 t7 = ws[(i + (u32)9U) % (u32)16U];
              Lib_IntVector_Intrinsics_vec256 t2 = ws[(i + (u32)14U) % (u32)16U];
              Lib_IntVector_Intrinsics_vec256
              s1 =
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t2,
                    (u32)19U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t2,
                      (u32)61U),
                    Lib_IntVector_Intrinsics_vec256_shift_right64(t2, (u32)6U)));
              Lib_IntVector_Intrinsics_vec256
              s0 =
                Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t15,
                    (u32)1U),
                  Lib_IntVector_Intrinsics_vec256_xor(Lib_IntVector_Intrinsics_vec256_rotate_right64(t15,
                      (u32)8U),
                    Lib_IntVector_Intrinsics_vec256_shift_right64(t15, (u32)7U)));
              ws[i] =
                Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(Lib_IntVector_Intrinsics_vec256_add64(s1,
                      t7),
                    s0),
                  t16);
            }
          }
        }
      }
      {
        u32 i;
        for (i = (u32)0U; i < (u32)8U; i++)
        {
          Lib_IntVector_Intrinsics_vec256 *os = hash;
          Lib_IntVector_Intrinsics_vec256
          x = Lib_IntVector_Intrinsics_vec256_add64(hash[i], hash_old[i]);
          os[i] = x;
        }
      }
    }
  }
}

void
Hacl_SHA2_Vec256_sha512_4(
  u8 *r0,
  u8 *r1,
  u8 *r2,
  u8 *r3,
  u32 len,
  u8 *b0,
  u8 *b1,
  u8 *b2,
  u8 *b3
)
{
  K____u8__K____u8__K____u8___u8_
  ib = { .fst = b0, .snd = { .fst = b1, .snd = { .fst = b2, .snd = b3 } } };
  K____u8__K____u8__K____u8___u8_
  rb = { .fst = r0, .snd = { .fst = r1, .snd = { .fst = r2, .snd = r3 } } };
  Lib_IntVector_Intrinsics_vec256 st[8U];
  {
    u32 _i;
    for (_i = 0U; _i < (u32)8U; ++_i)
      st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  }
  {
    u32 rem;
    uint128_t len_;
    u32 blocks0;
    u32 rem1;
    u8 *b310;
    u8 *b210;
    u8 *b110;
    u8 *b010;
    u8 *bl0;
    u8 *bl10;
    u8 *bl20;
    u8 *bl30;
    K____u8__K____u8__K____u8___u8_ lb;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)8U; i++)
      {
        Lib_IntVector_Intrinsics_vec256 *os = st;
        u64 hi = Hacl_Impl_SHA2_Generic_h512[i];
        Lib_IntVector_Intrinsics_vec256 x = Lib_IntVector_Intrinsics_vec256_load64(hi);
        os[i] = x;
      }
    }
    rem = len % (u32)128U;
    len_ = (uint128_t)(u64)len;
    blocks0 = len / (u32)128U;
    {
      u32 i;
      for (i = (u32)0U; i < blocks0; i++)
      {
        u8 *b31 = ib.snd.snd.snd;
        u8 *b21 = ib.snd.snd.fst;
        u8 *b11 = ib.snd.fst;
        u8 *b01 = ib.fst;
        u8 *bl00 = b01 + i * (u32)128U;
        u8 *bl1 = b11 + i * (u32)128U;
        u8 *bl2 = b21 + i * (u32)128U;
        u8 *bl3 = b31 + i * (u32)128U;
        K____u8__K____u8__K____u8___u8_
        mb = { .fst = bl00, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
        sha512_update4(mb, st);
      }
    }
    rem1 = len % (u32)128U;
    b310 = ib.snd.snd.snd;
    b210 = ib.snd.snd.fst;
    b110 = ib.snd.fst;
    b010 = ib.fst;
    bl0 = b010 + len - rem1;
    bl10 = b110 + len - rem1;
    bl20 = b210 + len - rem1;
    bl30 = b310 + len - rem1;
    lb =
      (
        (K____u8__K____u8__K____u8___u8_){
          .fst = bl0,
          .snd = { .fst = bl10, .snd = { .fst = bl20, .snd = bl30 } }
        }
      );
    {
      u32 blocks;
      if (rem + (u32)16U + (u32)1U <= (u32)128U)
        blocks = (u32)1U;
      else
        blocks = (u32)2U;
      {
        u32 fin = blocks * (u32)128U;
        u8 last[1024U] = { 0U };
        u8 totlen_buf[16U] = { 0U };
        uint128_t total_len_bits = len_ << (u32)3U;
        u8 *b311;
        u8 *b211;
        u8 *b111;
        u8 *b011;
        u8 *last00;
        u8 *last10;
        u8 *last2;
        u8 *last3;
        u8 *last010;
        u8 *last110;
        K____u8___u8_ scrut0;
        u8 *l00;
        u8 *l01;
        u8 *last011;
        u8 *last111;
        K____u8___u8_ scrut1;
        u8 *l10;
        u8 *l11;
        u8 *last012;
        u8 *last112;
        K____u8___u8_ scrut2;
        u8 *l20;
        u8 *l21;
        u8 *last01;
        u8 *last11;
        K____u8___u8_ scrut3;
        u8 *l30;
        u8 *l31;
        K____u8__K____u8__K____u8___u8_ mb0;
        K____u8__K____u8__K____u8___u8_ mb1;
        K___K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8___u8_ scrut;
        K____u8__K____u8__K____u8___u8_ last0;
        K____u8__K____u8__K____u8___u8_ last1;
        store128_be(totlen_buf, total_len_bits);
        b311 = lb.snd.snd.snd;
        b211 = lb.snd.snd.fst;
        b111 = lb.snd.fst;
        b011 = lb.fst;
        last00 = last;
        last10 = last + (u32)256U;
        last2 = last + (u32)512U;
        last3 = last + (u32)768U;
        memcpy(last00, b011, rem * sizeof (b011[0U]));
        last00[rem] = (u8)0x80U;
        memcpy(last00 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
        last010 = last00;
        last110 = last00 + (u32)128U;
        scrut0 = ((K____u8___u8_){ .fst = last010, .snd = last110 });
        l00 = scrut0.fst;
        l01 = scrut0.snd;
        memcpy(last10, b111, rem * sizeof (b111[0U]));
        last10[rem] = (u8)0x80U;
        memcpy(last10 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
        last011 = last10;
        last111 = last10 + (u32)128U;
        scrut1 = ((K____u8___u8_){ .fst = last011, .snd = last111 });
        l10 = scrut1.fst;
        l11 = scrut1.snd;
        memcpy(last2, b211, rem * sizeof (b211[0U]));
        last2[rem] = (u8)0x80U;
        memcpy(last2 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
        last012 = last2;
        last112 = last2 + (u32)128U;
        scrut2 = ((K____u8___u8_){ .fst = last012, .snd = last112 });
        l20 = scrut2.fst;
        l21 = scrut2.snd;
        memcpy(last3, b311, rem * sizeof (b311[0U]));
        last3[rem] = (u8)0x80U;
        memcpy(last3 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
        last01 = last3;
        last11 = last3 + (u32)128U;
        scrut3 = ((K____u8___u8_){ .fst = last01, .snd = last11 });
        l30 = scrut3.fst;
        l31 = scrut3.snd;
        mb0 =
          (
            (K____u8__K____u8__K____u8___u8_){
              .fst = l00,
              .snd = { .fst = l10, .snd = { .fst = l20, .snd = l30 } }
            }
          );
        mb1 =
          (
            (K____u8__K____u8__K____u8___u8_){
              .fst = l01,
              .snd = { .fst = l11, .snd = { .fst = l21, .snd = l31 } }
            }
          );
        scrut =
          (
            (K___K____u8__K____u8__K____u8___u8__K____u8__K____u8__K____u8___u8_){
              .fst = mb0,
              .snd = mb1
            }
          );
        last0 = scrut.fst;
        last1 = scrut.snd;
        sha512_update4(last0, st);
        if (blocks > (u32)1U)
          sha512_update4(last1, st);
        KRML_CHECK_SIZE(sizeof (u8), (u32)4U * (u32)8U * (u32)8U);
        {
          u8 hbuf[(u32)4U * (u32)8U * (u32)8U];
          memset(hbuf, 0U, (u32)4U * (u32)8U * (u32)8U * sizeof (hbuf[0U]));
          {
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
            u8 *b31;
            u8 *b21;
            u8 *b11;
            u8 *b01;
            st[0U] = st0_;
            st[1U] = st4_;
            st[2U] = st1_;
            st[3U] = st5_;
            st[4U] = st2_;
            st[5U] = st6_;
            st[6U] = st3_;
            st[7U] = st7_;
            {
              u32 i;
              for (i = (u32)0U; i < (u32)8U; i++)
                Lib_IntVector_Intrinsics_vec256_store64_be(hbuf + i * (u32)32U, st[i]);
            }
            b31 = rb.snd.snd.snd;
            b21 = rb.snd.snd.fst;
            b11 = rb.snd.fst;
            b01 = rb.fst;
            memcpy(b01, hbuf, (u32)64U * sizeof (hbuf[0U]));
            memcpy(b11, hbuf + (u32)64U, (u32)64U * sizeof ((hbuf + (u32)64U)[0U]));
            memcpy(b21, hbuf + (u32)128U, (u32)64U * sizeof ((hbuf + (u32)128U)[0U]));
            memcpy(b31, hbuf + (u32)192U, (u32)64U * sizeof ((hbuf + (u32)192U)[0U]));
          }
        }
      }
    }
  }
}

