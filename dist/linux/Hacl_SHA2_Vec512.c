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


#include "Hacl_SHA2_Vec512.h"

static inline void
sha512_update8(
  K____u8__K____u8__K____u8__K____u8__K____u8__K____u8__K____u8___u8_ b,
  Lib_IntVector_Intrinsics_vec512 *hash
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (u32)8U);
  {
    Lib_IntVector_Intrinsics_vec512 hash_old[8U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)8U; ++_i)
        hash_old[_i] = Lib_IntVector_Intrinsics_vec512_zero;
    }
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (u32)16U);
    {
      Lib_IntVector_Intrinsics_vec512 ws[16U];
      {
        u32 _i;
        for (_i = 0U; _i < (u32)16U; ++_i)
          ws[_i] = Lib_IntVector_Intrinsics_vec512_zero;
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
        Lib_IntVector_Intrinsics_vec512 v00;
        Lib_IntVector_Intrinsics_vec512 v10;
        Lib_IntVector_Intrinsics_vec512 v20;
        Lib_IntVector_Intrinsics_vec512 v30;
        Lib_IntVector_Intrinsics_vec512 v40;
        Lib_IntVector_Intrinsics_vec512 v50;
        Lib_IntVector_Intrinsics_vec512 v60;
        Lib_IntVector_Intrinsics_vec512 v70;
        Lib_IntVector_Intrinsics_vec512 v0_;
        Lib_IntVector_Intrinsics_vec512 v1_;
        Lib_IntVector_Intrinsics_vec512 v2_;
        Lib_IntVector_Intrinsics_vec512 v3_;
        Lib_IntVector_Intrinsics_vec512 v4_;
        Lib_IntVector_Intrinsics_vec512 v5_;
        Lib_IntVector_Intrinsics_vec512 v6_;
        Lib_IntVector_Intrinsics_vec512 v7_;
        Lib_IntVector_Intrinsics_vec512 v0_0;
        Lib_IntVector_Intrinsics_vec512 v1_0;
        Lib_IntVector_Intrinsics_vec512 v2_0;
        Lib_IntVector_Intrinsics_vec512 v3_0;
        Lib_IntVector_Intrinsics_vec512 v4_0;
        Lib_IntVector_Intrinsics_vec512 v5_0;
        Lib_IntVector_Intrinsics_vec512 v6_0;
        Lib_IntVector_Intrinsics_vec512 v7_0;
        Lib_IntVector_Intrinsics_vec512 v0_1;
        Lib_IntVector_Intrinsics_vec512 v2_1;
        Lib_IntVector_Intrinsics_vec512 v1_1;
        Lib_IntVector_Intrinsics_vec512 v3_1;
        Lib_IntVector_Intrinsics_vec512 v4_1;
        Lib_IntVector_Intrinsics_vec512 v6_1;
        Lib_IntVector_Intrinsics_vec512 v5_1;
        Lib_IntVector_Intrinsics_vec512 v7_1;
        Lib_IntVector_Intrinsics_vec512 v0_10;
        Lib_IntVector_Intrinsics_vec512 v1_10;
        Lib_IntVector_Intrinsics_vec512 v2_10;
        Lib_IntVector_Intrinsics_vec512 v3_10;
        Lib_IntVector_Intrinsics_vec512 v4_10;
        Lib_IntVector_Intrinsics_vec512 v5_10;
        Lib_IntVector_Intrinsics_vec512 v6_10;
        Lib_IntVector_Intrinsics_vec512 v7_10;
        Lib_IntVector_Intrinsics_vec512 v0_2;
        Lib_IntVector_Intrinsics_vec512 v4_2;
        Lib_IntVector_Intrinsics_vec512 v1_2;
        Lib_IntVector_Intrinsics_vec512 v5_2;
        Lib_IntVector_Intrinsics_vec512 v2_2;
        Lib_IntVector_Intrinsics_vec512 v6_2;
        Lib_IntVector_Intrinsics_vec512 v3_2;
        Lib_IntVector_Intrinsics_vec512 v7_2;
        Lib_IntVector_Intrinsics_vec512 v0_20;
        Lib_IntVector_Intrinsics_vec512 v1_20;
        Lib_IntVector_Intrinsics_vec512 v2_20;
        Lib_IntVector_Intrinsics_vec512 v3_20;
        Lib_IntVector_Intrinsics_vec512 v4_20;
        Lib_IntVector_Intrinsics_vec512 v5_20;
        Lib_IntVector_Intrinsics_vec512 v6_20;
        Lib_IntVector_Intrinsics_vec512 v7_20;
        Lib_IntVector_Intrinsics_vec512 ws0;
        Lib_IntVector_Intrinsics_vec512 ws1;
        Lib_IntVector_Intrinsics_vec512 ws2;
        Lib_IntVector_Intrinsics_vec512 ws3;
        Lib_IntVector_Intrinsics_vec512 ws4;
        Lib_IntVector_Intrinsics_vec512 ws5;
        Lib_IntVector_Intrinsics_vec512 ws6;
        Lib_IntVector_Intrinsics_vec512 ws7;
        Lib_IntVector_Intrinsics_vec512 v0;
        Lib_IntVector_Intrinsics_vec512 v1;
        Lib_IntVector_Intrinsics_vec512 v2;
        Lib_IntVector_Intrinsics_vec512 v3;
        Lib_IntVector_Intrinsics_vec512 v4;
        Lib_IntVector_Intrinsics_vec512 v5;
        Lib_IntVector_Intrinsics_vec512 v6;
        Lib_IntVector_Intrinsics_vec512 v7;
        Lib_IntVector_Intrinsics_vec512 v0_3;
        Lib_IntVector_Intrinsics_vec512 v1_3;
        Lib_IntVector_Intrinsics_vec512 v2_3;
        Lib_IntVector_Intrinsics_vec512 v3_3;
        Lib_IntVector_Intrinsics_vec512 v4_3;
        Lib_IntVector_Intrinsics_vec512 v5_3;
        Lib_IntVector_Intrinsics_vec512 v6_3;
        Lib_IntVector_Intrinsics_vec512 v7_3;
        Lib_IntVector_Intrinsics_vec512 v0_4;
        Lib_IntVector_Intrinsics_vec512 v1_4;
        Lib_IntVector_Intrinsics_vec512 v2_4;
        Lib_IntVector_Intrinsics_vec512 v3_4;
        Lib_IntVector_Intrinsics_vec512 v4_4;
        Lib_IntVector_Intrinsics_vec512 v5_4;
        Lib_IntVector_Intrinsics_vec512 v6_4;
        Lib_IntVector_Intrinsics_vec512 v7_4;
        Lib_IntVector_Intrinsics_vec512 v0_11;
        Lib_IntVector_Intrinsics_vec512 v2_11;
        Lib_IntVector_Intrinsics_vec512 v1_11;
        Lib_IntVector_Intrinsics_vec512 v3_11;
        Lib_IntVector_Intrinsics_vec512 v4_11;
        Lib_IntVector_Intrinsics_vec512 v6_11;
        Lib_IntVector_Intrinsics_vec512 v5_11;
        Lib_IntVector_Intrinsics_vec512 v7_11;
        Lib_IntVector_Intrinsics_vec512 v0_12;
        Lib_IntVector_Intrinsics_vec512 v1_12;
        Lib_IntVector_Intrinsics_vec512 v2_12;
        Lib_IntVector_Intrinsics_vec512 v3_12;
        Lib_IntVector_Intrinsics_vec512 v4_12;
        Lib_IntVector_Intrinsics_vec512 v5_12;
        Lib_IntVector_Intrinsics_vec512 v6_12;
        Lib_IntVector_Intrinsics_vec512 v7_12;
        Lib_IntVector_Intrinsics_vec512 v0_21;
        Lib_IntVector_Intrinsics_vec512 v4_21;
        Lib_IntVector_Intrinsics_vec512 v1_21;
        Lib_IntVector_Intrinsics_vec512 v5_21;
        Lib_IntVector_Intrinsics_vec512 v2_21;
        Lib_IntVector_Intrinsics_vec512 v6_21;
        Lib_IntVector_Intrinsics_vec512 v3_21;
        Lib_IntVector_Intrinsics_vec512 v7_21;
        Lib_IntVector_Intrinsics_vec512 v0_22;
        Lib_IntVector_Intrinsics_vec512 v1_22;
        Lib_IntVector_Intrinsics_vec512 v2_22;
        Lib_IntVector_Intrinsics_vec512 v3_22;
        Lib_IntVector_Intrinsics_vec512 v4_22;
        Lib_IntVector_Intrinsics_vec512 v5_22;
        Lib_IntVector_Intrinsics_vec512 v6_22;
        Lib_IntVector_Intrinsics_vec512 v7_22;
        Lib_IntVector_Intrinsics_vec512 ws8;
        Lib_IntVector_Intrinsics_vec512 ws9;
        Lib_IntVector_Intrinsics_vec512 ws10;
        Lib_IntVector_Intrinsics_vec512 ws11;
        Lib_IntVector_Intrinsics_vec512 ws12;
        Lib_IntVector_Intrinsics_vec512 ws13;
        Lib_IntVector_Intrinsics_vec512 ws14;
        Lib_IntVector_Intrinsics_vec512 ws15;
        memcpy(hash_old, hash, (u32)8U * sizeof (hash[0U]));
        b7 = b.snd.snd.snd.snd.snd.snd.snd;
        b6 = b.snd.snd.snd.snd.snd.snd.fst;
        b5 = b.snd.snd.snd.snd.snd.fst;
        b4 = b.snd.snd.snd.snd.fst;
        b3 = b.snd.snd.snd.fst;
        b2 = b.snd.snd.fst;
        b10 = b.snd.fst;
        b00 = b.fst;
        ws[0U] = Lib_IntVector_Intrinsics_vec512_load64_be(b00);
        ws[1U] = Lib_IntVector_Intrinsics_vec512_load64_be(b10);
        ws[2U] = Lib_IntVector_Intrinsics_vec512_load64_be(b2);
        ws[3U] = Lib_IntVector_Intrinsics_vec512_load64_be(b3);
        ws[4U] = Lib_IntVector_Intrinsics_vec512_load64_be(b4);
        ws[5U] = Lib_IntVector_Intrinsics_vec512_load64_be(b5);
        ws[6U] = Lib_IntVector_Intrinsics_vec512_load64_be(b6);
        ws[7U] = Lib_IntVector_Intrinsics_vec512_load64_be(b7);
        ws[8U] = Lib_IntVector_Intrinsics_vec512_load64_be(b00 + (u32)64U);
        ws[9U] = Lib_IntVector_Intrinsics_vec512_load64_be(b10 + (u32)64U);
        ws[10U] = Lib_IntVector_Intrinsics_vec512_load64_be(b2 + (u32)64U);
        ws[11U] = Lib_IntVector_Intrinsics_vec512_load64_be(b3 + (u32)64U);
        ws[12U] = Lib_IntVector_Intrinsics_vec512_load64_be(b4 + (u32)64U);
        ws[13U] = Lib_IntVector_Intrinsics_vec512_load64_be(b5 + (u32)64U);
        ws[14U] = Lib_IntVector_Intrinsics_vec512_load64_be(b6 + (u32)64U);
        ws[15U] = Lib_IntVector_Intrinsics_vec512_load64_be(b7 + (u32)64U);
        v00 = ws[0U];
        v10 = ws[1U];
        v20 = ws[2U];
        v30 = ws[3U];
        v40 = ws[4U];
        v50 = ws[5U];
        v60 = ws[6U];
        v70 = ws[7U];
        v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v00, v10);
        v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v00, v10);
        v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v20, v30);
        v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v20, v30);
        v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v40, v50);
        v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v40, v50);
        v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v60, v70);
        v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v60, v70);
        v0_0 = v0_;
        v1_0 = v1_;
        v2_0 = v2_;
        v3_0 = v3_;
        v4_0 = v4_;
        v5_0 = v5_;
        v6_0 = v6_;
        v7_0 = v7_;
        v0_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v0_0, v2_0);
        v2_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v0_0, v2_0);
        v1_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1_0, v3_0);
        v3_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1_0, v3_0);
        v4_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v4_0, v6_0);
        v6_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v4_0, v6_0);
        v5_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v5_0, v7_0);
        v7_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v5_0, v7_0);
        v0_10 = v0_1;
        v1_10 = v1_1;
        v2_10 = v2_1;
        v3_10 = v3_1;
        v4_10 = v4_1;
        v5_10 = v5_1;
        v6_10 = v6_1;
        v7_10 = v7_1;
        v0_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v0_10, v4_10);
        v4_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v0_10, v4_10);
        v1_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v1_10, v5_10);
        v5_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v1_10, v5_10);
        v2_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v2_10, v6_10);
        v6_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v2_10, v6_10);
        v3_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v3_10, v7_10);
        v7_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v3_10, v7_10);
        v0_20 = v0_2;
        v1_20 = v1_2;
        v2_20 = v2_2;
        v3_20 = v3_2;
        v4_20 = v4_2;
        v5_20 = v5_2;
        v6_20 = v6_2;
        v7_20 = v7_2;
        ws0 = v0_20;
        ws1 = v1_20;
        ws2 = v2_20;
        ws3 = v3_20;
        ws4 = v4_20;
        ws5 = v5_20;
        ws6 = v6_20;
        ws7 = v7_20;
        v0 = ws[8U];
        v1 = ws[9U];
        v2 = ws[10U];
        v3 = ws[11U];
        v4 = ws[12U];
        v5 = ws[13U];
        v6 = ws[14U];
        v7 = ws[15U];
        v0_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v0, v1);
        v1_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v0, v1);
        v2_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v2, v3);
        v3_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v2, v3);
        v4_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v4, v5);
        v5_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v4, v5);
        v6_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v6, v7);
        v7_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v6, v7);
        v0_4 = v0_3;
        v1_4 = v1_3;
        v2_4 = v2_3;
        v3_4 = v3_3;
        v4_4 = v4_3;
        v5_4 = v5_3;
        v6_4 = v6_3;
        v7_4 = v7_3;
        v0_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v0_4, v2_4);
        v2_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v0_4, v2_4);
        v1_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1_4, v3_4);
        v3_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1_4, v3_4);
        v4_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v4_4, v6_4);
        v6_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v4_4, v6_4);
        v5_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v5_4, v7_4);
        v7_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v5_4, v7_4);
        v0_12 = v0_11;
        v1_12 = v1_11;
        v2_12 = v2_11;
        v3_12 = v3_11;
        v4_12 = v4_11;
        v5_12 = v5_11;
        v6_12 = v6_11;
        v7_12 = v7_11;
        v0_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v0_12, v4_12);
        v4_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v0_12, v4_12);
        v1_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v1_12, v5_12);
        v5_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v1_12, v5_12);
        v2_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v2_12, v6_12);
        v6_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v2_12, v6_12);
        v3_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v3_12, v7_12);
        v7_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v3_12, v7_12);
        v0_22 = v0_21;
        v1_22 = v1_21;
        v2_22 = v2_21;
        v3_22 = v3_21;
        v4_22 = v4_21;
        v5_22 = v5_21;
        v6_22 = v6_21;
        v7_22 = v7_21;
        ws8 = v0_22;
        ws9 = v1_22;
        ws10 = v2_22;
        ws11 = v3_22;
        ws12 = v4_22;
        ws13 = v5_22;
        ws14 = v6_22;
        ws15 = v7_22;
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
                Lib_IntVector_Intrinsics_vec512 ws_t = ws[i];
                Lib_IntVector_Intrinsics_vec512 a0 = hash[0U];
                Lib_IntVector_Intrinsics_vec512 b0 = hash[1U];
                Lib_IntVector_Intrinsics_vec512 c0 = hash[2U];
                Lib_IntVector_Intrinsics_vec512 d0 = hash[3U];
                Lib_IntVector_Intrinsics_vec512 e0 = hash[4U];
                Lib_IntVector_Intrinsics_vec512 f0 = hash[5U];
                Lib_IntVector_Intrinsics_vec512 g0 = hash[6U];
                Lib_IntVector_Intrinsics_vec512 h02 = hash[7U];
                Lib_IntVector_Intrinsics_vec512 k_e_t = Lib_IntVector_Intrinsics_vec512_load64(k_t);
                Lib_IntVector_Intrinsics_vec512
                t1 =
                  Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(h02,
                          Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(e0,
                                (u32)64U - (u32)14U),
                              Lib_IntVector_Intrinsics_vec512_shift_right64(e0, (u32)14U)),
                            Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(e0,
                                  (u32)64U - (u32)18U),
                                Lib_IntVector_Intrinsics_vec512_shift_right64(e0, (u32)18U)),
                              Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(e0,
                                  (u32)64U - (u32)41U),
                                Lib_IntVector_Intrinsics_vec512_shift_right64(e0, (u32)41U))))),
                        Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_and(e0,
                            f0),
                          Lib_IntVector_Intrinsics_vec512_and(Lib_IntVector_Intrinsics_vec512_lognot(e0),
                            g0))),
                      k_e_t),
                    ws_t);
                Lib_IntVector_Intrinsics_vec512
                t2 =
                  Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(a0,
                          (u32)64U - (u32)28U),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(a0, (u32)28U)),
                      Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(a0,
                            (u32)64U - (u32)34U),
                          Lib_IntVector_Intrinsics_vec512_shift_right64(a0, (u32)34U)),
                        Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(a0,
                            (u32)64U - (u32)39U),
                          Lib_IntVector_Intrinsics_vec512_shift_right64(a0, (u32)39U)))),
                    Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_and(a0, b0),
                      Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_and(a0,
                          c0),
                        Lib_IntVector_Intrinsics_vec512_and(b0, c0))));
                Lib_IntVector_Intrinsics_vec512 a1 = Lib_IntVector_Intrinsics_vec512_add64(t1, t2);
                Lib_IntVector_Intrinsics_vec512 b1 = a0;
                Lib_IntVector_Intrinsics_vec512 c1 = b0;
                Lib_IntVector_Intrinsics_vec512 d1 = c0;
                Lib_IntVector_Intrinsics_vec512 e1 = Lib_IntVector_Intrinsics_vec512_add64(d0, t1);
                Lib_IntVector_Intrinsics_vec512 f1 = e0;
                Lib_IntVector_Intrinsics_vec512 g1 = f0;
                Lib_IntVector_Intrinsics_vec512 h12 = g0;
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
                Lib_IntVector_Intrinsics_vec512 t16 = ws[i];
                Lib_IntVector_Intrinsics_vec512 t15 = ws[(i + (u32)1U) % (u32)16U];
                Lib_IntVector_Intrinsics_vec512 t7 = ws[(i + (u32)9U) % (u32)16U];
                Lib_IntVector_Intrinsics_vec512 t2 = ws[(i + (u32)14U) % (u32)16U];
                Lib_IntVector_Intrinsics_vec512
                s1 =
                  Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t2,
                        (u32)64U - (u32)19U),
                      Lib_IntVector_Intrinsics_vec512_shift_right64(t2, (u32)19U)),
                    Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t2,
                          (u32)64U - (u32)61U),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(t2, (u32)61U)),
                      Lib_IntVector_Intrinsics_vec512_shift_right64(t2, (u32)6U)));
                Lib_IntVector_Intrinsics_vec512
                s0 =
                  Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t15,
                        (u32)64U - (u32)1U),
                      Lib_IntVector_Intrinsics_vec512_shift_right64(t15, (u32)1U)),
                    Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t15,
                          (u32)64U - (u32)8U),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(t15, (u32)8U)),
                      Lib_IntVector_Intrinsics_vec512_shift_right64(t15, (u32)7U)));
                ws[i] =
                  Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(s1,
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
            Lib_IntVector_Intrinsics_vec512 *os = hash;
            Lib_IntVector_Intrinsics_vec512
            x = Lib_IntVector_Intrinsics_vec512_add64(hash[i], hash_old[i]);
            os[i] = x;
          }
        }
      }
    }
  }
}

void
Hacl_SHA2_Vec512_sha512_8(
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
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (u32)8U);
  {
    Lib_IntVector_Intrinsics_vec512 st[8U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)8U; ++_i)
        st[_i] = Lib_IntVector_Intrinsics_vec512_zero;
    }
    {
      u32 rem;
      uint128_t len_;
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
          Lib_IntVector_Intrinsics_vec512 *os = st;
          u64 hi = Hacl_Impl_SHA2_Generic_h512[i];
          Lib_IntVector_Intrinsics_vec512 x = Lib_IntVector_Intrinsics_vec512_load64(hi);
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
          u8 *b71 = ib.snd.snd.snd.snd.snd.snd.snd;
          u8 *b61 = ib.snd.snd.snd.snd.snd.snd.fst;
          u8 *b51 = ib.snd.snd.snd.snd.snd.fst;
          u8 *b41 = ib.snd.snd.snd.snd.fst;
          u8 *b31 = ib.snd.snd.snd.fst;
          u8 *b21 = ib.snd.snd.fst;
          u8 *b11 = ib.snd.fst;
          u8 *b01 = ib.fst;
          u8 *bl00 = b01 + i * (u32)128U;
          u8 *bl1 = b11 + i * (u32)128U;
          u8 *bl2 = b21 + i * (u32)128U;
          u8 *bl3 = b31 + i * (u32)128U;
          u8 *bl4 = b41 + i * (u32)128U;
          u8 *bl5 = b51 + i * (u32)128U;
          u8 *bl6 = b61 + i * (u32)128U;
          u8 *bl7 = b71 + i * (u32)128U;
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
          sha512_update8(mb, st);
        }
      }
      rem1 = len % (u32)128U;
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
                  .snd = {
                    .fst = bl40,
                    .snd = { .fst = bl50, .snd = { .fst = bl60, .snd = bl70 } }
                  }
                }
              }
            }
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
          u8 last[2048U] = { 0U };
          u8 totlen_buf[16U] = { 0U };
          uint128_t total_len_bits = len_ << (u32)3U;
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
          store128_be(totlen_buf, total_len_bits);
          b711 = lb.snd.snd.snd.snd.snd.snd.snd;
          b611 = lb.snd.snd.snd.snd.snd.snd.fst;
          b511 = lb.snd.snd.snd.snd.snd.fst;
          b411 = lb.snd.snd.snd.snd.fst;
          b311 = lb.snd.snd.snd.fst;
          b211 = lb.snd.snd.fst;
          b111 = lb.snd.fst;
          b011 = lb.fst;
          last00 = last;
          last10 = last + (u32)256U;
          last2 = last + (u32)512U;
          last3 = last + (u32)768U;
          last4 = last + (u32)1024U;
          last5 = last + (u32)1280U;
          last6 = last + (u32)1536U;
          last7 = last + (u32)1792U;
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
          last013 = last3;
          last113 = last3 + (u32)128U;
          scrut3 = ((K____u8___u8_){ .fst = last013, .snd = last113 });
          l30 = scrut3.fst;
          l31 = scrut3.snd;
          memcpy(last4, b411, rem * sizeof (b411[0U]));
          last4[rem] = (u8)0x80U;
          memcpy(last4 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
          last014 = last4;
          last114 = last4 + (u32)128U;
          scrut4 = ((K____u8___u8_){ .fst = last014, .snd = last114 });
          l40 = scrut4.fst;
          l41 = scrut4.snd;
          memcpy(last5, b511, rem * sizeof (b511[0U]));
          last5[rem] = (u8)0x80U;
          memcpy(last5 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
          last015 = last5;
          last115 = last5 + (u32)128U;
          scrut5 = ((K____u8___u8_){ .fst = last015, .snd = last115 });
          l50 = scrut5.fst;
          l51 = scrut5.snd;
          memcpy(last6, b611, rem * sizeof (b611[0U]));
          last6[rem] = (u8)0x80U;
          memcpy(last6 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
          last016 = last6;
          last116 = last6 + (u32)128U;
          scrut6 = ((K____u8___u8_){ .fst = last016, .snd = last116 });
          l60 = scrut6.fst;
          l61 = scrut6.snd;
          memcpy(last7, b711, rem * sizeof (b711[0U]));
          last7[rem] = (u8)0x80U;
          memcpy(last7 + fin - (u32)16U, totlen_buf, (u32)16U * sizeof (totlen_buf[0U]));
          last01 = last7;
          last11 = last7 + (u32)128U;
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
                      .snd = {
                        .fst = l40,
                        .snd = { .fst = l50, .snd = { .fst = l60, .snd = l70 } }
                      }
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
                      .snd = {
                        .fst = l41,
                        .snd = { .fst = l51, .snd = { .fst = l61, .snd = l71 } }
                      }
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
          sha512_update8(last0, st);
          if (blocks > (u32)1U)
            sha512_update8(last1, st);
          KRML_CHECK_SIZE(sizeof (u8), (u32)8U * (u32)8U * (u32)8U);
          {
            u8 hbuf[(u32)8U * (u32)8U * (u32)8U];
            memset(hbuf, 0U, (u32)8U * (u32)8U * (u32)8U * sizeof (hbuf[0U]));
            {
              Lib_IntVector_Intrinsics_vec512 v0 = st[0U];
              Lib_IntVector_Intrinsics_vec512 v1 = st[1U];
              Lib_IntVector_Intrinsics_vec512 v2 = st[2U];
              Lib_IntVector_Intrinsics_vec512 v3 = st[3U];
              Lib_IntVector_Intrinsics_vec512 v4 = st[4U];
              Lib_IntVector_Intrinsics_vec512 v5 = st[5U];
              Lib_IntVector_Intrinsics_vec512 v6 = st[6U];
              Lib_IntVector_Intrinsics_vec512 v7 = st[7U];
              Lib_IntVector_Intrinsics_vec512
              v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v0, v1);
              Lib_IntVector_Intrinsics_vec512
              v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v0, v1);
              Lib_IntVector_Intrinsics_vec512
              v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v2, v3);
              Lib_IntVector_Intrinsics_vec512
              v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v2, v3);
              Lib_IntVector_Intrinsics_vec512
              v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v4, v5);
              Lib_IntVector_Intrinsics_vec512
              v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v4, v5);
              Lib_IntVector_Intrinsics_vec512
              v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v6, v7);
              Lib_IntVector_Intrinsics_vec512
              v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v6, v7);
              Lib_IntVector_Intrinsics_vec512 v0_0 = v0_;
              Lib_IntVector_Intrinsics_vec512 v1_0 = v1_;
              Lib_IntVector_Intrinsics_vec512 v2_0 = v2_;
              Lib_IntVector_Intrinsics_vec512 v3_0 = v3_;
              Lib_IntVector_Intrinsics_vec512 v4_0 = v4_;
              Lib_IntVector_Intrinsics_vec512 v5_0 = v5_;
              Lib_IntVector_Intrinsics_vec512 v6_0 = v6_;
              Lib_IntVector_Intrinsics_vec512 v7_0 = v7_;
              Lib_IntVector_Intrinsics_vec512
              v0_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v0_0, v2_0);
              Lib_IntVector_Intrinsics_vec512
              v2_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v0_0, v2_0);
              Lib_IntVector_Intrinsics_vec512
              v1_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1_0, v3_0);
              Lib_IntVector_Intrinsics_vec512
              v3_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1_0, v3_0);
              Lib_IntVector_Intrinsics_vec512
              v4_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v4_0, v6_0);
              Lib_IntVector_Intrinsics_vec512
              v6_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v4_0, v6_0);
              Lib_IntVector_Intrinsics_vec512
              v5_1 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v5_0, v7_0);
              Lib_IntVector_Intrinsics_vec512
              v7_1 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v5_0, v7_0);
              Lib_IntVector_Intrinsics_vec512 v0_10 = v0_1;
              Lib_IntVector_Intrinsics_vec512 v1_10 = v1_1;
              Lib_IntVector_Intrinsics_vec512 v2_10 = v2_1;
              Lib_IntVector_Intrinsics_vec512 v3_10 = v3_1;
              Lib_IntVector_Intrinsics_vec512 v4_10 = v4_1;
              Lib_IntVector_Intrinsics_vec512 v5_10 = v5_1;
              Lib_IntVector_Intrinsics_vec512 v6_10 = v6_1;
              Lib_IntVector_Intrinsics_vec512 v7_10 = v7_1;
              Lib_IntVector_Intrinsics_vec512
              v0_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v0_10, v4_10);
              Lib_IntVector_Intrinsics_vec512
              v4_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v0_10, v4_10);
              Lib_IntVector_Intrinsics_vec512
              v1_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v1_10, v5_10);
              Lib_IntVector_Intrinsics_vec512
              v5_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v1_10, v5_10);
              Lib_IntVector_Intrinsics_vec512
              v2_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v2_10, v6_10);
              Lib_IntVector_Intrinsics_vec512
              v6_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v2_10, v6_10);
              Lib_IntVector_Intrinsics_vec512
              v3_2 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v3_10, v7_10);
              Lib_IntVector_Intrinsics_vec512
              v7_2 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v3_10, v7_10);
              Lib_IntVector_Intrinsics_vec512 v0_20 = v0_2;
              Lib_IntVector_Intrinsics_vec512 v1_20 = v1_2;
              Lib_IntVector_Intrinsics_vec512 v2_20 = v2_2;
              Lib_IntVector_Intrinsics_vec512 v3_20 = v3_2;
              Lib_IntVector_Intrinsics_vec512 v4_20 = v4_2;
              Lib_IntVector_Intrinsics_vec512 v5_20 = v5_2;
              Lib_IntVector_Intrinsics_vec512 v6_20 = v6_2;
              Lib_IntVector_Intrinsics_vec512 v7_20 = v7_2;
              Lib_IntVector_Intrinsics_vec512 st0_ = v0_20;
              Lib_IntVector_Intrinsics_vec512 st1_ = v1_20;
              Lib_IntVector_Intrinsics_vec512 st2_ = v2_20;
              Lib_IntVector_Intrinsics_vec512 st3_ = v3_20;
              Lib_IntVector_Intrinsics_vec512 st4_ = v4_20;
              Lib_IntVector_Intrinsics_vec512 st5_ = v5_20;
              Lib_IntVector_Intrinsics_vec512 st6_ = v6_20;
              Lib_IntVector_Intrinsics_vec512 st7_ = v7_20;
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
                  Lib_IntVector_Intrinsics_vec512_store64_be(hbuf + i * (u32)64U, st[i]);
              }
              b71 = rb.snd.snd.snd.snd.snd.snd.snd;
              b61 = rb.snd.snd.snd.snd.snd.snd.fst;
              b51 = rb.snd.snd.snd.snd.snd.fst;
              b41 = rb.snd.snd.snd.snd.fst;
              b31 = rb.snd.snd.snd.fst;
              b21 = rb.snd.snd.fst;
              b11 = rb.snd.fst;
              b01 = rb.fst;
              memcpy(b01, hbuf, (u32)64U * sizeof (hbuf[0U]));
              memcpy(b11, hbuf + (u32)64U, (u32)64U * sizeof ((hbuf + (u32)64U)[0U]));
              memcpy(b21, hbuf + (u32)128U, (u32)64U * sizeof ((hbuf + (u32)128U)[0U]));
              memcpy(b31, hbuf + (u32)192U, (u32)64U * sizeof ((hbuf + (u32)192U)[0U]));
              memcpy(b41, hbuf + (u32)256U, (u32)64U * sizeof ((hbuf + (u32)256U)[0U]));
              memcpy(b51, hbuf + (u32)320U, (u32)64U * sizeof ((hbuf + (u32)320U)[0U]));
              memcpy(b61, hbuf + (u32)384U, (u32)64U * sizeof ((hbuf + (u32)384U)[0U]));
              memcpy(b71, hbuf + (u32)448U, (u32)64U * sizeof ((hbuf + (u32)448U)[0U]));
            }
          }
        }
      }
    }
  }
}

