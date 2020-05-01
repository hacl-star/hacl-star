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
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  b,
  Lib_IntVector_Intrinsics_vec512 *hash
)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)8U);
  {
    Lib_IntVector_Intrinsics_vec512 hash_old[8U];
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)8U; ++_i)
        hash_old[_i] = Lib_IntVector_Intrinsics_vec512_zero;
    }
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
    {
      Lib_IntVector_Intrinsics_vec512 ws[16U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)16U; ++_i)
          ws[_i] = Lib_IntVector_Intrinsics_vec512_zero;
      }
      {
        uint8_t *b7;
        uint8_t *b6;
        uint8_t *b5;
        uint8_t *b4;
        uint8_t *b3;
        uint8_t *b2;
        uint8_t *b10;
        uint8_t *b00;
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
        memcpy(hash_old, hash, (uint32_t)8U * sizeof (hash[0U]));
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
        ws[8U] = Lib_IntVector_Intrinsics_vec512_load64_be(b00 + (uint32_t)64U);
        ws[9U] = Lib_IntVector_Intrinsics_vec512_load64_be(b10 + (uint32_t)64U);
        ws[10U] = Lib_IntVector_Intrinsics_vec512_load64_be(b2 + (uint32_t)64U);
        ws[11U] = Lib_IntVector_Intrinsics_vec512_load64_be(b3 + (uint32_t)64U);
        ws[12U] = Lib_IntVector_Intrinsics_vec512_load64_be(b4 + (uint32_t)64U);
        ws[13U] = Lib_IntVector_Intrinsics_vec512_load64_be(b5 + (uint32_t)64U);
        ws[14U] = Lib_IntVector_Intrinsics_vec512_load64_be(b6 + (uint32_t)64U);
        ws[15U] = Lib_IntVector_Intrinsics_vec512_load64_be(b7 + (uint32_t)64U);
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
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
          {
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[(uint32_t)16U * i0 + i];
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
                                (uint32_t)64U - (uint32_t)14U),
                              Lib_IntVector_Intrinsics_vec512_shift_right64(e0, (uint32_t)14U)),
                            Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(e0,
                                  (uint32_t)64U - (uint32_t)18U),
                                Lib_IntVector_Intrinsics_vec512_shift_right64(e0, (uint32_t)18U)),
                              Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(e0,
                                  (uint32_t)64U - (uint32_t)41U),
                                Lib_IntVector_Intrinsics_vec512_shift_right64(e0, (uint32_t)41U))))),
                        Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_and(e0,
                            f0),
                          Lib_IntVector_Intrinsics_vec512_and(Lib_IntVector_Intrinsics_vec512_lognot(e0),
                            g0))),
                      k_e_t),
                    ws_t);
                Lib_IntVector_Intrinsics_vec512
                t2 =
                  Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(a0,
                          (uint32_t)64U - (uint32_t)28U),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(a0, (uint32_t)28U)),
                      Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(a0,
                            (uint32_t)64U - (uint32_t)34U),
                          Lib_IntVector_Intrinsics_vec512_shift_right64(a0, (uint32_t)34U)),
                        Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(a0,
                            (uint32_t)64U - (uint32_t)39U),
                          Lib_IntVector_Intrinsics_vec512_shift_right64(a0, (uint32_t)39U)))),
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
            if (i0 < (uint32_t)5U - (uint32_t)1U)
            {
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  Lib_IntVector_Intrinsics_vec512 t16 = ws[i];
                  Lib_IntVector_Intrinsics_vec512 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
                  Lib_IntVector_Intrinsics_vec512 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
                  Lib_IntVector_Intrinsics_vec512 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
                  Lib_IntVector_Intrinsics_vec512
                  s1 =
                    Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t2,
                          (uint32_t)64U - (uint32_t)19U),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(t2, (uint32_t)19U)),
                      Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t2,
                            (uint32_t)64U - (uint32_t)61U),
                          Lib_IntVector_Intrinsics_vec512_shift_right64(t2, (uint32_t)61U)),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(t2, (uint32_t)6U)));
                  Lib_IntVector_Intrinsics_vec512
                  s0 =
                    Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t15,
                          (uint32_t)64U - (uint32_t)1U),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(t15, (uint32_t)1U)),
                      Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_or(Lib_IntVector_Intrinsics_vec512_shift_left64(t15,
                            (uint32_t)64U - (uint32_t)8U),
                          Lib_IntVector_Intrinsics_vec512_shift_right64(t15, (uint32_t)8U)),
                        Lib_IntVector_Intrinsics_vec512_shift_right64(t15, (uint32_t)7U)));
                  ws[i] =
                    Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(Lib_IntVector_Intrinsics_vec512_add64(s1,
                          t7),
                        s0),
                      t16);
                }
              }
            }
          }
        }
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
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
  uint8_t *r0,
  uint8_t *r1,
  uint8_t *r2,
  uint8_t *r3,
  uint8_t *r4,
  uint8_t *r5,
  uint8_t *r6,
  uint8_t *r7,
  uint32_t len,
  uint8_t *b0,
  uint8_t *b1,
  uint8_t *b2,
  uint8_t *b3,
  uint8_t *b4,
  uint8_t *b5,
  uint8_t *b6,
  uint8_t *b7
)
{
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  ib;
  ib.fst = b0;
  ib.snd.fst = b1;
  ib.snd.snd.fst = b2;
  ib.snd.snd.snd.fst = b3;
  ib.snd.snd.snd.snd.fst = b4;
  ib.snd.snd.snd.snd.snd.fst = b5;
  ib.snd.snd.snd.snd.snd.snd.fst = b6;
  ib.snd.snd.snd.snd.snd.snd.snd = b7;
  {
    K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
    rb;
    rb.fst = r0;
    rb.snd.fst = r1;
    rb.snd.snd.fst = r2;
    rb.snd.snd.snd.fst = r3;
    rb.snd.snd.snd.snd.fst = r4;
    rb.snd.snd.snd.snd.snd.fst = r5;
    rb.snd.snd.snd.snd.snd.snd.fst = r6;
    rb.snd.snd.snd.snd.snd.snd.snd = r7;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)8U);
    {
      Lib_IntVector_Intrinsics_vec512 st[8U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)8U; ++_i)
          st[_i] = Lib_IntVector_Intrinsics_vec512_zero;
      }
      {
        uint32_t rem;
        FStar_UInt128_uint128 len_;
        uint32_t blocks0;
        uint32_t rem1;
        uint8_t *b710;
        uint8_t *b610;
        uint8_t *b510;
        uint8_t *b410;
        uint8_t *b310;
        uint8_t *b210;
        uint8_t *b110;
        uint8_t *b010;
        uint8_t *bl0;
        uint8_t *bl10;
        uint8_t *bl20;
        uint8_t *bl30;
        uint8_t *bl40;
        uint8_t *bl50;
        uint8_t *bl60;
        uint8_t *bl70;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
          {
            Lib_IntVector_Intrinsics_vec512 *os = st;
            uint64_t hi = Hacl_Impl_SHA2_Generic_h512[i];
            Lib_IntVector_Intrinsics_vec512 x = Lib_IntVector_Intrinsics_vec512_load64(hi);
            os[i] = x;
          }
        }
        rem = len % (uint32_t)128U;
        len_ = FStar_UInt128_uint64_to_uint128((uint64_t)len);
        blocks0 = len / (uint32_t)128U;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < blocks0; i++)
          {
            uint8_t *b71 = ib.snd.snd.snd.snd.snd.snd.snd;
            uint8_t *b61 = ib.snd.snd.snd.snd.snd.snd.fst;
            uint8_t *b51 = ib.snd.snd.snd.snd.snd.fst;
            uint8_t *b41 = ib.snd.snd.snd.snd.fst;
            uint8_t *b31 = ib.snd.snd.snd.fst;
            uint8_t *b21 = ib.snd.snd.fst;
            uint8_t *b11 = ib.snd.fst;
            uint8_t *b01 = ib.fst;
            uint8_t *bl00 = b01 + i * (uint32_t)128U;
            uint8_t *bl1 = b11 + i * (uint32_t)128U;
            uint8_t *bl2 = b21 + i * (uint32_t)128U;
            uint8_t *bl3 = b31 + i * (uint32_t)128U;
            uint8_t *bl4 = b41 + i * (uint32_t)128U;
            uint8_t *bl5 = b51 + i * (uint32_t)128U;
            uint8_t *bl6 = b61 + i * (uint32_t)128U;
            uint8_t *bl7 = b71 + i * (uint32_t)128U;
            K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
            lit;
            lit.fst = bl00;
            lit.snd.fst = bl1;
            lit.snd.snd.fst = bl2;
            lit.snd.snd.snd.fst = bl3;
            lit.snd.snd.snd.snd.fst = bl4;
            lit.snd.snd.snd.snd.snd.fst = bl5;
            lit.snd.snd.snd.snd.snd.snd.fst = bl6;
            lit.snd.snd.snd.snd.snd.snd.snd = bl7;
            {
              K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
              mb = lit;
              sha512_update8(mb, st);
            }
          }
        }
        rem1 = len % (uint32_t)128U;
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
        {
          K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
          lit0;
          K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
          lb;
          lit0.fst = bl0;
          lit0.snd.fst = bl10;
          lit0.snd.snd.fst = bl20;
          lit0.snd.snd.snd.fst = bl30;
          lit0.snd.snd.snd.snd.fst = bl40;
          lit0.snd.snd.snd.snd.snd.fst = bl50;
          lit0.snd.snd.snd.snd.snd.snd.fst = bl60;
          lit0.snd.snd.snd.snd.snd.snd.snd = bl70;
          lb = lit0;
          {
            uint32_t blocks;
            if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
            {
              blocks = (uint32_t)1U;
            }
            else
            {
              blocks = (uint32_t)2U;
            }
            {
              uint32_t fin = blocks * (uint32_t)128U;
              uint8_t last[2048U] = { 0U };
              uint8_t totlen_buf[16U] = { 0U };
              FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(len_, (uint32_t)3U);
              uint8_t *b711;
              uint8_t *b611;
              uint8_t *b511;
              uint8_t *b411;
              uint8_t *b311;
              uint8_t *b211;
              uint8_t *b111;
              uint8_t *b011;
              uint8_t *last00;
              uint8_t *last10;
              uint8_t *last2;
              uint8_t *last3;
              uint8_t *last4;
              uint8_t *last5;
              uint8_t *last6;
              uint8_t *last7;
              uint8_t *last010;
              uint8_t *last110;
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
              last10 = last + (uint32_t)256U;
              last2 = last + (uint32_t)512U;
              last3 = last + (uint32_t)768U;
              last4 = last + (uint32_t)1024U;
              last5 = last + (uint32_t)1280U;
              last6 = last + (uint32_t)1536U;
              last7 = last + (uint32_t)1792U;
              memcpy(last00, b011, rem * sizeof (b011[0U]));
              last00[rem] = (uint8_t)0x80U;
              memcpy(last00 + fin - (uint32_t)16U,
                totlen_buf,
                (uint32_t)16U * sizeof (totlen_buf[0U]));
              last010 = last00;
              last110 = last00 + (uint32_t)128U;
              {
                K____uint8_t___uint8_t_ lit1;
                K____uint8_t___uint8_t_ scrut0;
                uint8_t *l00;
                uint8_t *l01;
                uint8_t *last011;
                uint8_t *last111;
                lit1.fst = last010;
                lit1.snd = last110;
                scrut0 = lit1;
                l00 = scrut0.fst;
                l01 = scrut0.snd;
                memcpy(last10, b111, rem * sizeof (b111[0U]));
                last10[rem] = (uint8_t)0x80U;
                memcpy(last10 + fin - (uint32_t)16U,
                  totlen_buf,
                  (uint32_t)16U * sizeof (totlen_buf[0U]));
                last011 = last10;
                last111 = last10 + (uint32_t)128U;
                {
                  K____uint8_t___uint8_t_ lit2;
                  K____uint8_t___uint8_t_ scrut1;
                  uint8_t *l10;
                  uint8_t *l11;
                  uint8_t *last012;
                  uint8_t *last112;
                  lit2.fst = last011;
                  lit2.snd = last111;
                  scrut1 = lit2;
                  l10 = scrut1.fst;
                  l11 = scrut1.snd;
                  memcpy(last2, b211, rem * sizeof (b211[0U]));
                  last2[rem] = (uint8_t)0x80U;
                  memcpy(last2 + fin - (uint32_t)16U,
                    totlen_buf,
                    (uint32_t)16U * sizeof (totlen_buf[0U]));
                  last012 = last2;
                  last112 = last2 + (uint32_t)128U;
                  {
                    K____uint8_t___uint8_t_ lit3;
                    K____uint8_t___uint8_t_ scrut2;
                    uint8_t *l20;
                    uint8_t *l21;
                    uint8_t *last013;
                    uint8_t *last113;
                    lit3.fst = last012;
                    lit3.snd = last112;
                    scrut2 = lit3;
                    l20 = scrut2.fst;
                    l21 = scrut2.snd;
                    memcpy(last3, b311, rem * sizeof (b311[0U]));
                    last3[rem] = (uint8_t)0x80U;
                    memcpy(last3 + fin - (uint32_t)16U,
                      totlen_buf,
                      (uint32_t)16U * sizeof (totlen_buf[0U]));
                    last013 = last3;
                    last113 = last3 + (uint32_t)128U;
                    {
                      K____uint8_t___uint8_t_ lit4;
                      K____uint8_t___uint8_t_ scrut3;
                      uint8_t *l30;
                      uint8_t *l31;
                      uint8_t *last014;
                      uint8_t *last114;
                      lit4.fst = last013;
                      lit4.snd = last113;
                      scrut3 = lit4;
                      l30 = scrut3.fst;
                      l31 = scrut3.snd;
                      memcpy(last4, b411, rem * sizeof (b411[0U]));
                      last4[rem] = (uint8_t)0x80U;
                      memcpy(last4 + fin - (uint32_t)16U,
                        totlen_buf,
                        (uint32_t)16U * sizeof (totlen_buf[0U]));
                      last014 = last4;
                      last114 = last4 + (uint32_t)128U;
                      {
                        K____uint8_t___uint8_t_ lit5;
                        K____uint8_t___uint8_t_ scrut4;
                        uint8_t *l40;
                        uint8_t *l41;
                        uint8_t *last015;
                        uint8_t *last115;
                        lit5.fst = last014;
                        lit5.snd = last114;
                        scrut4 = lit5;
                        l40 = scrut4.fst;
                        l41 = scrut4.snd;
                        memcpy(last5, b511, rem * sizeof (b511[0U]));
                        last5[rem] = (uint8_t)0x80U;
                        memcpy(last5 + fin - (uint32_t)16U,
                          totlen_buf,
                          (uint32_t)16U * sizeof (totlen_buf[0U]));
                        last015 = last5;
                        last115 = last5 + (uint32_t)128U;
                        {
                          K____uint8_t___uint8_t_ lit6;
                          K____uint8_t___uint8_t_ scrut5;
                          uint8_t *l50;
                          uint8_t *l51;
                          uint8_t *last016;
                          uint8_t *last116;
                          lit6.fst = last015;
                          lit6.snd = last115;
                          scrut5 = lit6;
                          l50 = scrut5.fst;
                          l51 = scrut5.snd;
                          memcpy(last6, b611, rem * sizeof (b611[0U]));
                          last6[rem] = (uint8_t)0x80U;
                          memcpy(last6 + fin - (uint32_t)16U,
                            totlen_buf,
                            (uint32_t)16U * sizeof (totlen_buf[0U]));
                          last016 = last6;
                          last116 = last6 + (uint32_t)128U;
                          {
                            K____uint8_t___uint8_t_ lit7;
                            K____uint8_t___uint8_t_ scrut6;
                            uint8_t *l60;
                            uint8_t *l61;
                            uint8_t *last01;
                            uint8_t *last11;
                            lit7.fst = last016;
                            lit7.snd = last116;
                            scrut6 = lit7;
                            l60 = scrut6.fst;
                            l61 = scrut6.snd;
                            memcpy(last7, b711, rem * sizeof (b711[0U]));
                            last7[rem] = (uint8_t)0x80U;
                            memcpy(last7 + fin - (uint32_t)16U,
                              totlen_buf,
                              (uint32_t)16U * sizeof (totlen_buf[0U]));
                            last01 = last7;
                            last11 = last7 + (uint32_t)128U;
                            {
                              K____uint8_t___uint8_t_ lit8;
                              K____uint8_t___uint8_t_ scrut7;
                              uint8_t *l70;
                              uint8_t *l71;
                              lit8.fst = last01;
                              lit8.snd = last11;
                              scrut7 = lit8;
                              l70 = scrut7.fst;
                              l71 = scrut7.snd;
                              {
                                K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                                mb0;
                                mb0.fst = l00;
                                mb0.snd.fst = l10;
                                mb0.snd.snd.fst = l20;
                                mb0.snd.snd.snd.fst = l30;
                                mb0.snd.snd.snd.snd.fst = l40;
                                mb0.snd.snd.snd.snd.snd.fst = l50;
                                mb0.snd.snd.snd.snd.snd.snd.fst = l60;
                                mb0.snd.snd.snd.snd.snd.snd.snd = l70;
                                {
                                  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                                  mb1;
                                  mb1.fst = l01;
                                  mb1.snd.fst = l11;
                                  mb1.snd.snd.fst = l21;
                                  mb1.snd.snd.snd.fst = l31;
                                  mb1.snd.snd.snd.snd.fst = l41;
                                  mb1.snd.snd.snd.snd.snd.fst = l51;
                                  mb1.snd.snd.snd.snd.snd.snd.fst = l61;
                                  mb1.snd.snd.snd.snd.snd.snd.snd = l71;
                                  {
                                    K___K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                                    lit;
                                    K___K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                                    scrut;
                                    K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                                    last0;
                                    K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                                    last1;
                                    lit.fst = mb0;
                                    lit.snd = mb1;
                                    scrut = lit;
                                    last0 = scrut.fst;
                                    last1 = scrut.snd;
                                    sha512_update8(last0, st);
                                    if (blocks > (uint32_t)1U)
                                    {
                                      sha512_update8(last1, st);
                                    }
                                    KRML_CHECK_SIZE(sizeof (uint8_t),
                                      (uint32_t)8U * (uint32_t)8U * (uint32_t)8U);
                                    {
                                      uint8_t hbuf[(uint32_t)8U * (uint32_t)8U * (uint32_t)8U];
                                      memset(hbuf,
                                        0U,
                                        (uint32_t)8U
                                        * (uint32_t)8U
                                        * (uint32_t)8U
                                        * sizeof (hbuf[0U]));
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
                                        v0_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low64(v0,
                                            v1);
                                        Lib_IntVector_Intrinsics_vec512
                                        v1_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high64(v0,
                                            v1);
                                        Lib_IntVector_Intrinsics_vec512
                                        v2_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low64(v2,
                                            v3);
                                        Lib_IntVector_Intrinsics_vec512
                                        v3_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high64(v2,
                                            v3);
                                        Lib_IntVector_Intrinsics_vec512
                                        v4_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low64(v4,
                                            v5);
                                        Lib_IntVector_Intrinsics_vec512
                                        v5_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high64(v4,
                                            v5);
                                        Lib_IntVector_Intrinsics_vec512
                                        v6_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low64(v6,
                                            v7);
                                        Lib_IntVector_Intrinsics_vec512
                                        v7_ =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high64(v6,
                                            v7);
                                        Lib_IntVector_Intrinsics_vec512 v0_0 = v0_;
                                        Lib_IntVector_Intrinsics_vec512 v1_0 = v1_;
                                        Lib_IntVector_Intrinsics_vec512 v2_0 = v2_;
                                        Lib_IntVector_Intrinsics_vec512 v3_0 = v3_;
                                        Lib_IntVector_Intrinsics_vec512 v4_0 = v4_;
                                        Lib_IntVector_Intrinsics_vec512 v5_0 = v5_;
                                        Lib_IntVector_Intrinsics_vec512 v6_0 = v6_;
                                        Lib_IntVector_Intrinsics_vec512 v7_0 = v7_;
                                        Lib_IntVector_Intrinsics_vec512
                                        v0_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low128(v0_0,
                                            v2_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v2_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high128(v0_0,
                                            v2_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v1_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low128(v1_0,
                                            v3_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v3_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high128(v1_0,
                                            v3_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v4_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low128(v4_0,
                                            v6_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v6_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high128(v4_0,
                                            v6_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v5_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low128(v5_0,
                                            v7_0);
                                        Lib_IntVector_Intrinsics_vec512
                                        v7_1 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high128(v5_0,
                                            v7_0);
                                        Lib_IntVector_Intrinsics_vec512 v0_10 = v0_1;
                                        Lib_IntVector_Intrinsics_vec512 v1_10 = v1_1;
                                        Lib_IntVector_Intrinsics_vec512 v2_10 = v2_1;
                                        Lib_IntVector_Intrinsics_vec512 v3_10 = v3_1;
                                        Lib_IntVector_Intrinsics_vec512 v4_10 = v4_1;
                                        Lib_IntVector_Intrinsics_vec512 v5_10 = v5_1;
                                        Lib_IntVector_Intrinsics_vec512 v6_10 = v6_1;
                                        Lib_IntVector_Intrinsics_vec512 v7_10 = v7_1;
                                        Lib_IntVector_Intrinsics_vec512
                                        v0_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low256(v0_10,
                                            v4_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v4_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high256(v0_10,
                                            v4_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v1_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low256(v1_10,
                                            v5_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v5_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high256(v1_10,
                                            v5_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v2_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low256(v2_10,
                                            v6_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v6_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high256(v2_10,
                                            v6_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v3_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_low256(v3_10,
                                            v7_10);
                                        Lib_IntVector_Intrinsics_vec512
                                        v7_2 =
                                          Lib_IntVector_Intrinsics_vec512_interleave_high256(v3_10,
                                            v7_10);
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
                                        uint8_t *b71;
                                        uint8_t *b61;
                                        uint8_t *b51;
                                        uint8_t *b41;
                                        uint8_t *b31;
                                        uint8_t *b21;
                                        uint8_t *b11;
                                        uint8_t *b01;
                                        st[0U] = st0_;
                                        st[1U] = st1_;
                                        st[2U] = st2_;
                                        st[3U] = st3_;
                                        st[4U] = st4_;
                                        st[5U] = st5_;
                                        st[6U] = st6_;
                                        st[7U] = st7_;
                                        {
                                          uint32_t i;
                                          for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
                                          {
                                            Lib_IntVector_Intrinsics_vec512_store64_be(hbuf
                                              + i * (uint32_t)64U,
                                              st[i]);
                                          }
                                        }
                                        b71 = rb.snd.snd.snd.snd.snd.snd.snd;
                                        b61 = rb.snd.snd.snd.snd.snd.snd.fst;
                                        b51 = rb.snd.snd.snd.snd.snd.fst;
                                        b41 = rb.snd.snd.snd.snd.fst;
                                        b31 = rb.snd.snd.snd.fst;
                                        b21 = rb.snd.snd.fst;
                                        b11 = rb.snd.fst;
                                        b01 = rb.fst;
                                        memcpy(b01, hbuf, (uint32_t)64U * sizeof (hbuf[0U]));
                                        memcpy(b11,
                                          hbuf + (uint32_t)64U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)64U)[0U]));
                                        memcpy(b21,
                                          hbuf + (uint32_t)128U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)128U)[0U]));
                                        memcpy(b31,
                                          hbuf + (uint32_t)192U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)192U)[0U]));
                                        memcpy(b41,
                                          hbuf + (uint32_t)256U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)256U)[0U]));
                                        memcpy(b51,
                                          hbuf + (uint32_t)320U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)320U)[0U]));
                                        memcpy(b61,
                                          hbuf + (uint32_t)384U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)384U)[0U]));
                                        memcpy(b71,
                                          hbuf + (uint32_t)448U,
                                          (uint32_t)64U * sizeof ((hbuf + (uint32_t)448U)[0U]));
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

