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
  Lib_IntVector_Intrinsics_vec512 hash_old[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    hash_old[_i] = Lib_IntVector_Intrinsics_vec512_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)16U);
  Lib_IntVector_Intrinsics_vec512 ws[16U];
  for (uint32_t _i = 0U; _i < (uint32_t)16U; ++_i)
    ws[_i] = Lib_IntVector_Intrinsics_vec512_zero;
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (hash[0U]));
  uint8_t *b7 = b.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b6 = b.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b5 = b.snd.snd.snd.snd.snd.fst;
  uint8_t *b4 = b.snd.snd.snd.snd.fst;
  uint8_t *b3 = b.snd.snd.snd.fst;
  uint8_t *b2 = b.snd.snd.fst;
  uint8_t *b10 = b.snd.fst;
  uint8_t *b00 = b.fst;
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
  Lib_IntVector_Intrinsics_vec512 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec512 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec512 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec512 v30 = ws[3U];
  Lib_IntVector_Intrinsics_vec512 v40 = ws[4U];
  Lib_IntVector_Intrinsics_vec512 v50 = ws[5U];
  Lib_IntVector_Intrinsics_vec512 v60 = ws[6U];
  Lib_IntVector_Intrinsics_vec512 v70 = ws[7U];
  Lib_IntVector_Intrinsics_vec512
  v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v00, v10);
  Lib_IntVector_Intrinsics_vec512
  v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v00, v10);
  Lib_IntVector_Intrinsics_vec512
  v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v20, v30);
  Lib_IntVector_Intrinsics_vec512
  v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v20, v30);
  Lib_IntVector_Intrinsics_vec512
  v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v40, v50);
  Lib_IntVector_Intrinsics_vec512
  v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v40, v50);
  Lib_IntVector_Intrinsics_vec512
  v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v60, v70);
  Lib_IntVector_Intrinsics_vec512
  v7_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v60, v70);
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
  Lib_IntVector_Intrinsics_vec512 ws0 = v0_20;
  Lib_IntVector_Intrinsics_vec512 ws1 = v1_20;
  Lib_IntVector_Intrinsics_vec512 ws2 = v2_20;
  Lib_IntVector_Intrinsics_vec512 ws3 = v3_20;
  Lib_IntVector_Intrinsics_vec512 ws4 = v4_20;
  Lib_IntVector_Intrinsics_vec512 ws5 = v5_20;
  Lib_IntVector_Intrinsics_vec512 ws6 = v6_20;
  Lib_IntVector_Intrinsics_vec512 ws7 = v7_20;
  Lib_IntVector_Intrinsics_vec512 v0 = ws[8U];
  Lib_IntVector_Intrinsics_vec512 v1 = ws[9U];
  Lib_IntVector_Intrinsics_vec512 v2 = ws[10U];
  Lib_IntVector_Intrinsics_vec512 v3 = ws[11U];
  Lib_IntVector_Intrinsics_vec512 v4 = ws[12U];
  Lib_IntVector_Intrinsics_vec512 v5 = ws[13U];
  Lib_IntVector_Intrinsics_vec512 v6 = ws[14U];
  Lib_IntVector_Intrinsics_vec512 v7 = ws[15U];
  Lib_IntVector_Intrinsics_vec512
  v0_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v0, v1);
  Lib_IntVector_Intrinsics_vec512
  v1_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v0, v1);
  Lib_IntVector_Intrinsics_vec512
  v2_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v2, v3);
  Lib_IntVector_Intrinsics_vec512
  v3_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v2, v3);
  Lib_IntVector_Intrinsics_vec512
  v4_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v4, v5);
  Lib_IntVector_Intrinsics_vec512
  v5_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v4, v5);
  Lib_IntVector_Intrinsics_vec512
  v6_3 = Lib_IntVector_Intrinsics_vec512_interleave_low64(v6, v7);
  Lib_IntVector_Intrinsics_vec512
  v7_3 = Lib_IntVector_Intrinsics_vec512_interleave_high64(v6, v7);
  Lib_IntVector_Intrinsics_vec512 v0_4 = v0_3;
  Lib_IntVector_Intrinsics_vec512 v1_4 = v1_3;
  Lib_IntVector_Intrinsics_vec512 v2_4 = v2_3;
  Lib_IntVector_Intrinsics_vec512 v3_4 = v3_3;
  Lib_IntVector_Intrinsics_vec512 v4_4 = v4_3;
  Lib_IntVector_Intrinsics_vec512 v5_4 = v5_3;
  Lib_IntVector_Intrinsics_vec512 v6_4 = v6_3;
  Lib_IntVector_Intrinsics_vec512 v7_4 = v7_3;
  Lib_IntVector_Intrinsics_vec512
  v0_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v0_4, v2_4);
  Lib_IntVector_Intrinsics_vec512
  v2_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v0_4, v2_4);
  Lib_IntVector_Intrinsics_vec512
  v1_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v1_4, v3_4);
  Lib_IntVector_Intrinsics_vec512
  v3_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v1_4, v3_4);
  Lib_IntVector_Intrinsics_vec512
  v4_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v4_4, v6_4);
  Lib_IntVector_Intrinsics_vec512
  v6_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v4_4, v6_4);
  Lib_IntVector_Intrinsics_vec512
  v5_11 = Lib_IntVector_Intrinsics_vec512_interleave_low128(v5_4, v7_4);
  Lib_IntVector_Intrinsics_vec512
  v7_11 = Lib_IntVector_Intrinsics_vec512_interleave_high128(v5_4, v7_4);
  Lib_IntVector_Intrinsics_vec512 v0_12 = v0_11;
  Lib_IntVector_Intrinsics_vec512 v1_12 = v1_11;
  Lib_IntVector_Intrinsics_vec512 v2_12 = v2_11;
  Lib_IntVector_Intrinsics_vec512 v3_12 = v3_11;
  Lib_IntVector_Intrinsics_vec512 v4_12 = v4_11;
  Lib_IntVector_Intrinsics_vec512 v5_12 = v5_11;
  Lib_IntVector_Intrinsics_vec512 v6_12 = v6_11;
  Lib_IntVector_Intrinsics_vec512 v7_12 = v7_11;
  Lib_IntVector_Intrinsics_vec512
  v0_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v0_12, v4_12);
  Lib_IntVector_Intrinsics_vec512
  v4_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v0_12, v4_12);
  Lib_IntVector_Intrinsics_vec512
  v1_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v1_12, v5_12);
  Lib_IntVector_Intrinsics_vec512
  v5_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v1_12, v5_12);
  Lib_IntVector_Intrinsics_vec512
  v2_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v2_12, v6_12);
  Lib_IntVector_Intrinsics_vec512
  v6_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v2_12, v6_12);
  Lib_IntVector_Intrinsics_vec512
  v3_21 = Lib_IntVector_Intrinsics_vec512_interleave_low256(v3_12, v7_12);
  Lib_IntVector_Intrinsics_vec512
  v7_21 = Lib_IntVector_Intrinsics_vec512_interleave_high256(v3_12, v7_12);
  Lib_IntVector_Intrinsics_vec512 v0_22 = v0_21;
  Lib_IntVector_Intrinsics_vec512 v1_22 = v1_21;
  Lib_IntVector_Intrinsics_vec512 v2_22 = v2_21;
  Lib_IntVector_Intrinsics_vec512 v3_22 = v3_21;
  Lib_IntVector_Intrinsics_vec512 v4_22 = v4_21;
  Lib_IntVector_Intrinsics_vec512 v5_22 = v5_21;
  Lib_IntVector_Intrinsics_vec512 v6_22 = v6_21;
  Lib_IntVector_Intrinsics_vec512 v7_22 = v7_21;
  Lib_IntVector_Intrinsics_vec512 ws8 = v0_22;
  Lib_IntVector_Intrinsics_vec512 ws9 = v1_22;
  Lib_IntVector_Intrinsics_vec512 ws10 = v2_22;
  Lib_IntVector_Intrinsics_vec512 ws11 = v3_22;
  Lib_IntVector_Intrinsics_vec512 ws12 = v4_22;
  Lib_IntVector_Intrinsics_vec512 ws13 = v5_22;
  Lib_IntVector_Intrinsics_vec512 ws14 = v6_22;
  Lib_IntVector_Intrinsics_vec512 ws15 = v7_22;
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
              Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_and(e0, f0),
                Lib_IntVector_Intrinsics_vec512_and(Lib_IntVector_Intrinsics_vec512_lognot(e0), g0))),
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
            Lib_IntVector_Intrinsics_vec512_xor(Lib_IntVector_Intrinsics_vec512_and(a0, c0),
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
    if (i0 < (uint32_t)5U - (uint32_t)1U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
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
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec512 *os = hash;
    Lib_IntVector_Intrinsics_vec512
    x = Lib_IntVector_Intrinsics_vec512_add64(hash[i], hash_old[i]);
    os[i] = x;
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
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
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
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec512), (uint32_t)8U);
  Lib_IntVector_Intrinsics_vec512 st[8U];
  for (uint32_t _i = 0U; _i < (uint32_t)8U; ++_i)
    st[_i] = Lib_IntVector_Intrinsics_vec512_zero;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    Lib_IntVector_Intrinsics_vec512 *os = st;
    uint64_t hi = Hacl_Impl_SHA2_Generic_h512[i];
    Lib_IntVector_Intrinsics_vec512 x = Lib_IntVector_Intrinsics_vec512_load64(hi);
    os[i] = x;
  }
  uint32_t rem = len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)len);
  uint32_t blocks0 = len / (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < blocks0; i++)
  {
    uint8_t *b71 = ib.snd.snd.snd.snd.snd.snd.snd;
    uint8_t *b61 = ib.snd.snd.snd.snd.snd.snd.fst;
    uint8_t *b51 = ib.snd.snd.snd.snd.snd.fst;
    uint8_t *b41 = ib.snd.snd.snd.snd.fst;
    uint8_t *b31 = ib.snd.snd.snd.fst;
    uint8_t *b21 = ib.snd.snd.fst;
    uint8_t *b11 = ib.snd.fst;
    uint8_t *b01 = ib.fst;
    uint8_t *bl0 = b01 + i * (uint32_t)128U;
    uint8_t *bl1 = b11 + i * (uint32_t)128U;
    uint8_t *bl2 = b21 + i * (uint32_t)128U;
    uint8_t *bl3 = b31 + i * (uint32_t)128U;
    uint8_t *bl4 = b41 + i * (uint32_t)128U;
    uint8_t *bl5 = b51 + i * (uint32_t)128U;
    uint8_t *bl6 = b61 + i * (uint32_t)128U;
    uint8_t *bl7 = b71 + i * (uint32_t)128U;
    K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
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
    sha512_update8(mb, st);
  }
  uint32_t rem1 = len % (uint32_t)128U;
  uint8_t *b71 = ib.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b610 = ib.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b510 = ib.snd.snd.snd.snd.snd.fst;
  uint8_t *b410 = ib.snd.snd.snd.snd.fst;
  uint8_t *b310 = ib.snd.snd.snd.fst;
  uint8_t *b210 = ib.snd.snd.fst;
  uint8_t *b110 = ib.snd.fst;
  uint8_t *b010 = ib.fst;
  uint8_t *bl0 = b010 + len - rem1;
  uint8_t *bl1 = b110 + len - rem1;
  uint8_t *bl2 = b210 + len - rem1;
  uint8_t *bl3 = b310 + len - rem1;
  uint8_t *bl4 = b410 + len - rem1;
  uint8_t *bl5 = b510 + len - rem1;
  uint8_t *bl6 = b610 + len - rem1;
  uint8_t *bl7 = b71 + len - rem1;
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
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
  if (rem + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)128U;
  uint8_t last[2048U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(len_, (uint32_t)3U);
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b710 = lb.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b611 = lb.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b511 = lb.snd.snd.snd.snd.snd.fst;
  uint8_t *b411 = lb.snd.snd.snd.snd.fst;
  uint8_t *b311 = lb.snd.snd.snd.fst;
  uint8_t *b211 = lb.snd.snd.fst;
  uint8_t *b111 = lb.snd.fst;
  uint8_t *b011 = lb.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)256U;
  uint8_t *last2 = last + (uint32_t)512U;
  uint8_t *last3 = last + (uint32_t)768U;
  uint8_t *last4 = last + (uint32_t)1024U;
  uint8_t *last5 = last + (uint32_t)1280U;
  uint8_t *last6 = last + (uint32_t)1536U;
  uint8_t *last7 = last + (uint32_t)1792U;
  memcpy(last00, b011, rem * sizeof (b011[0U]));
  last00[rem] = (uint8_t)0x80U;
  memcpy(last00 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut = { .fst = last010, .snd = last110 };
  uint8_t *l00 = scrut.fst;
  uint8_t *l01 = scrut.snd;
  memcpy(last10, b111, rem * sizeof (b111[0U]));
  last10[rem] = (uint8_t)0x80U;
  memcpy(last10 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut0 = { .fst = last011, .snd = last111 };
  uint8_t *l10 = scrut0.fst;
  uint8_t *l11 = scrut0.snd;
  memcpy(last2, b211, rem * sizeof (b211[0U]));
  last2[rem] = (uint8_t)0x80U;
  memcpy(last2 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut1 = { .fst = last012, .snd = last112 };
  uint8_t *l20 = scrut1.fst;
  uint8_t *l21 = scrut1.snd;
  memcpy(last3, b311, rem * sizeof (b311[0U]));
  last3[rem] = (uint8_t)0x80U;
  memcpy(last3 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last013 = last3;
  uint8_t *last113 = last3 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut2 = { .fst = last013, .snd = last113 };
  uint8_t *l30 = scrut2.fst;
  uint8_t *l31 = scrut2.snd;
  memcpy(last4, b411, rem * sizeof (b411[0U]));
  last4[rem] = (uint8_t)0x80U;
  memcpy(last4 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last014 = last4;
  uint8_t *last114 = last4 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut3 = { .fst = last014, .snd = last114 };
  uint8_t *l40 = scrut3.fst;
  uint8_t *l41 = scrut3.snd;
  memcpy(last5, b511, rem * sizeof (b511[0U]));
  last5[rem] = (uint8_t)0x80U;
  memcpy(last5 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last015 = last5;
  uint8_t *last115 = last5 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut4 = { .fst = last015, .snd = last115 };
  uint8_t *l50 = scrut4.fst;
  uint8_t *l51 = scrut4.snd;
  memcpy(last6, b611, rem * sizeof (b611[0U]));
  last6[rem] = (uint8_t)0x80U;
  memcpy(last6 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last016 = last6;
  uint8_t *last116 = last6 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut5 = { .fst = last016, .snd = last116 };
  uint8_t *l60 = scrut5.fst;
  uint8_t *l61 = scrut5.snd;
  memcpy(last7, b710, rem * sizeof (b710[0U]));
  last7[rem] = (uint8_t)0x80U;
  memcpy(last7 + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (totlen_buf[0U]));
  uint8_t *last01 = last7;
  uint8_t *last11 = last7 + (uint32_t)128U;
  K____uint8_t___uint8_t_ scrut6 = { .fst = last01, .snd = last11 };
  uint8_t *l70 = scrut6.fst;
  uint8_t *l71 = scrut6.snd;
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
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
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
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
  K___K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  scrut7 = { .fst = mb0, .snd = mb1 };
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  last0 = scrut7.fst;
  K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
  last1 = scrut7.snd;
  sha512_update8(last0, st);
  if (blocks > (uint32_t)1U)
  {
    sha512_update8(last1, st);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)8U * (uint32_t)8U * (uint32_t)8U);
  uint8_t hbuf[(uint32_t)8U * (uint32_t)8U * (uint32_t)8U];
  memset(hbuf, 0U, (uint32_t)8U * (uint32_t)8U * (uint32_t)8U * sizeof (hbuf[0U]));
  Lib_IntVector_Intrinsics_vec512 v0 = st[0U];
  Lib_IntVector_Intrinsics_vec512 v1 = st[1U];
  Lib_IntVector_Intrinsics_vec512 v2 = st[2U];
  Lib_IntVector_Intrinsics_vec512 v3 = st[3U];
  Lib_IntVector_Intrinsics_vec512 v4 = st[4U];
  Lib_IntVector_Intrinsics_vec512 v5 = st[5U];
  Lib_IntVector_Intrinsics_vec512 v6 = st[6U];
  Lib_IntVector_Intrinsics_vec512 v7 = st[7U];
  Lib_IntVector_Intrinsics_vec512 v0_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v0, v1);
  Lib_IntVector_Intrinsics_vec512
  v1_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v0, v1);
  Lib_IntVector_Intrinsics_vec512 v2_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v2, v3);
  Lib_IntVector_Intrinsics_vec512
  v3_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v2, v3);
  Lib_IntVector_Intrinsics_vec512 v4_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v4, v5);
  Lib_IntVector_Intrinsics_vec512
  v5_ = Lib_IntVector_Intrinsics_vec512_interleave_high64(v4, v5);
  Lib_IntVector_Intrinsics_vec512 v6_ = Lib_IntVector_Intrinsics_vec512_interleave_low64(v6, v7);
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
    Lib_IntVector_Intrinsics_vec512_store64_be(hbuf + i * (uint32_t)64U, st[i]);
  }
  uint8_t *b711 = rb.snd.snd.snd.snd.snd.snd.snd;
  uint8_t *b61 = rb.snd.snd.snd.snd.snd.snd.fst;
  uint8_t *b51 = rb.snd.snd.snd.snd.snd.fst;
  uint8_t *b41 = rb.snd.snd.snd.snd.fst;
  uint8_t *b31 = rb.snd.snd.snd.fst;
  uint8_t *b21 = rb.snd.snd.fst;
  uint8_t *b11 = rb.snd.fst;
  uint8_t *b01 = rb.fst;
  memcpy(b01, hbuf, (uint32_t)64U * sizeof (hbuf[0U]));
  memcpy(b11, hbuf + (uint32_t)64U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)64U)[0U]));
  memcpy(b21, hbuf + (uint32_t)128U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)128U)[0U]));
  memcpy(b31, hbuf + (uint32_t)192U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)192U)[0U]));
  memcpy(b41, hbuf + (uint32_t)256U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)256U)[0U]));
  memcpy(b51, hbuf + (uint32_t)320U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)320U)[0U]));
  memcpy(b61, hbuf + (uint32_t)384U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)384U)[0U]));
  memcpy(b711, hbuf + (uint32_t)448U, (uint32_t)64U * sizeof ((hbuf + (uint32_t)448U)[0U]));
}

