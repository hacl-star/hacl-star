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


#include "Hacl_SHA2_Vec128.h"

#include "internal/Hacl_SHA2_Vec256.h"
#include "libintvector.h"
static inline void
sha224_update4(
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ block,
  Lib_IntVector_Intrinsics_vec128 *hash
)
{
  Lib_IntVector_Intrinsics_vec128 hash_old[8U];
  {
    uint32_t _i;
    for (_i = 0U; _i < (uint32_t)8U; ++_i)
      hash_old[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec128 ws[16U];
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)16U; ++_i)
        ws[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    }
    {
      uint8_t *b3;
      uint8_t *b2;
      uint8_t *b10;
      uint8_t *b00;
      Lib_IntVector_Intrinsics_vec128 v00;
      Lib_IntVector_Intrinsics_vec128 v10;
      Lib_IntVector_Intrinsics_vec128 v20;
      Lib_IntVector_Intrinsics_vec128 v30;
      Lib_IntVector_Intrinsics_vec128 v0_;
      Lib_IntVector_Intrinsics_vec128 v1_;
      Lib_IntVector_Intrinsics_vec128 v2_;
      Lib_IntVector_Intrinsics_vec128 v3_;
      Lib_IntVector_Intrinsics_vec128 v0__;
      Lib_IntVector_Intrinsics_vec128 v1__;
      Lib_IntVector_Intrinsics_vec128 v2__;
      Lib_IntVector_Intrinsics_vec128 v3__;
      Lib_IntVector_Intrinsics_vec128 v0__0;
      Lib_IntVector_Intrinsics_vec128 v2__0;
      Lib_IntVector_Intrinsics_vec128 v1__0;
      Lib_IntVector_Intrinsics_vec128 v3__0;
      Lib_IntVector_Intrinsics_vec128 ws0;
      Lib_IntVector_Intrinsics_vec128 ws1;
      Lib_IntVector_Intrinsics_vec128 ws2;
      Lib_IntVector_Intrinsics_vec128 ws3;
      Lib_IntVector_Intrinsics_vec128 v01;
      Lib_IntVector_Intrinsics_vec128 v11;
      Lib_IntVector_Intrinsics_vec128 v21;
      Lib_IntVector_Intrinsics_vec128 v31;
      Lib_IntVector_Intrinsics_vec128 v0_0;
      Lib_IntVector_Intrinsics_vec128 v1_0;
      Lib_IntVector_Intrinsics_vec128 v2_0;
      Lib_IntVector_Intrinsics_vec128 v3_0;
      Lib_IntVector_Intrinsics_vec128 v0__1;
      Lib_IntVector_Intrinsics_vec128 v1__1;
      Lib_IntVector_Intrinsics_vec128 v2__1;
      Lib_IntVector_Intrinsics_vec128 v3__1;
      Lib_IntVector_Intrinsics_vec128 v0__2;
      Lib_IntVector_Intrinsics_vec128 v2__2;
      Lib_IntVector_Intrinsics_vec128 v1__2;
      Lib_IntVector_Intrinsics_vec128 v3__2;
      Lib_IntVector_Intrinsics_vec128 ws4;
      Lib_IntVector_Intrinsics_vec128 ws5;
      Lib_IntVector_Intrinsics_vec128 ws6;
      Lib_IntVector_Intrinsics_vec128 ws7;
      Lib_IntVector_Intrinsics_vec128 v02;
      Lib_IntVector_Intrinsics_vec128 v12;
      Lib_IntVector_Intrinsics_vec128 v22;
      Lib_IntVector_Intrinsics_vec128 v32;
      Lib_IntVector_Intrinsics_vec128 v0_1;
      Lib_IntVector_Intrinsics_vec128 v1_1;
      Lib_IntVector_Intrinsics_vec128 v2_1;
      Lib_IntVector_Intrinsics_vec128 v3_1;
      Lib_IntVector_Intrinsics_vec128 v0__3;
      Lib_IntVector_Intrinsics_vec128 v1__3;
      Lib_IntVector_Intrinsics_vec128 v2__3;
      Lib_IntVector_Intrinsics_vec128 v3__3;
      Lib_IntVector_Intrinsics_vec128 v0__4;
      Lib_IntVector_Intrinsics_vec128 v2__4;
      Lib_IntVector_Intrinsics_vec128 v1__4;
      Lib_IntVector_Intrinsics_vec128 v3__4;
      Lib_IntVector_Intrinsics_vec128 ws8;
      Lib_IntVector_Intrinsics_vec128 ws9;
      Lib_IntVector_Intrinsics_vec128 ws10;
      Lib_IntVector_Intrinsics_vec128 ws11;
      Lib_IntVector_Intrinsics_vec128 v0;
      Lib_IntVector_Intrinsics_vec128 v1;
      Lib_IntVector_Intrinsics_vec128 v2;
      Lib_IntVector_Intrinsics_vec128 v3;
      Lib_IntVector_Intrinsics_vec128 v0_2;
      Lib_IntVector_Intrinsics_vec128 v1_2;
      Lib_IntVector_Intrinsics_vec128 v2_2;
      Lib_IntVector_Intrinsics_vec128 v3_2;
      Lib_IntVector_Intrinsics_vec128 v0__5;
      Lib_IntVector_Intrinsics_vec128 v1__5;
      Lib_IntVector_Intrinsics_vec128 v2__5;
      Lib_IntVector_Intrinsics_vec128 v3__5;
      Lib_IntVector_Intrinsics_vec128 v0__6;
      Lib_IntVector_Intrinsics_vec128 v2__6;
      Lib_IntVector_Intrinsics_vec128 v1__6;
      Lib_IntVector_Intrinsics_vec128 v3__6;
      Lib_IntVector_Intrinsics_vec128 ws12;
      Lib_IntVector_Intrinsics_vec128 ws13;
      Lib_IntVector_Intrinsics_vec128 ws14;
      Lib_IntVector_Intrinsics_vec128 ws15;
      memcpy(hash_old, hash, (uint32_t)8U * sizeof (Lib_IntVector_Intrinsics_vec128));
      b3 = block.snd.snd.snd;
      b2 = block.snd.snd.fst;
      b10 = block.snd.fst;
      b00 = block.fst;
      ws[0U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00);
      ws[1U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10);
      ws[2U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2);
      ws[3U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3);
      ws[4U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + (uint32_t)16U);
      ws[5U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + (uint32_t)16U);
      ws[6U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + (uint32_t)16U);
      ws[7U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + (uint32_t)16U);
      ws[8U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + (uint32_t)32U);
      ws[9U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + (uint32_t)32U);
      ws[10U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + (uint32_t)32U);
      ws[11U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + (uint32_t)32U);
      ws[12U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + (uint32_t)48U);
      ws[13U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + (uint32_t)48U);
      ws[14U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + (uint32_t)48U);
      ws[15U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + (uint32_t)48U);
      v00 = ws[0U];
      v10 = ws[1U];
      v20 = ws[2U];
      v30 = ws[3U];
      v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v10);
      v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v10);
      v2_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v20, v30);
      v3_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v20, v30);
      v0__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_, v2_);
      v1__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_, v2_);
      v2__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_, v3_);
      v3__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_, v3_);
      v0__0 = v0__;
      v2__0 = v2__;
      v1__0 = v1__;
      v3__0 = v3__;
      ws0 = v0__0;
      ws1 = v1__0;
      ws2 = v2__0;
      ws3 = v3__0;
      v01 = ws[4U];
      v11 = ws[5U];
      v21 = ws[6U];
      v31 = ws[7U];
      v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v11);
      v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v11);
      v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
      v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
      v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
      v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
      v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
      v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
      v0__2 = v0__1;
      v2__2 = v2__1;
      v1__2 = v1__1;
      v3__2 = v3__1;
      ws4 = v0__2;
      ws5 = v1__2;
      ws6 = v2__2;
      ws7 = v3__2;
      v02 = ws[8U];
      v12 = ws[9U];
      v22 = ws[10U];
      v32 = ws[11U];
      v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v02, v12);
      v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v02, v12);
      v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v22, v32);
      v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v22, v32);
      v0__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
      v1__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
      v2__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
      v3__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
      v0__4 = v0__3;
      v2__4 = v2__3;
      v1__4 = v1__3;
      v3__4 = v3__3;
      ws8 = v0__4;
      ws9 = v1__4;
      ws10 = v2__4;
      ws11 = v3__4;
      v0 = ws[12U];
      v1 = ws[13U];
      v2 = ws[14U];
      v3 = ws[15U];
      v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v0, v1);
      v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v0, v1);
      v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v2, v3);
      v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v2, v3);
      v0__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
      v1__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
      v2__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
      v3__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
      v0__6 = v0__5;
      v2__6 = v2__5;
      v1__6 = v1__5;
      v3__6 = v3__5;
      ws12 = v0__6;
      ws13 = v1__6;
      ws14 = v2__6;
      ws15 = v3__6;
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
        for (i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
        {
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
            {
              uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
              Lib_IntVector_Intrinsics_vec128 ws_t = ws[i];
              Lib_IntVector_Intrinsics_vec128 a0 = hash[0U];
              Lib_IntVector_Intrinsics_vec128 b0 = hash[1U];
              Lib_IntVector_Intrinsics_vec128 c0 = hash[2U];
              Lib_IntVector_Intrinsics_vec128 d0 = hash[3U];
              Lib_IntVector_Intrinsics_vec128 e0 = hash[4U];
              Lib_IntVector_Intrinsics_vec128 f0 = hash[5U];
              Lib_IntVector_Intrinsics_vec128 g0 = hash[6U];
              Lib_IntVector_Intrinsics_vec128 h02 = hash[7U];
              Lib_IntVector_Intrinsics_vec128 k_e_t = Lib_IntVector_Intrinsics_vec128_load32(k_t);
              Lib_IntVector_Intrinsics_vec128
              t1 =
                Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(h02,
                        Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(e0,
                            (uint32_t)6U),
                          Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(e0,
                              (uint32_t)11U),
                            Lib_IntVector_Intrinsics_vec128_rotate_right32(e0, (uint32_t)25U)))),
                      Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(e0,
                          f0),
                        Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_lognot(e0),
                          g0))),
                    k_e_t),
                  ws_t);
              Lib_IntVector_Intrinsics_vec128
              t2 =
                Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
                      (uint32_t)2U),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
                        (uint32_t)13U),
                      Lib_IntVector_Intrinsics_vec128_rotate_right32(a0, (uint32_t)22U))),
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(a0, b0),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(a0, c0),
                      Lib_IntVector_Intrinsics_vec128_and(b0, c0))));
              Lib_IntVector_Intrinsics_vec128 a1 = Lib_IntVector_Intrinsics_vec128_add32(t1, t2);
              Lib_IntVector_Intrinsics_vec128 b1 = a0;
              Lib_IntVector_Intrinsics_vec128 c1 = b0;
              Lib_IntVector_Intrinsics_vec128 d1 = c0;
              Lib_IntVector_Intrinsics_vec128 e1 = Lib_IntVector_Intrinsics_vec128_add32(d0, t1);
              Lib_IntVector_Intrinsics_vec128 f1 = e0;
              Lib_IntVector_Intrinsics_vec128 g1 = f0;
              Lib_IntVector_Intrinsics_vec128 h12 = g0;
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
          if (i0 < (uint32_t)4U - (uint32_t)1U)
          {
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                Lib_IntVector_Intrinsics_vec128 t16 = ws[i];
                Lib_IntVector_Intrinsics_vec128 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
                Lib_IntVector_Intrinsics_vec128 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
                Lib_IntVector_Intrinsics_vec128 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
                Lib_IntVector_Intrinsics_vec128
                s1 =
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
                      (uint32_t)17U),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
                        (uint32_t)19U),
                      Lib_IntVector_Intrinsics_vec128_shift_right32(t2, (uint32_t)10U)));
                Lib_IntVector_Intrinsics_vec128
                s0 =
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
                      (uint32_t)7U),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
                        (uint32_t)18U),
                      Lib_IntVector_Intrinsics_vec128_shift_right32(t15, (uint32_t)3U)));
                ws[i] =
                  Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(s1,
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
          Lib_IntVector_Intrinsics_vec128 *os = hash;
          Lib_IntVector_Intrinsics_vec128
          x = Lib_IntVector_Intrinsics_vec128_add32(hash[i], hash_old[i]);
          os[i] = x;
        }
      }
    }
  }
}

void
Hacl_SHA2_Vec128_sha224_4(
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
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ ib;
  ib.fst = input0;
  ib.snd.fst = input1;
  ib.snd.snd.fst = input2;
  ib.snd.snd.snd = input3;
  {
    K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ rb;
    rb.fst = dst0;
    rb.snd.fst = dst1;
    rb.snd.snd.fst = dst2;
    rb.snd.snd.snd = dst3;
    {
      Lib_IntVector_Intrinsics_vec128 st[8U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)8U; ++_i)
          st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
      }
      {
        uint32_t rem;
        uint64_t len_;
        uint32_t blocks0;
        uint32_t rem1;
        uint8_t *b30;
        uint8_t *b20;
        uint8_t *b10;
        uint8_t *b00;
        uint8_t *bl0;
        uint8_t *bl10;
        uint8_t *bl20;
        uint8_t *bl30;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
          {
            Lib_IntVector_Intrinsics_vec128 *os = st;
            uint32_t hi = Hacl_Impl_SHA2_Generic_h224[i];
            Lib_IntVector_Intrinsics_vec128 x = Lib_IntVector_Intrinsics_vec128_load32(hi);
            os[i] = x;
          }
        }
        rem = input_len % (uint32_t)64U;
        len_ = (uint64_t)input_len;
        blocks0 = input_len / (uint32_t)64U;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < blocks0; i++)
          {
            uint8_t *b3 = ib.snd.snd.snd;
            uint8_t *b2 = ib.snd.snd.fst;
            uint8_t *b1 = ib.snd.fst;
            uint8_t *b0 = ib.fst;
            uint8_t *bl00 = b0 + i * (uint32_t)64U;
            uint8_t *bl1 = b1 + i * (uint32_t)64U;
            uint8_t *bl2 = b2 + i * (uint32_t)64U;
            uint8_t *bl3 = b3 + i * (uint32_t)64U;
            K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ lit;
            lit.fst = bl00;
            lit.snd.fst = bl1;
            lit.snd.snd.fst = bl2;
            lit.snd.snd.snd = bl3;
            {
              K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ mb = lit;
              sha224_update4(mb, st);
            }
          }
        }
        rem1 = input_len % (uint32_t)64U;
        b30 = ib.snd.snd.snd;
        b20 = ib.snd.snd.fst;
        b10 = ib.snd.fst;
        b00 = ib.fst;
        bl0 = b00 + input_len - rem1;
        bl10 = b10 + input_len - rem1;
        bl20 = b20 + input_len - rem1;
        bl30 = b30 + input_len - rem1;
        {
          K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ lit0;
          K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ lb;
          lit0.fst = bl0;
          lit0.snd.fst = bl10;
          lit0.snd.snd.fst = bl20;
          lit0.snd.snd.snd = bl30;
          lb = lit0;
          {
            uint32_t blocks;
            if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
            {
              blocks = (uint32_t)1U;
            }
            else
            {
              blocks = (uint32_t)2U;
            }
            {
              uint32_t fin = blocks * (uint32_t)64U;
              uint8_t last[512U] = { 0U };
              uint8_t totlen_buf[8U] = { 0U };
              uint64_t total_len_bits = len_ << (uint32_t)3U;
              uint8_t *b31;
              uint8_t *b21;
              uint8_t *b11;
              uint8_t *b01;
              uint8_t *last00;
              uint8_t *last10;
              uint8_t *last2;
              uint8_t *last3;
              uint8_t *last010;
              uint8_t *last110;
              store64_be(totlen_buf, total_len_bits);
              b31 = lb.snd.snd.snd;
              b21 = lb.snd.snd.fst;
              b11 = lb.snd.fst;
              b01 = lb.fst;
              last00 = last;
              last10 = last + (uint32_t)128U;
              last2 = last + (uint32_t)256U;
              last3 = last + (uint32_t)384U;
              memcpy(last00, b01, rem * sizeof (uint8_t));
              last00[rem] = (uint8_t)0x80U;
              memcpy(last00 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
              last010 = last00;
              last110 = last00 + (uint32_t)64U;
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
                memcpy(last10, b11, rem * sizeof (uint8_t));
                last10[rem] = (uint8_t)0x80U;
                memcpy(last10 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
                last011 = last10;
                last111 = last10 + (uint32_t)64U;
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
                  memcpy(last2, b21, rem * sizeof (uint8_t));
                  last2[rem] = (uint8_t)0x80U;
                  memcpy(last2 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
                  last012 = last2;
                  last112 = last2 + (uint32_t)64U;
                  {
                    K____uint8_t___uint8_t_ lit3;
                    K____uint8_t___uint8_t_ scrut2;
                    uint8_t *l20;
                    uint8_t *l21;
                    uint8_t *last01;
                    uint8_t *last11;
                    lit3.fst = last012;
                    lit3.snd = last112;
                    scrut2 = lit3;
                    l20 = scrut2.fst;
                    l21 = scrut2.snd;
                    memcpy(last3, b31, rem * sizeof (uint8_t));
                    last3[rem] = (uint8_t)0x80U;
                    memcpy(last3 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
                    last01 = last3;
                    last11 = last3 + (uint32_t)64U;
                    {
                      K____uint8_t___uint8_t_ lit4;
                      K____uint8_t___uint8_t_ scrut3;
                      uint8_t *l30;
                      uint8_t *l31;
                      lit4.fst = last01;
                      lit4.snd = last11;
                      scrut3 = lit4;
                      l30 = scrut3.fst;
                      l31 = scrut3.snd;
                      {
                        K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ mb0;
                        mb0.fst = l00;
                        mb0.snd.fst = l10;
                        mb0.snd.snd.fst = l20;
                        mb0.snd.snd.snd = l30;
                        {
                          K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ mb1;
                          mb1.fst = l01;
                          mb1.snd.fst = l11;
                          mb1.snd.snd.fst = l21;
                          mb1.snd.snd.snd = l31;
                          {
                            K___K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                            lit;
                            K___K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                            scrut;
                            K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last0;
                            K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last1;
                            lit.fst = mb0;
                            lit.snd = mb1;
                            scrut = lit;
                            last0 = scrut.fst;
                            last1 = scrut.snd;
                            sha224_update4(last0, st);
                            if (blocks > (uint32_t)1U)
                            {
                              sha224_update4(last1, st);
                            }
                            KRML_CHECK_SIZE(sizeof (uint8_t),
                              (uint32_t)4U * (uint32_t)8U * (uint32_t)4U);
                            {
                              uint8_t hbuf[(uint32_t)4U * (uint32_t)8U * (uint32_t)4U];
                              memset(hbuf,
                                0U,
                                (uint32_t)4U * (uint32_t)8U * (uint32_t)4U * sizeof (uint8_t));
                              {
                                Lib_IntVector_Intrinsics_vec128 v00 = st[0U];
                                Lib_IntVector_Intrinsics_vec128 v10 = st[1U];
                                Lib_IntVector_Intrinsics_vec128 v20 = st[2U];
                                Lib_IntVector_Intrinsics_vec128 v30 = st[3U];
                                Lib_IntVector_Intrinsics_vec128
                                v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v10);
                                Lib_IntVector_Intrinsics_vec128
                                v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v10);
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
                                Lib_IntVector_Intrinsics_vec128 v0__0 = v0__;
                                Lib_IntVector_Intrinsics_vec128 v2__0 = v2__;
                                Lib_IntVector_Intrinsics_vec128 v1__0 = v1__;
                                Lib_IntVector_Intrinsics_vec128 v3__0 = v3__;
                                Lib_IntVector_Intrinsics_vec128 st0_ = v0__0;
                                Lib_IntVector_Intrinsics_vec128 st1_ = v1__0;
                                Lib_IntVector_Intrinsics_vec128 st2_ = v2__0;
                                Lib_IntVector_Intrinsics_vec128 st3_ = v3__0;
                                Lib_IntVector_Intrinsics_vec128 v0 = st[4U];
                                Lib_IntVector_Intrinsics_vec128 v1 = st[5U];
                                Lib_IntVector_Intrinsics_vec128 v2 = st[6U];
                                Lib_IntVector_Intrinsics_vec128 v3 = st[7U];
                                Lib_IntVector_Intrinsics_vec128
                                v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v0, v1);
                                Lib_IntVector_Intrinsics_vec128
                                v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v0, v1);
                                Lib_IntVector_Intrinsics_vec128
                                v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v2, v3);
                                Lib_IntVector_Intrinsics_vec128
                                v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v2, v3);
                                Lib_IntVector_Intrinsics_vec128
                                v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
                                Lib_IntVector_Intrinsics_vec128
                                v1__1 =
                                  Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0,
                                    v2_0);
                                Lib_IntVector_Intrinsics_vec128
                                v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
                                Lib_IntVector_Intrinsics_vec128
                                v3__1 =
                                  Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0,
                                    v3_0);
                                Lib_IntVector_Intrinsics_vec128 v0__2 = v0__1;
                                Lib_IntVector_Intrinsics_vec128 v2__2 = v2__1;
                                Lib_IntVector_Intrinsics_vec128 v1__2 = v1__1;
                                Lib_IntVector_Intrinsics_vec128 v3__2 = v3__1;
                                Lib_IntVector_Intrinsics_vec128 st4_ = v0__2;
                                Lib_IntVector_Intrinsics_vec128 st5_ = v1__2;
                                Lib_IntVector_Intrinsics_vec128 st6_ = v2__2;
                                Lib_IntVector_Intrinsics_vec128 st7_ = v3__2;
                                uint8_t *b3;
                                uint8_t *b2;
                                uint8_t *b1;
                                uint8_t *b0;
                                st[0U] = st0_;
                                st[1U] = st4_;
                                st[2U] = st1_;
                                st[3U] = st5_;
                                st[4U] = st2_;
                                st[5U] = st6_;
                                st[6U] = st3_;
                                st[7U] = st7_;
                                {
                                  uint32_t i;
                                  for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
                                  {
                                    Lib_IntVector_Intrinsics_vec128_store32_be(hbuf
                                      + i * (uint32_t)16U,
                                      st[i]);
                                  }
                                }
                                b3 = rb.snd.snd.snd;
                                b2 = rb.snd.snd.fst;
                                b1 = rb.snd.fst;
                                b0 = rb.fst;
                                memcpy(b0, hbuf, (uint32_t)28U * sizeof (uint8_t));
                                memcpy(b1, hbuf + (uint32_t)32U, (uint32_t)28U * sizeof (uint8_t));
                                memcpy(b2, hbuf + (uint32_t)64U, (uint32_t)28U * sizeof (uint8_t));
                                memcpy(b3, hbuf + (uint32_t)96U, (uint32_t)28U * sizeof (uint8_t));
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

static inline void
sha256_update4(
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ block,
  Lib_IntVector_Intrinsics_vec128 *hash
)
{
  Lib_IntVector_Intrinsics_vec128 hash_old[8U];
  {
    uint32_t _i;
    for (_i = 0U; _i < (uint32_t)8U; ++_i)
      hash_old[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec128 ws[16U];
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)16U; ++_i)
        ws[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    }
    {
      uint8_t *b3;
      uint8_t *b2;
      uint8_t *b10;
      uint8_t *b00;
      Lib_IntVector_Intrinsics_vec128 v00;
      Lib_IntVector_Intrinsics_vec128 v10;
      Lib_IntVector_Intrinsics_vec128 v20;
      Lib_IntVector_Intrinsics_vec128 v30;
      Lib_IntVector_Intrinsics_vec128 v0_;
      Lib_IntVector_Intrinsics_vec128 v1_;
      Lib_IntVector_Intrinsics_vec128 v2_;
      Lib_IntVector_Intrinsics_vec128 v3_;
      Lib_IntVector_Intrinsics_vec128 v0__;
      Lib_IntVector_Intrinsics_vec128 v1__;
      Lib_IntVector_Intrinsics_vec128 v2__;
      Lib_IntVector_Intrinsics_vec128 v3__;
      Lib_IntVector_Intrinsics_vec128 v0__0;
      Lib_IntVector_Intrinsics_vec128 v2__0;
      Lib_IntVector_Intrinsics_vec128 v1__0;
      Lib_IntVector_Intrinsics_vec128 v3__0;
      Lib_IntVector_Intrinsics_vec128 ws0;
      Lib_IntVector_Intrinsics_vec128 ws1;
      Lib_IntVector_Intrinsics_vec128 ws2;
      Lib_IntVector_Intrinsics_vec128 ws3;
      Lib_IntVector_Intrinsics_vec128 v01;
      Lib_IntVector_Intrinsics_vec128 v11;
      Lib_IntVector_Intrinsics_vec128 v21;
      Lib_IntVector_Intrinsics_vec128 v31;
      Lib_IntVector_Intrinsics_vec128 v0_0;
      Lib_IntVector_Intrinsics_vec128 v1_0;
      Lib_IntVector_Intrinsics_vec128 v2_0;
      Lib_IntVector_Intrinsics_vec128 v3_0;
      Lib_IntVector_Intrinsics_vec128 v0__1;
      Lib_IntVector_Intrinsics_vec128 v1__1;
      Lib_IntVector_Intrinsics_vec128 v2__1;
      Lib_IntVector_Intrinsics_vec128 v3__1;
      Lib_IntVector_Intrinsics_vec128 v0__2;
      Lib_IntVector_Intrinsics_vec128 v2__2;
      Lib_IntVector_Intrinsics_vec128 v1__2;
      Lib_IntVector_Intrinsics_vec128 v3__2;
      Lib_IntVector_Intrinsics_vec128 ws4;
      Lib_IntVector_Intrinsics_vec128 ws5;
      Lib_IntVector_Intrinsics_vec128 ws6;
      Lib_IntVector_Intrinsics_vec128 ws7;
      Lib_IntVector_Intrinsics_vec128 v02;
      Lib_IntVector_Intrinsics_vec128 v12;
      Lib_IntVector_Intrinsics_vec128 v22;
      Lib_IntVector_Intrinsics_vec128 v32;
      Lib_IntVector_Intrinsics_vec128 v0_1;
      Lib_IntVector_Intrinsics_vec128 v1_1;
      Lib_IntVector_Intrinsics_vec128 v2_1;
      Lib_IntVector_Intrinsics_vec128 v3_1;
      Lib_IntVector_Intrinsics_vec128 v0__3;
      Lib_IntVector_Intrinsics_vec128 v1__3;
      Lib_IntVector_Intrinsics_vec128 v2__3;
      Lib_IntVector_Intrinsics_vec128 v3__3;
      Lib_IntVector_Intrinsics_vec128 v0__4;
      Lib_IntVector_Intrinsics_vec128 v2__4;
      Lib_IntVector_Intrinsics_vec128 v1__4;
      Lib_IntVector_Intrinsics_vec128 v3__4;
      Lib_IntVector_Intrinsics_vec128 ws8;
      Lib_IntVector_Intrinsics_vec128 ws9;
      Lib_IntVector_Intrinsics_vec128 ws10;
      Lib_IntVector_Intrinsics_vec128 ws11;
      Lib_IntVector_Intrinsics_vec128 v0;
      Lib_IntVector_Intrinsics_vec128 v1;
      Lib_IntVector_Intrinsics_vec128 v2;
      Lib_IntVector_Intrinsics_vec128 v3;
      Lib_IntVector_Intrinsics_vec128 v0_2;
      Lib_IntVector_Intrinsics_vec128 v1_2;
      Lib_IntVector_Intrinsics_vec128 v2_2;
      Lib_IntVector_Intrinsics_vec128 v3_2;
      Lib_IntVector_Intrinsics_vec128 v0__5;
      Lib_IntVector_Intrinsics_vec128 v1__5;
      Lib_IntVector_Intrinsics_vec128 v2__5;
      Lib_IntVector_Intrinsics_vec128 v3__5;
      Lib_IntVector_Intrinsics_vec128 v0__6;
      Lib_IntVector_Intrinsics_vec128 v2__6;
      Lib_IntVector_Intrinsics_vec128 v1__6;
      Lib_IntVector_Intrinsics_vec128 v3__6;
      Lib_IntVector_Intrinsics_vec128 ws12;
      Lib_IntVector_Intrinsics_vec128 ws13;
      Lib_IntVector_Intrinsics_vec128 ws14;
      Lib_IntVector_Intrinsics_vec128 ws15;
      memcpy(hash_old, hash, (uint32_t)8U * sizeof (Lib_IntVector_Intrinsics_vec128));
      b3 = block.snd.snd.snd;
      b2 = block.snd.snd.fst;
      b10 = block.snd.fst;
      b00 = block.fst;
      ws[0U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00);
      ws[1U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10);
      ws[2U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2);
      ws[3U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3);
      ws[4U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + (uint32_t)16U);
      ws[5U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + (uint32_t)16U);
      ws[6U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + (uint32_t)16U);
      ws[7U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + (uint32_t)16U);
      ws[8U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + (uint32_t)32U);
      ws[9U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + (uint32_t)32U);
      ws[10U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + (uint32_t)32U);
      ws[11U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + (uint32_t)32U);
      ws[12U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + (uint32_t)48U);
      ws[13U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + (uint32_t)48U);
      ws[14U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + (uint32_t)48U);
      ws[15U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + (uint32_t)48U);
      v00 = ws[0U];
      v10 = ws[1U];
      v20 = ws[2U];
      v30 = ws[3U];
      v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v10);
      v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v10);
      v2_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v20, v30);
      v3_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v20, v30);
      v0__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_, v2_);
      v1__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_, v2_);
      v2__ = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_, v3_);
      v3__ = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_, v3_);
      v0__0 = v0__;
      v2__0 = v2__;
      v1__0 = v1__;
      v3__0 = v3__;
      ws0 = v0__0;
      ws1 = v1__0;
      ws2 = v2__0;
      ws3 = v3__0;
      v01 = ws[4U];
      v11 = ws[5U];
      v21 = ws[6U];
      v31 = ws[7U];
      v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v11);
      v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v11);
      v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
      v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
      v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
      v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
      v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
      v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
      v0__2 = v0__1;
      v2__2 = v2__1;
      v1__2 = v1__1;
      v3__2 = v3__1;
      ws4 = v0__2;
      ws5 = v1__2;
      ws6 = v2__2;
      ws7 = v3__2;
      v02 = ws[8U];
      v12 = ws[9U];
      v22 = ws[10U];
      v32 = ws[11U];
      v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v02, v12);
      v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v02, v12);
      v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v22, v32);
      v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v22, v32);
      v0__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
      v1__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
      v2__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
      v3__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
      v0__4 = v0__3;
      v2__4 = v2__3;
      v1__4 = v1__3;
      v3__4 = v3__3;
      ws8 = v0__4;
      ws9 = v1__4;
      ws10 = v2__4;
      ws11 = v3__4;
      v0 = ws[12U];
      v1 = ws[13U];
      v2 = ws[14U];
      v3 = ws[15U];
      v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v0, v1);
      v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v0, v1);
      v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v2, v3);
      v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v2, v3);
      v0__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
      v1__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
      v2__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
      v3__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
      v0__6 = v0__5;
      v2__6 = v2__5;
      v1__6 = v1__5;
      v3__6 = v3__5;
      ws12 = v0__6;
      ws13 = v1__6;
      ws14 = v2__6;
      ws15 = v3__6;
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
        for (i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
        {
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
            {
              uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
              Lib_IntVector_Intrinsics_vec128 ws_t = ws[i];
              Lib_IntVector_Intrinsics_vec128 a0 = hash[0U];
              Lib_IntVector_Intrinsics_vec128 b0 = hash[1U];
              Lib_IntVector_Intrinsics_vec128 c0 = hash[2U];
              Lib_IntVector_Intrinsics_vec128 d0 = hash[3U];
              Lib_IntVector_Intrinsics_vec128 e0 = hash[4U];
              Lib_IntVector_Intrinsics_vec128 f0 = hash[5U];
              Lib_IntVector_Intrinsics_vec128 g0 = hash[6U];
              Lib_IntVector_Intrinsics_vec128 h02 = hash[7U];
              Lib_IntVector_Intrinsics_vec128 k_e_t = Lib_IntVector_Intrinsics_vec128_load32(k_t);
              Lib_IntVector_Intrinsics_vec128
              t1 =
                Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(h02,
                        Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(e0,
                            (uint32_t)6U),
                          Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(e0,
                              (uint32_t)11U),
                            Lib_IntVector_Intrinsics_vec128_rotate_right32(e0, (uint32_t)25U)))),
                      Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(e0,
                          f0),
                        Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_lognot(e0),
                          g0))),
                    k_e_t),
                  ws_t);
              Lib_IntVector_Intrinsics_vec128
              t2 =
                Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
                      (uint32_t)2U),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
                        (uint32_t)13U),
                      Lib_IntVector_Intrinsics_vec128_rotate_right32(a0, (uint32_t)22U))),
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(a0, b0),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(a0, c0),
                      Lib_IntVector_Intrinsics_vec128_and(b0, c0))));
              Lib_IntVector_Intrinsics_vec128 a1 = Lib_IntVector_Intrinsics_vec128_add32(t1, t2);
              Lib_IntVector_Intrinsics_vec128 b1 = a0;
              Lib_IntVector_Intrinsics_vec128 c1 = b0;
              Lib_IntVector_Intrinsics_vec128 d1 = c0;
              Lib_IntVector_Intrinsics_vec128 e1 = Lib_IntVector_Intrinsics_vec128_add32(d0, t1);
              Lib_IntVector_Intrinsics_vec128 f1 = e0;
              Lib_IntVector_Intrinsics_vec128 g1 = f0;
              Lib_IntVector_Intrinsics_vec128 h12 = g0;
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
          if (i0 < (uint32_t)4U - (uint32_t)1U)
          {
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                Lib_IntVector_Intrinsics_vec128 t16 = ws[i];
                Lib_IntVector_Intrinsics_vec128 t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
                Lib_IntVector_Intrinsics_vec128 t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
                Lib_IntVector_Intrinsics_vec128 t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
                Lib_IntVector_Intrinsics_vec128
                s1 =
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
                      (uint32_t)17U),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
                        (uint32_t)19U),
                      Lib_IntVector_Intrinsics_vec128_shift_right32(t2, (uint32_t)10U)));
                Lib_IntVector_Intrinsics_vec128
                s0 =
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
                      (uint32_t)7U),
                    Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
                        (uint32_t)18U),
                      Lib_IntVector_Intrinsics_vec128_shift_right32(t15, (uint32_t)3U)));
                ws[i] =
                  Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(s1,
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
          Lib_IntVector_Intrinsics_vec128 *os = hash;
          Lib_IntVector_Intrinsics_vec128
          x = Lib_IntVector_Intrinsics_vec128_add32(hash[i], hash_old[i]);
          os[i] = x;
        }
      }
    }
  }
}

void
Hacl_SHA2_Vec128_sha256_4(
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
  K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ ib;
  ib.fst = input0;
  ib.snd.fst = input1;
  ib.snd.snd.fst = input2;
  ib.snd.snd.snd = input3;
  {
    K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ rb;
    rb.fst = dst0;
    rb.snd.fst = dst1;
    rb.snd.snd.fst = dst2;
    rb.snd.snd.snd = dst3;
    {
      Lib_IntVector_Intrinsics_vec128 st[8U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)8U; ++_i)
          st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
      }
      {
        uint32_t rem;
        uint64_t len_;
        uint32_t blocks0;
        uint32_t rem1;
        uint8_t *b30;
        uint8_t *b20;
        uint8_t *b10;
        uint8_t *b00;
        uint8_t *bl0;
        uint8_t *bl10;
        uint8_t *bl20;
        uint8_t *bl30;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
          {
            Lib_IntVector_Intrinsics_vec128 *os = st;
            uint32_t hi = Hacl_Impl_SHA2_Generic_h256[i];
            Lib_IntVector_Intrinsics_vec128 x = Lib_IntVector_Intrinsics_vec128_load32(hi);
            os[i] = x;
          }
        }
        rem = input_len % (uint32_t)64U;
        len_ = (uint64_t)input_len;
        blocks0 = input_len / (uint32_t)64U;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < blocks0; i++)
          {
            uint8_t *b3 = ib.snd.snd.snd;
            uint8_t *b2 = ib.snd.snd.fst;
            uint8_t *b1 = ib.snd.fst;
            uint8_t *b0 = ib.fst;
            uint8_t *bl00 = b0 + i * (uint32_t)64U;
            uint8_t *bl1 = b1 + i * (uint32_t)64U;
            uint8_t *bl2 = b2 + i * (uint32_t)64U;
            uint8_t *bl3 = b3 + i * (uint32_t)64U;
            K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ lit;
            lit.fst = bl00;
            lit.snd.fst = bl1;
            lit.snd.snd.fst = bl2;
            lit.snd.snd.snd = bl3;
            {
              K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ mb = lit;
              sha256_update4(mb, st);
            }
          }
        }
        rem1 = input_len % (uint32_t)64U;
        b30 = ib.snd.snd.snd;
        b20 = ib.snd.snd.fst;
        b10 = ib.snd.fst;
        b00 = ib.fst;
        bl0 = b00 + input_len - rem1;
        bl10 = b10 + input_len - rem1;
        bl20 = b20 + input_len - rem1;
        bl30 = b30 + input_len - rem1;
        {
          K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ lit0;
          K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ lb;
          lit0.fst = bl0;
          lit0.snd.fst = bl10;
          lit0.snd.snd.fst = bl20;
          lit0.snd.snd.snd = bl30;
          lb = lit0;
          {
            uint32_t blocks;
            if (rem + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
            {
              blocks = (uint32_t)1U;
            }
            else
            {
              blocks = (uint32_t)2U;
            }
            {
              uint32_t fin = blocks * (uint32_t)64U;
              uint8_t last[512U] = { 0U };
              uint8_t totlen_buf[8U] = { 0U };
              uint64_t total_len_bits = len_ << (uint32_t)3U;
              uint8_t *b31;
              uint8_t *b21;
              uint8_t *b11;
              uint8_t *b01;
              uint8_t *last00;
              uint8_t *last10;
              uint8_t *last2;
              uint8_t *last3;
              uint8_t *last010;
              uint8_t *last110;
              store64_be(totlen_buf, total_len_bits);
              b31 = lb.snd.snd.snd;
              b21 = lb.snd.snd.fst;
              b11 = lb.snd.fst;
              b01 = lb.fst;
              last00 = last;
              last10 = last + (uint32_t)128U;
              last2 = last + (uint32_t)256U;
              last3 = last + (uint32_t)384U;
              memcpy(last00, b01, rem * sizeof (uint8_t));
              last00[rem] = (uint8_t)0x80U;
              memcpy(last00 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
              last010 = last00;
              last110 = last00 + (uint32_t)64U;
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
                memcpy(last10, b11, rem * sizeof (uint8_t));
                last10[rem] = (uint8_t)0x80U;
                memcpy(last10 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
                last011 = last10;
                last111 = last10 + (uint32_t)64U;
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
                  memcpy(last2, b21, rem * sizeof (uint8_t));
                  last2[rem] = (uint8_t)0x80U;
                  memcpy(last2 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
                  last012 = last2;
                  last112 = last2 + (uint32_t)64U;
                  {
                    K____uint8_t___uint8_t_ lit3;
                    K____uint8_t___uint8_t_ scrut2;
                    uint8_t *l20;
                    uint8_t *l21;
                    uint8_t *last01;
                    uint8_t *last11;
                    lit3.fst = last012;
                    lit3.snd = last112;
                    scrut2 = lit3;
                    l20 = scrut2.fst;
                    l21 = scrut2.snd;
                    memcpy(last3, b31, rem * sizeof (uint8_t));
                    last3[rem] = (uint8_t)0x80U;
                    memcpy(last3 + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
                    last01 = last3;
                    last11 = last3 + (uint32_t)64U;
                    {
                      K____uint8_t___uint8_t_ lit4;
                      K____uint8_t___uint8_t_ scrut3;
                      uint8_t *l30;
                      uint8_t *l31;
                      lit4.fst = last01;
                      lit4.snd = last11;
                      scrut3 = lit4;
                      l30 = scrut3.fst;
                      l31 = scrut3.snd;
                      {
                        K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ mb0;
                        mb0.fst = l00;
                        mb0.snd.fst = l10;
                        mb0.snd.snd.fst = l20;
                        mb0.snd.snd.snd = l30;
                        {
                          K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ mb1;
                          mb1.fst = l01;
                          mb1.snd.fst = l11;
                          mb1.snd.snd.fst = l21;
                          mb1.snd.snd.snd = l31;
                          {
                            K___K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                            lit;
                            K___K____uint8_t__K____uint8_t__K____uint8_t___uint8_t__K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_
                            scrut;
                            K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last0;
                            K____uint8_t__K____uint8_t__K____uint8_t___uint8_t_ last1;
                            lit.fst = mb0;
                            lit.snd = mb1;
                            scrut = lit;
                            last0 = scrut.fst;
                            last1 = scrut.snd;
                            sha256_update4(last0, st);
                            if (blocks > (uint32_t)1U)
                            {
                              sha256_update4(last1, st);
                            }
                            KRML_CHECK_SIZE(sizeof (uint8_t),
                              (uint32_t)4U * (uint32_t)8U * (uint32_t)4U);
                            {
                              uint8_t hbuf[(uint32_t)4U * (uint32_t)8U * (uint32_t)4U];
                              memset(hbuf,
                                0U,
                                (uint32_t)4U * (uint32_t)8U * (uint32_t)4U * sizeof (uint8_t));
                              {
                                Lib_IntVector_Intrinsics_vec128 v00 = st[0U];
                                Lib_IntVector_Intrinsics_vec128 v10 = st[1U];
                                Lib_IntVector_Intrinsics_vec128 v20 = st[2U];
                                Lib_IntVector_Intrinsics_vec128 v30 = st[3U];
                                Lib_IntVector_Intrinsics_vec128
                                v0_ = Lib_IntVector_Intrinsics_vec128_interleave_low32(v00, v10);
                                Lib_IntVector_Intrinsics_vec128
                                v1_ = Lib_IntVector_Intrinsics_vec128_interleave_high32(v00, v10);
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
                                Lib_IntVector_Intrinsics_vec128 v0__0 = v0__;
                                Lib_IntVector_Intrinsics_vec128 v2__0 = v2__;
                                Lib_IntVector_Intrinsics_vec128 v1__0 = v1__;
                                Lib_IntVector_Intrinsics_vec128 v3__0 = v3__;
                                Lib_IntVector_Intrinsics_vec128 st0_ = v0__0;
                                Lib_IntVector_Intrinsics_vec128 st1_ = v1__0;
                                Lib_IntVector_Intrinsics_vec128 st2_ = v2__0;
                                Lib_IntVector_Intrinsics_vec128 st3_ = v3__0;
                                Lib_IntVector_Intrinsics_vec128 v0 = st[4U];
                                Lib_IntVector_Intrinsics_vec128 v1 = st[5U];
                                Lib_IntVector_Intrinsics_vec128 v2 = st[6U];
                                Lib_IntVector_Intrinsics_vec128 v3 = st[7U];
                                Lib_IntVector_Intrinsics_vec128
                                v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v0, v1);
                                Lib_IntVector_Intrinsics_vec128
                                v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v0, v1);
                                Lib_IntVector_Intrinsics_vec128
                                v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v2, v3);
                                Lib_IntVector_Intrinsics_vec128
                                v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v2, v3);
                                Lib_IntVector_Intrinsics_vec128
                                v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
                                Lib_IntVector_Intrinsics_vec128
                                v1__1 =
                                  Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0,
                                    v2_0);
                                Lib_IntVector_Intrinsics_vec128
                                v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
                                Lib_IntVector_Intrinsics_vec128
                                v3__1 =
                                  Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0,
                                    v3_0);
                                Lib_IntVector_Intrinsics_vec128 v0__2 = v0__1;
                                Lib_IntVector_Intrinsics_vec128 v2__2 = v2__1;
                                Lib_IntVector_Intrinsics_vec128 v1__2 = v1__1;
                                Lib_IntVector_Intrinsics_vec128 v3__2 = v3__1;
                                Lib_IntVector_Intrinsics_vec128 st4_ = v0__2;
                                Lib_IntVector_Intrinsics_vec128 st5_ = v1__2;
                                Lib_IntVector_Intrinsics_vec128 st6_ = v2__2;
                                Lib_IntVector_Intrinsics_vec128 st7_ = v3__2;
                                uint8_t *b3;
                                uint8_t *b2;
                                uint8_t *b1;
                                uint8_t *b0;
                                st[0U] = st0_;
                                st[1U] = st4_;
                                st[2U] = st1_;
                                st[3U] = st5_;
                                st[4U] = st2_;
                                st[5U] = st6_;
                                st[6U] = st3_;
                                st[7U] = st7_;
                                {
                                  uint32_t i;
                                  for (i = (uint32_t)0U; i < (uint32_t)8U; i++)
                                  {
                                    Lib_IntVector_Intrinsics_vec128_store32_be(hbuf
                                      + i * (uint32_t)16U,
                                      st[i]);
                                  }
                                }
                                b3 = rb.snd.snd.snd;
                                b2 = rb.snd.snd.fst;
                                b1 = rb.snd.fst;
                                b0 = rb.fst;
                                memcpy(b0, hbuf, (uint32_t)32U * sizeof (uint8_t));
                                memcpy(b1, hbuf + (uint32_t)32U, (uint32_t)32U * sizeof (uint8_t));
                                memcpy(b2, hbuf + (uint32_t)64U, (uint32_t)32U * sizeof (uint8_t));
                                memcpy(b3, hbuf + (uint32_t)96U, (uint32_t)32U * sizeof (uint8_t));
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

