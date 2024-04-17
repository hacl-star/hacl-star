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


#include "Hacl_SHA2_Vec128.h"

#include "internal/Hacl_SHA2_Types.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "libintvector.h"

static inline void sha224_init4(Lib_IntVector_Intrinsics_vec128 *hash)
{
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    Lib_IntVector_Intrinsics_vec128 *os = hash;
    uint32_t hi = Hacl_Hash_SHA2_h224[i];
    Lib_IntVector_Intrinsics_vec128 x = Lib_IntVector_Intrinsics_vec128_load32(hi);
    os[i] = x;);
}

static inline void
sha224_update4(
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ b,
  Lib_IntVector_Intrinsics_vec128 *hash
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 hash_old[8U] KRML_POST_ALIGN(16) = { 0U };
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ws[16U] KRML_POST_ALIGN(16) = { 0U };
  memcpy(hash_old, hash, 8U * sizeof (Lib_IntVector_Intrinsics_vec128));
  uint8_t *b3 = b.snd.snd.snd;
  uint8_t *b2 = b.snd.snd.fst;
  uint8_t *b10 = b.snd.fst;
  uint8_t *b00 = b.fst;
  ws[0U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00);
  ws[1U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10);
  ws[2U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2);
  ws[3U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3);
  ws[4U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + 16U);
  ws[5U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + 16U);
  ws[6U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + 16U);
  ws[7U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + 16U);
  ws[8U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + 32U);
  ws[9U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + 32U);
  ws[10U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + 32U);
  ws[11U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + 32U);
  ws[12U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + 48U);
  ws[13U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + 48U);
  ws[14U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + 48U);
  ws[15U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + 48U);
  Lib_IntVector_Intrinsics_vec128 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec128 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec128 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec128 v30 = ws[3U];
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
  Lib_IntVector_Intrinsics_vec128 ws0 = v0__0;
  Lib_IntVector_Intrinsics_vec128 ws1 = v1__0;
  Lib_IntVector_Intrinsics_vec128 ws2 = v2__0;
  Lib_IntVector_Intrinsics_vec128 ws3 = v3__0;
  Lib_IntVector_Intrinsics_vec128 v01 = ws[4U];
  Lib_IntVector_Intrinsics_vec128 v11 = ws[5U];
  Lib_IntVector_Intrinsics_vec128 v21 = ws[6U];
  Lib_IntVector_Intrinsics_vec128 v31 = ws[7U];
  Lib_IntVector_Intrinsics_vec128
  v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v11);
  Lib_IntVector_Intrinsics_vec128
  v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v11);
  Lib_IntVector_Intrinsics_vec128
  v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
  Lib_IntVector_Intrinsics_vec128
  v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
  Lib_IntVector_Intrinsics_vec128
  v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec128
  v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec128
  v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128
  v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128 v0__2 = v0__1;
  Lib_IntVector_Intrinsics_vec128 v2__2 = v2__1;
  Lib_IntVector_Intrinsics_vec128 v1__2 = v1__1;
  Lib_IntVector_Intrinsics_vec128 v3__2 = v3__1;
  Lib_IntVector_Intrinsics_vec128 ws4 = v0__2;
  Lib_IntVector_Intrinsics_vec128 ws5 = v1__2;
  Lib_IntVector_Intrinsics_vec128 ws6 = v2__2;
  Lib_IntVector_Intrinsics_vec128 ws7 = v3__2;
  Lib_IntVector_Intrinsics_vec128 v02 = ws[8U];
  Lib_IntVector_Intrinsics_vec128 v12 = ws[9U];
  Lib_IntVector_Intrinsics_vec128 v22 = ws[10U];
  Lib_IntVector_Intrinsics_vec128 v32 = ws[11U];
  Lib_IntVector_Intrinsics_vec128
  v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v02, v12);
  Lib_IntVector_Intrinsics_vec128
  v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v02, v12);
  Lib_IntVector_Intrinsics_vec128
  v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v22, v32);
  Lib_IntVector_Intrinsics_vec128
  v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v22, v32);
  Lib_IntVector_Intrinsics_vec128
  v0__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec128
  v1__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec128
  v2__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec128
  v3__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec128 v0__4 = v0__3;
  Lib_IntVector_Intrinsics_vec128 v2__4 = v2__3;
  Lib_IntVector_Intrinsics_vec128 v1__4 = v1__3;
  Lib_IntVector_Intrinsics_vec128 v3__4 = v3__3;
  Lib_IntVector_Intrinsics_vec128 ws8 = v0__4;
  Lib_IntVector_Intrinsics_vec128 ws9 = v1__4;
  Lib_IntVector_Intrinsics_vec128 ws10 = v2__4;
  Lib_IntVector_Intrinsics_vec128 ws11 = v3__4;
  Lib_IntVector_Intrinsics_vec128 v0 = ws[12U];
  Lib_IntVector_Intrinsics_vec128 v1 = ws[13U];
  Lib_IntVector_Intrinsics_vec128 v2 = ws[14U];
  Lib_IntVector_Intrinsics_vec128 v3 = ws[15U];
  Lib_IntVector_Intrinsics_vec128
  v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v0, v1);
  Lib_IntVector_Intrinsics_vec128
  v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v0, v1);
  Lib_IntVector_Intrinsics_vec128
  v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v2, v3);
  Lib_IntVector_Intrinsics_vec128
  v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v2, v3);
  Lib_IntVector_Intrinsics_vec128
  v0__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec128
  v1__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec128
  v2__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec128
  v3__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec128 v0__6 = v0__5;
  Lib_IntVector_Intrinsics_vec128 v2__6 = v2__5;
  Lib_IntVector_Intrinsics_vec128 v1__6 = v1__5;
  Lib_IntVector_Intrinsics_vec128 v3__6 = v3__5;
  Lib_IntVector_Intrinsics_vec128 ws12 = v0__6;
  Lib_IntVector_Intrinsics_vec128 ws13 = v1__6;
  Lib_IntVector_Intrinsics_vec128 ws14 = v2__6;
  Lib_IntVector_Intrinsics_vec128 ws15 = v3__6;
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
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t k_t = Hacl_Hash_SHA2_k224_256[16U * i0 + i];
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
                    6U),
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(e0,
                      11U),
                    Lib_IntVector_Intrinsics_vec128_rotate_right32(e0, 25U)))),
              Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(e0, f0),
                Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_lognot(e0), g0))),
            k_e_t),
          ws_t);
      Lib_IntVector_Intrinsics_vec128
      t2 =
        Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
              2U),
            Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
                13U),
              Lib_IntVector_Intrinsics_vec128_rotate_right32(a0, 22U))),
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
      hash[7U] = h12;);
    if (i0 < 3U)
    {
      KRML_MAYBE_FOR16(i,
        0U,
        16U,
        1U,
        Lib_IntVector_Intrinsics_vec128 t16 = ws[i];
        Lib_IntVector_Intrinsics_vec128 t15 = ws[(i + 1U) % 16U];
        Lib_IntVector_Intrinsics_vec128 t7 = ws[(i + 9U) % 16U];
        Lib_IntVector_Intrinsics_vec128 t2 = ws[(i + 14U) % 16U];
        Lib_IntVector_Intrinsics_vec128
        s1 =
          Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
              17U),
            Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
                19U),
              Lib_IntVector_Intrinsics_vec128_shift_right32(t2, 10U)));
        Lib_IntVector_Intrinsics_vec128
        s0 =
          Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
              7U),
            Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
                18U),
              Lib_IntVector_Intrinsics_vec128_shift_right32(t15, 3U)));
        ws[i] =
          Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(s1,
                t7),
              s0),
            t16););
    });
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    Lib_IntVector_Intrinsics_vec128 *os = hash;
    Lib_IntVector_Intrinsics_vec128
    x = Lib_IntVector_Intrinsics_vec128_add32(hash[i], hash_old[i]);
    os[i] = x;);
}

static inline void
sha224_update_nblocks4(
  uint32_t len,
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ b,
  Lib_IntVector_Intrinsics_vec128 *st
)
{
  uint32_t blocks = len / 64U;
  for (uint32_t i = 0U; i < blocks; i++)
  {
    uint8_t *b3 = b.snd.snd.snd;
    uint8_t *b2 = b.snd.snd.fst;
    uint8_t *b1 = b.snd.fst;
    uint8_t *b0 = b.fst;
    uint8_t *bl0 = b0 + i * 64U;
    uint8_t *bl1 = b1 + i * 64U;
    uint8_t *bl2 = b2 + i * 64U;
    uint8_t *bl3 = b3 + i * 64U;
    K____uint8_t___uint8_t____K____uint8_t___uint8_t_
    mb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
    sha224_update4(mb, st);
  }
}

static inline void
sha224_update_last4(
  uint64_t totlen,
  uint32_t len,
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ b,
  Lib_IntVector_Intrinsics_vec128 *hash
)
{
  uint32_t blocks;
  if (len + 8U + 1U <= 64U)
  {
    blocks = 1U;
  }
  else
  {
    blocks = 2U;
  }
  uint32_t fin = blocks * 64U;
  uint8_t last[512U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = totlen << 3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b3 = b.snd.snd.snd;
  uint8_t *b2 = b.snd.snd.fst;
  uint8_t *b1 = b.snd.fst;
  uint8_t *b0 = b.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + 128U;
  uint8_t *last2 = last + 256U;
  uint8_t *last3 = last + 384U;
  memcpy(last00, b0, len * sizeof (uint8_t));
  last00[len] = 0x80U;
  memcpy(last00 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + 64U;
  uint8_t *l00 = last010;
  uint8_t *l01 = last110;
  memcpy(last10, b1, len * sizeof (uint8_t));
  last10[len] = 0x80U;
  memcpy(last10 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + 64U;
  uint8_t *l10 = last011;
  uint8_t *l11 = last111;
  memcpy(last2, b2, len * sizeof (uint8_t));
  last2[len] = 0x80U;
  memcpy(last2 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + 64U;
  uint8_t *l20 = last012;
  uint8_t *l21 = last112;
  memcpy(last3, b3, len * sizeof (uint8_t));
  last3[len] = 0x80U;
  memcpy(last3 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last01 = last3;
  uint8_t *last11 = last3 + 64U;
  uint8_t *l30 = last01;
  uint8_t *l31 = last11;
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  mb0 = { .fst = l00, .snd = { .fst = l10, .snd = { .fst = l20, .snd = l30 } } };
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  mb1 = { .fst = l01, .snd = { .fst = l11, .snd = { .fst = l21, .snd = l31 } } };
  Hacl_Hash_SHA2_uint8_2x4p scrut = { .fst = mb0, .snd = mb1 };
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ last0 = scrut.fst;
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ last1 = scrut.snd;
  sha224_update4(last0, hash);
  if (blocks > 1U)
  {
    sha224_update4(last1, hash);
    return;
  }
}

static inline void
sha224_finish4(
  Lib_IntVector_Intrinsics_vec128 *st,
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ h
)
{
  uint8_t hbuf[128U] = { 0U };
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
  v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec128
  v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128
  v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128 v0__2 = v0__1;
  Lib_IntVector_Intrinsics_vec128 v2__2 = v2__1;
  Lib_IntVector_Intrinsics_vec128 v1__2 = v1__1;
  Lib_IntVector_Intrinsics_vec128 v3__2 = v3__1;
  Lib_IntVector_Intrinsics_vec128 st4_ = v0__2;
  Lib_IntVector_Intrinsics_vec128 st5_ = v1__2;
  Lib_IntVector_Intrinsics_vec128 st6_ = v2__2;
  Lib_IntVector_Intrinsics_vec128 st7_ = v3__2;
  st[0U] = st0_;
  st[1U] = st4_;
  st[2U] = st1_;
  st[3U] = st5_;
  st[4U] = st2_;
  st[5U] = st6_;
  st[6U] = st3_;
  st[7U] = st7_;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    Lib_IntVector_Intrinsics_vec128_store32_be(hbuf + i * 16U, st[i]););
  uint8_t *b3 = h.snd.snd.snd;
  uint8_t *b2 = h.snd.snd.fst;
  uint8_t *b1 = h.snd.fst;
  uint8_t *b0 = h.fst;
  memcpy(b0, hbuf, 28U * sizeof (uint8_t));
  memcpy(b1, hbuf + 32U, 28U * sizeof (uint8_t));
  memcpy(b2, hbuf + 64U, 28U * sizeof (uint8_t));
  memcpy(b3, hbuf + 96U, 28U * sizeof (uint8_t));
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
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  ib = { .fst = input0, .snd = { .fst = input1, .snd = { .fst = input2, .snd = input3 } } };
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  rb = { .fst = dst0, .snd = { .fst = dst1, .snd = { .fst = dst2, .snd = dst3 } } };
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[8U] KRML_POST_ALIGN(16) = { 0U };
  sha224_init4(st);
  uint32_t rem = input_len % 64U;
  uint64_t len_ = (uint64_t)input_len;
  sha224_update_nblocks4(input_len, ib, st);
  uint32_t rem1 = input_len % 64U;
  uint8_t *b3 = ib.snd.snd.snd;
  uint8_t *b2 = ib.snd.snd.fst;
  uint8_t *b1 = ib.snd.fst;
  uint8_t *b0 = ib.fst;
  uint8_t *bl0 = b0 + input_len - rem1;
  uint8_t *bl1 = b1 + input_len - rem1;
  uint8_t *bl2 = b2 + input_len - rem1;
  uint8_t *bl3 = b3 + input_len - rem1;
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  lb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
  sha224_update_last4(len_, rem, lb, st);
  sha224_finish4(st, rb);
}

static inline void sha256_init4(Lib_IntVector_Intrinsics_vec128 *hash)
{
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    Lib_IntVector_Intrinsics_vec128 *os = hash;
    uint32_t hi = Hacl_Hash_SHA2_h256[i];
    Lib_IntVector_Intrinsics_vec128 x = Lib_IntVector_Intrinsics_vec128_load32(hi);
    os[i] = x;);
}

static inline void
sha256_update4(
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ b,
  Lib_IntVector_Intrinsics_vec128 *hash
)
{
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 hash_old[8U] KRML_POST_ALIGN(16) = { 0U };
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 ws[16U] KRML_POST_ALIGN(16) = { 0U };
  memcpy(hash_old, hash, 8U * sizeof (Lib_IntVector_Intrinsics_vec128));
  uint8_t *b3 = b.snd.snd.snd;
  uint8_t *b2 = b.snd.snd.fst;
  uint8_t *b10 = b.snd.fst;
  uint8_t *b00 = b.fst;
  ws[0U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00);
  ws[1U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10);
  ws[2U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2);
  ws[3U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3);
  ws[4U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + 16U);
  ws[5U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + 16U);
  ws[6U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + 16U);
  ws[7U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + 16U);
  ws[8U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + 32U);
  ws[9U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + 32U);
  ws[10U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + 32U);
  ws[11U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + 32U);
  ws[12U] = Lib_IntVector_Intrinsics_vec128_load32_be(b00 + 48U);
  ws[13U] = Lib_IntVector_Intrinsics_vec128_load32_be(b10 + 48U);
  ws[14U] = Lib_IntVector_Intrinsics_vec128_load32_be(b2 + 48U);
  ws[15U] = Lib_IntVector_Intrinsics_vec128_load32_be(b3 + 48U);
  Lib_IntVector_Intrinsics_vec128 v00 = ws[0U];
  Lib_IntVector_Intrinsics_vec128 v10 = ws[1U];
  Lib_IntVector_Intrinsics_vec128 v20 = ws[2U];
  Lib_IntVector_Intrinsics_vec128 v30 = ws[3U];
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
  Lib_IntVector_Intrinsics_vec128 ws0 = v0__0;
  Lib_IntVector_Intrinsics_vec128 ws1 = v1__0;
  Lib_IntVector_Intrinsics_vec128 ws2 = v2__0;
  Lib_IntVector_Intrinsics_vec128 ws3 = v3__0;
  Lib_IntVector_Intrinsics_vec128 v01 = ws[4U];
  Lib_IntVector_Intrinsics_vec128 v11 = ws[5U];
  Lib_IntVector_Intrinsics_vec128 v21 = ws[6U];
  Lib_IntVector_Intrinsics_vec128 v31 = ws[7U];
  Lib_IntVector_Intrinsics_vec128
  v0_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v01, v11);
  Lib_IntVector_Intrinsics_vec128
  v1_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v01, v11);
  Lib_IntVector_Intrinsics_vec128
  v2_0 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v21, v31);
  Lib_IntVector_Intrinsics_vec128
  v3_0 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v21, v31);
  Lib_IntVector_Intrinsics_vec128
  v0__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec128
  v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec128
  v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128
  v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128 v0__2 = v0__1;
  Lib_IntVector_Intrinsics_vec128 v2__2 = v2__1;
  Lib_IntVector_Intrinsics_vec128 v1__2 = v1__1;
  Lib_IntVector_Intrinsics_vec128 v3__2 = v3__1;
  Lib_IntVector_Intrinsics_vec128 ws4 = v0__2;
  Lib_IntVector_Intrinsics_vec128 ws5 = v1__2;
  Lib_IntVector_Intrinsics_vec128 ws6 = v2__2;
  Lib_IntVector_Intrinsics_vec128 ws7 = v3__2;
  Lib_IntVector_Intrinsics_vec128 v02 = ws[8U];
  Lib_IntVector_Intrinsics_vec128 v12 = ws[9U];
  Lib_IntVector_Intrinsics_vec128 v22 = ws[10U];
  Lib_IntVector_Intrinsics_vec128 v32 = ws[11U];
  Lib_IntVector_Intrinsics_vec128
  v0_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v02, v12);
  Lib_IntVector_Intrinsics_vec128
  v1_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v02, v12);
  Lib_IntVector_Intrinsics_vec128
  v2_1 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v22, v32);
  Lib_IntVector_Intrinsics_vec128
  v3_1 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v22, v32);
  Lib_IntVector_Intrinsics_vec128
  v0__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec128
  v1__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_1, v2_1);
  Lib_IntVector_Intrinsics_vec128
  v2__3 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec128
  v3__3 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_1, v3_1);
  Lib_IntVector_Intrinsics_vec128 v0__4 = v0__3;
  Lib_IntVector_Intrinsics_vec128 v2__4 = v2__3;
  Lib_IntVector_Intrinsics_vec128 v1__4 = v1__3;
  Lib_IntVector_Intrinsics_vec128 v3__4 = v3__3;
  Lib_IntVector_Intrinsics_vec128 ws8 = v0__4;
  Lib_IntVector_Intrinsics_vec128 ws9 = v1__4;
  Lib_IntVector_Intrinsics_vec128 ws10 = v2__4;
  Lib_IntVector_Intrinsics_vec128 ws11 = v3__4;
  Lib_IntVector_Intrinsics_vec128 v0 = ws[12U];
  Lib_IntVector_Intrinsics_vec128 v1 = ws[13U];
  Lib_IntVector_Intrinsics_vec128 v2 = ws[14U];
  Lib_IntVector_Intrinsics_vec128 v3 = ws[15U];
  Lib_IntVector_Intrinsics_vec128
  v0_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v0, v1);
  Lib_IntVector_Intrinsics_vec128
  v1_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v0, v1);
  Lib_IntVector_Intrinsics_vec128
  v2_2 = Lib_IntVector_Intrinsics_vec128_interleave_low32(v2, v3);
  Lib_IntVector_Intrinsics_vec128
  v3_2 = Lib_IntVector_Intrinsics_vec128_interleave_high32(v2, v3);
  Lib_IntVector_Intrinsics_vec128
  v0__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec128
  v1__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_2, v2_2);
  Lib_IntVector_Intrinsics_vec128
  v2__5 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec128
  v3__5 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_2, v3_2);
  Lib_IntVector_Intrinsics_vec128 v0__6 = v0__5;
  Lib_IntVector_Intrinsics_vec128 v2__6 = v2__5;
  Lib_IntVector_Intrinsics_vec128 v1__6 = v1__5;
  Lib_IntVector_Intrinsics_vec128 v3__6 = v3__5;
  Lib_IntVector_Intrinsics_vec128 ws12 = v0__6;
  Lib_IntVector_Intrinsics_vec128 ws13 = v1__6;
  Lib_IntVector_Intrinsics_vec128 ws14 = v2__6;
  Lib_IntVector_Intrinsics_vec128 ws15 = v3__6;
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
  KRML_MAYBE_FOR4(i0,
    0U,
    4U,
    1U,
    KRML_MAYBE_FOR16(i,
      0U,
      16U,
      1U,
      uint32_t k_t = Hacl_Hash_SHA2_k224_256[16U * i0 + i];
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
                    6U),
                  Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(e0,
                      11U),
                    Lib_IntVector_Intrinsics_vec128_rotate_right32(e0, 25U)))),
              Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_and(e0, f0),
                Lib_IntVector_Intrinsics_vec128_and(Lib_IntVector_Intrinsics_vec128_lognot(e0), g0))),
            k_e_t),
          ws_t);
      Lib_IntVector_Intrinsics_vec128
      t2 =
        Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
              2U),
            Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(a0,
                13U),
              Lib_IntVector_Intrinsics_vec128_rotate_right32(a0, 22U))),
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
      hash[7U] = h12;);
    if (i0 < 3U)
    {
      KRML_MAYBE_FOR16(i,
        0U,
        16U,
        1U,
        Lib_IntVector_Intrinsics_vec128 t16 = ws[i];
        Lib_IntVector_Intrinsics_vec128 t15 = ws[(i + 1U) % 16U];
        Lib_IntVector_Intrinsics_vec128 t7 = ws[(i + 9U) % 16U];
        Lib_IntVector_Intrinsics_vec128 t2 = ws[(i + 14U) % 16U];
        Lib_IntVector_Intrinsics_vec128
        s1 =
          Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
              17U),
            Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t2,
                19U),
              Lib_IntVector_Intrinsics_vec128_shift_right32(t2, 10U)));
        Lib_IntVector_Intrinsics_vec128
        s0 =
          Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
              7U),
            Lib_IntVector_Intrinsics_vec128_xor(Lib_IntVector_Intrinsics_vec128_rotate_right32(t15,
                18U),
              Lib_IntVector_Intrinsics_vec128_shift_right32(t15, 3U)));
        ws[i] =
          Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(Lib_IntVector_Intrinsics_vec128_add32(s1,
                t7),
              s0),
            t16););
    });
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    Lib_IntVector_Intrinsics_vec128 *os = hash;
    Lib_IntVector_Intrinsics_vec128
    x = Lib_IntVector_Intrinsics_vec128_add32(hash[i], hash_old[i]);
    os[i] = x;);
}

static inline void
sha256_update_nblocks4(
  uint32_t len,
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ b,
  Lib_IntVector_Intrinsics_vec128 *st
)
{
  uint32_t blocks = len / 64U;
  for (uint32_t i = 0U; i < blocks; i++)
  {
    uint8_t *b3 = b.snd.snd.snd;
    uint8_t *b2 = b.snd.snd.fst;
    uint8_t *b1 = b.snd.fst;
    uint8_t *b0 = b.fst;
    uint8_t *bl0 = b0 + i * 64U;
    uint8_t *bl1 = b1 + i * 64U;
    uint8_t *bl2 = b2 + i * 64U;
    uint8_t *bl3 = b3 + i * 64U;
    K____uint8_t___uint8_t____K____uint8_t___uint8_t_
    mb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
    sha256_update4(mb, st);
  }
}

static inline void
sha256_update_last4(
  uint64_t totlen,
  uint32_t len,
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ b,
  Lib_IntVector_Intrinsics_vec128 *hash
)
{
  uint32_t blocks;
  if (len + 8U + 1U <= 64U)
  {
    blocks = 1U;
  }
  else
  {
    blocks = 2U;
  }
  uint32_t fin = blocks * 64U;
  uint8_t last[512U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = totlen << 3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b3 = b.snd.snd.snd;
  uint8_t *b2 = b.snd.snd.fst;
  uint8_t *b1 = b.snd.fst;
  uint8_t *b0 = b.fst;
  uint8_t *last00 = last;
  uint8_t *last10 = last + 128U;
  uint8_t *last2 = last + 256U;
  uint8_t *last3 = last + 384U;
  memcpy(last00, b0, len * sizeof (uint8_t));
  last00[len] = 0x80U;
  memcpy(last00 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last010 = last00;
  uint8_t *last110 = last00 + 64U;
  uint8_t *l00 = last010;
  uint8_t *l01 = last110;
  memcpy(last10, b1, len * sizeof (uint8_t));
  last10[len] = 0x80U;
  memcpy(last10 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last011 = last10;
  uint8_t *last111 = last10 + 64U;
  uint8_t *l10 = last011;
  uint8_t *l11 = last111;
  memcpy(last2, b2, len * sizeof (uint8_t));
  last2[len] = 0x80U;
  memcpy(last2 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last012 = last2;
  uint8_t *last112 = last2 + 64U;
  uint8_t *l20 = last012;
  uint8_t *l21 = last112;
  memcpy(last3, b3, len * sizeof (uint8_t));
  last3[len] = 0x80U;
  memcpy(last3 + fin - 8U, totlen_buf, 8U * sizeof (uint8_t));
  uint8_t *last01 = last3;
  uint8_t *last11 = last3 + 64U;
  uint8_t *l30 = last01;
  uint8_t *l31 = last11;
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  mb0 = { .fst = l00, .snd = { .fst = l10, .snd = { .fst = l20, .snd = l30 } } };
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  mb1 = { .fst = l01, .snd = { .fst = l11, .snd = { .fst = l21, .snd = l31 } } };
  Hacl_Hash_SHA2_uint8_2x4p scrut = { .fst = mb0, .snd = mb1 };
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ last0 = scrut.fst;
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ last1 = scrut.snd;
  sha256_update4(last0, hash);
  if (blocks > 1U)
  {
    sha256_update4(last1, hash);
    return;
  }
}

static inline void
sha256_finish4(
  Lib_IntVector_Intrinsics_vec128 *st,
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_ h
)
{
  uint8_t hbuf[128U] = { 0U };
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
  v1__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v0_0, v2_0);
  Lib_IntVector_Intrinsics_vec128
  v2__1 = Lib_IntVector_Intrinsics_vec128_interleave_low64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128
  v3__1 = Lib_IntVector_Intrinsics_vec128_interleave_high64(v1_0, v3_0);
  Lib_IntVector_Intrinsics_vec128 v0__2 = v0__1;
  Lib_IntVector_Intrinsics_vec128 v2__2 = v2__1;
  Lib_IntVector_Intrinsics_vec128 v1__2 = v1__1;
  Lib_IntVector_Intrinsics_vec128 v3__2 = v3__1;
  Lib_IntVector_Intrinsics_vec128 st4_ = v0__2;
  Lib_IntVector_Intrinsics_vec128 st5_ = v1__2;
  Lib_IntVector_Intrinsics_vec128 st6_ = v2__2;
  Lib_IntVector_Intrinsics_vec128 st7_ = v3__2;
  st[0U] = st0_;
  st[1U] = st4_;
  st[2U] = st1_;
  st[3U] = st5_;
  st[4U] = st2_;
  st[5U] = st6_;
  st[6U] = st3_;
  st[7U] = st7_;
  KRML_MAYBE_FOR8(i,
    0U,
    8U,
    1U,
    Lib_IntVector_Intrinsics_vec128_store32_be(hbuf + i * 16U, st[i]););
  uint8_t *b3 = h.snd.snd.snd;
  uint8_t *b2 = h.snd.snd.fst;
  uint8_t *b1 = h.snd.fst;
  uint8_t *b0 = h.fst;
  memcpy(b0, hbuf, 32U * sizeof (uint8_t));
  memcpy(b1, hbuf + 32U, 32U * sizeof (uint8_t));
  memcpy(b2, hbuf + 64U, 32U * sizeof (uint8_t));
  memcpy(b3, hbuf + 96U, 32U * sizeof (uint8_t));
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
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  ib = { .fst = input0, .snd = { .fst = input1, .snd = { .fst = input2, .snd = input3 } } };
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  rb = { .fst = dst0, .snd = { .fst = dst1, .snd = { .fst = dst2, .snd = dst3 } } };
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 st[8U] KRML_POST_ALIGN(16) = { 0U };
  sha256_init4(st);
  uint32_t rem = input_len % 64U;
  uint64_t len_ = (uint64_t)input_len;
  sha256_update_nblocks4(input_len, ib, st);
  uint32_t rem1 = input_len % 64U;
  uint8_t *b3 = ib.snd.snd.snd;
  uint8_t *b2 = ib.snd.snd.fst;
  uint8_t *b1 = ib.snd.fst;
  uint8_t *b0 = ib.fst;
  uint8_t *bl0 = b0 + input_len - rem1;
  uint8_t *bl1 = b1 + input_len - rem1;
  uint8_t *bl2 = b2 + input_len - rem1;
  uint8_t *bl3 = b3 + input_len - rem1;
  K____uint8_t___uint8_t____K____uint8_t___uint8_t_
  lb = { .fst = bl0, .snd = { .fst = bl1, .snd = { .fst = bl2, .snd = bl3 } } };
  sha256_update_last4(len_, rem, lb, st);
  sha256_finish4(st, rb);
}

