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


#include "internal/Hacl_Hash_Blake2s.h"

#include "internal/Hacl_Impl_Blake2_Constants.h"
#include "internal/Hacl_Hash_Blake2b.h"
#include "lib_memzero0.h"

/* SNIPPET_START: update_block */

static inline void
update_block(uint32_t *wv, uint32_t *hash, bool flag, uint64_t totlen, uint8_t *d)
{
  uint32_t m_w[16U] = { 0U };
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint32_t *os = m_w;
    uint8_t *bj = d + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  uint32_t mask[4U] = { 0U };
  uint32_t wv_14;
  if (flag)
  {
    wv_14 = 0xFFFFFFFFU;
  }
  else
  {
    wv_14 = 0U;
  }
  uint32_t wv_15 = 0U;
  mask[0U] = (uint32_t)totlen;
  mask[1U] = (uint32_t)(totlen >> 32U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, hash, 16U * sizeof (uint32_t));
  uint32_t *wv3 = wv + 12U;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint32_t *os = wv3;
    uint32_t x = wv3[i] ^ mask[i];
    os[i] = x;);
  KRML_MAYBE_FOR10(i0,
    0U,
    10U,
    1U,
    uint32_t start_idx = i0 % 10U * 16U;
    uint32_t m_st[16U] = { 0U };
    uint32_t *r0 = m_st;
    uint32_t *r1 = m_st + 4U;
    uint32_t *r20 = m_st + 8U;
    uint32_t *r30 = m_st + 12U;
    uint32_t s0 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 0U];
    uint32_t s1 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 1U];
    uint32_t s2 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 2U];
    uint32_t s3 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 3U];
    uint32_t s4 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 4U];
    uint32_t s5 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 5U];
    uint32_t s6 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 6U];
    uint32_t s7 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 7U];
    uint32_t s8 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 8U];
    uint32_t s9 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 9U];
    uint32_t s10 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 10U];
    uint32_t s11 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 11U];
    uint32_t s12 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 12U];
    uint32_t s13 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 13U];
    uint32_t s14 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 14U];
    uint32_t s15 = Hacl_Hash_Blake2s_sigmaTable[start_idx + 15U];
    uint32_t uu____0 = m_w[s2];
    uint32_t uu____1 = m_w[s4];
    uint32_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint32_t uu____3 = m_w[s3];
    uint32_t uu____4 = m_w[s5];
    uint32_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint32_t uu____6 = m_w[s10];
    uint32_t uu____7 = m_w[s12];
    uint32_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint32_t uu____9 = m_w[s11];
    uint32_t uu____10 = m_w[s13];
    uint32_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint32_t *x = m_st;
    uint32_t *y = m_st + 4U;
    uint32_t *z = m_st + 8U;
    uint32_t *w = m_st + 12U;
    uint32_t a = 0U;
    uint32_t b0 = 1U;
    uint32_t c0 = 2U;
    uint32_t d10 = 3U;
    uint32_t *wv_a0 = wv + a * 4U;
    uint32_t *wv_b0 = wv + b0 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;);
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + x[i];
      os[i] = x1;);
    uint32_t *wv_a1 = wv + d10 * 4U;
    uint32_t *wv_b1 = wv + a * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a1;
      uint32_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;);
    uint32_t *r10 = wv_a1;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r10;
      uint32_t x1 = r10[i];
      uint32_t x10 = x1 >> 16U | x1 << 16U;
      os[i] = x10;);
    uint32_t *wv_a2 = wv + c0 * 4U;
    uint32_t *wv_b2 = wv + d10 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a2;
      uint32_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;);
    uint32_t *wv_a3 = wv + b0 * 4U;
    uint32_t *wv_b3 = wv + c0 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a3;
      uint32_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;);
    uint32_t *r12 = wv_a3;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r12;
      uint32_t x1 = r12[i];
      uint32_t x10 = x1 >> 12U | x1 << 20U;
      os[i] = x10;);
    uint32_t *wv_a4 = wv + a * 4U;
    uint32_t *wv_b4 = wv + b0 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;);
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + y[i];
      os[i] = x1;);
    uint32_t *wv_a5 = wv + d10 * 4U;
    uint32_t *wv_b5 = wv + a * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a5;
      uint32_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;);
    uint32_t *r13 = wv_a5;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r13;
      uint32_t x1 = r13[i];
      uint32_t x10 = x1 >> 8U | x1 << 24U;
      os[i] = x10;);
    uint32_t *wv_a6 = wv + c0 * 4U;
    uint32_t *wv_b6 = wv + d10 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a6;
      uint32_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;);
    uint32_t *wv_a7 = wv + b0 * 4U;
    uint32_t *wv_b7 = wv + c0 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a7;
      uint32_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;);
    uint32_t *r14 = wv_a7;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r14;
      uint32_t x1 = r14[i];
      uint32_t x10 = x1 >> 7U | x1 << 25U;
      os[i] = x10;);
    uint32_t *r15 = wv + 4U;
    uint32_t *r21 = wv + 8U;
    uint32_t *r31 = wv + 12U;
    uint32_t *r110 = r15;
    uint32_t x00 = r110[1U];
    uint32_t x10 = r110[2U];
    uint32_t x20 = r110[3U];
    uint32_t x30 = r110[0U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint32_t *r111 = r21;
    uint32_t x01 = r111[2U];
    uint32_t x11 = r111[3U];
    uint32_t x21 = r111[0U];
    uint32_t x31 = r111[1U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint32_t *r112 = r31;
    uint32_t x02 = r112[3U];
    uint32_t x12 = r112[0U];
    uint32_t x22 = r112[1U];
    uint32_t x32 = r112[2U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = 0U;
    uint32_t b = 1U;
    uint32_t c = 2U;
    uint32_t d1 = 3U;
    uint32_t *wv_a = wv + a0 * 4U;
    uint32_t *wv_b8 = wv + b * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;);
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + z[i];
      os[i] = x1;);
    uint32_t *wv_a8 = wv + d1 * 4U;
    uint32_t *wv_b9 = wv + a0 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a8;
      uint32_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;);
    uint32_t *r16 = wv_a8;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r16;
      uint32_t x1 = r16[i];
      uint32_t x13 = x1 >> 16U | x1 << 16U;
      os[i] = x13;);
    uint32_t *wv_a9 = wv + c * 4U;
    uint32_t *wv_b10 = wv + d1 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a9;
      uint32_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;);
    uint32_t *wv_a10 = wv + b * 4U;
    uint32_t *wv_b11 = wv + c * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a10;
      uint32_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;);
    uint32_t *r17 = wv_a10;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r17;
      uint32_t x1 = r17[i];
      uint32_t x13 = x1 >> 12U | x1 << 20U;
      os[i] = x13;);
    uint32_t *wv_a11 = wv + a0 * 4U;
    uint32_t *wv_b12 = wv + b * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;);
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + w[i];
      os[i] = x1;);
    uint32_t *wv_a12 = wv + d1 * 4U;
    uint32_t *wv_b13 = wv + a0 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a12;
      uint32_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;);
    uint32_t *r18 = wv_a12;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r18;
      uint32_t x1 = r18[i];
      uint32_t x13 = x1 >> 8U | x1 << 24U;
      os[i] = x13;);
    uint32_t *wv_a13 = wv + c * 4U;
    uint32_t *wv_b14 = wv + d1 * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a13;
      uint32_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;);
    uint32_t *wv_a14 = wv + b * 4U;
    uint32_t *wv_b = wv + c * 4U;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = wv_a14;
      uint32_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;);
    uint32_t *r19 = wv_a14;
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *os = r19;
      uint32_t x1 = r19[i];
      uint32_t x13 = x1 >> 7U | x1 << 25U;
      os[i] = x13;);
    uint32_t *r113 = wv + 4U;
    uint32_t *r2 = wv + 8U;
    uint32_t *r3 = wv + 12U;
    uint32_t *r11 = r113;
    uint32_t x03 = r11[3U];
    uint32_t x13 = r11[0U];
    uint32_t x23 = r11[1U];
    uint32_t x33 = r11[2U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint32_t *r114 = r2;
    uint32_t x04 = r114[2U];
    uint32_t x14 = r114[3U];
    uint32_t x24 = r114[0U];
    uint32_t x34 = r114[1U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint32_t *r115 = r3;
    uint32_t x0 = r115[1U];
    uint32_t x1 = r115[2U];
    uint32_t x2 = r115[3U];
    uint32_t x3 = r115[0U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;);
  uint32_t *s0 = hash;
  uint32_t *s1 = hash + 4U;
  uint32_t *r0 = wv;
  uint32_t *r1 = wv + 4U;
  uint32_t *r2 = wv + 8U;
  uint32_t *r3 = wv + 12U;
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r0[i];
    os[i] = x;);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r2[i];
    os[i] = x;);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r1[i];
    os[i] = x;);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r3[i];
    os[i] = x;);
}

/* SNIPPET_END: update_block */

/* SNIPPET_START: Hacl_Hash_Blake2s_init */

void Hacl_Hash_Blake2s_init(uint32_t *hash, uint32_t kk, uint32_t nn)
{
  uint32_t tmp[8U] = { 0U };
  uint32_t *r0 = hash;
  uint32_t *r1 = hash + 4U;
  uint32_t *r2 = hash + 8U;
  uint32_t *r3 = hash + 12U;
  uint32_t iv0 = Hacl_Hash_Blake2s_ivTable_S[0U];
  uint32_t iv1 = Hacl_Hash_Blake2s_ivTable_S[1U];
  uint32_t iv2 = Hacl_Hash_Blake2s_ivTable_S[2U];
  uint32_t iv3 = Hacl_Hash_Blake2s_ivTable_S[3U];
  uint32_t iv4 = Hacl_Hash_Blake2s_ivTable_S[4U];
  uint32_t iv5 = Hacl_Hash_Blake2s_ivTable_S[5U];
  uint32_t iv6 = Hacl_Hash_Blake2s_ivTable_S[6U];
  uint32_t iv7 = Hacl_Hash_Blake2s_ivTable_S[7U];
  r2[0U] = iv0;
  r2[1U] = iv1;
  r2[2U] = iv2;
  r2[3U] = iv3;
  r3[0U] = iv4;
  r3[1U] = iv5;
  r3[2U] = iv6;
  r3[3U] = iv7;
  uint8_t salt[8U] = { 0U };
  uint8_t personal[8U] = { 0U };
  Hacl_Hash_Blake2s_blake2_params
  p =
    {
      .digest_length = 32U, .key_length = 0U, .fanout = 1U, .depth = 1U, .leaf_length = 0U,
      .node_offset = 0ULL, .node_depth = 0U, .inner_length = 0U, .salt = salt, .personal = personal
    };
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t *os = tmp + 4U;
    uint8_t *bj = p.salt + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint32_t *os = tmp + 6U;
    uint8_t *bj = p.personal + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;);
  tmp[0U] = nn ^ (kk << 8U ^ ((uint32_t)p.fanout << 16U ^ (uint32_t)p.depth << 24U));
  tmp[1U] = p.leaf_length;
  tmp[2U] = (uint32_t)p.node_offset;
  tmp[3U] =
    (uint32_t)(p.node_offset >> 32U)
    ^ ((uint32_t)p.node_depth << 16U ^ (uint32_t)p.inner_length << 24U);
  uint32_t tmp0 = tmp[0U];
  uint32_t tmp1 = tmp[1U];
  uint32_t tmp2 = tmp[2U];
  uint32_t tmp3 = tmp[3U];
  uint32_t tmp4 = tmp[4U];
  uint32_t tmp5 = tmp[5U];
  uint32_t tmp6 = tmp[6U];
  uint32_t tmp7 = tmp[7U];
  uint32_t iv0_ = iv0 ^ tmp0;
  uint32_t iv1_ = iv1 ^ tmp1;
  uint32_t iv2_ = iv2 ^ tmp2;
  uint32_t iv3_ = iv3 ^ tmp3;
  uint32_t iv4_ = iv4 ^ tmp4;
  uint32_t iv5_ = iv5 ^ tmp5;
  uint32_t iv6_ = iv6 ^ tmp6;
  uint32_t iv7_ = iv7 ^ tmp7;
  r0[0U] = iv0_;
  r0[1U] = iv1_;
  r0[2U] = iv2_;
  r0[3U] = iv3_;
  r1[0U] = iv4_;
  r1[1U] = iv5_;
  r1[2U] = iv6_;
  r1[3U] = iv7_;
}

/* SNIPPET_END: Hacl_Hash_Blake2s_init */

/* SNIPPET_START: update_key */

static void update_key(uint32_t *wv, uint32_t *hash, uint32_t kk, uint8_t *k, uint32_t ll)
{
  uint64_t lb = (uint64_t)64U;
  uint8_t b[64U] = { 0U };
  memcpy(b, k, kk * sizeof (uint8_t));
  if (ll == 0U)
  {
    update_block(wv, hash, true, lb, b);
  }
  else
  {
    update_block(wv, hash, false, lb, b);
  }
  Lib_Memzero0_memzero(b, 64U, uint8_t, void *);
}

/* SNIPPET_END: update_key */

/* SNIPPET_START: Hacl_Hash_Blake2s_update_multi */

void
Hacl_Hash_Blake2s_update_multi(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint8_t *blocks,
  uint32_t nb
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  for (uint32_t i = 0U; i < nb; i++)
  {
    uint64_t totlen = prev + (uint64_t)((i + 1U) * 64U);
    uint8_t *b = blocks + i * 64U;
    update_block(wv, hash, false, totlen, b);
  }
}

/* SNIPPET_END: Hacl_Hash_Blake2s_update_multi */

/* SNIPPET_START: Hacl_Hash_Blake2s_update_last */

void
Hacl_Hash_Blake2s_update_last(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint32_t rem,
  uint8_t *d
)
{
  uint8_t b[64U] = { 0U };
  uint8_t *last = d + len - rem;
  memcpy(b, last, rem * sizeof (uint8_t));
  uint64_t totlen = prev + (uint64_t)len;
  update_block(wv, hash, true, totlen, b);
  Lib_Memzero0_memzero(b, 64U, uint8_t, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2s_update_last */

/* SNIPPET_START: update_blocks */

static void
update_blocks(uint32_t len, uint32_t *wv, uint32_t *hash, uint64_t prev, uint8_t *blocks)
{
  uint32_t nb0 = len / 64U;
  uint32_t rem0 = len % 64U;
  uint32_t nb;
  if (rem0 == 0U && nb0 > 0U)
  {
    nb = nb0 - 1U;
  }
  else
  {
    nb = nb0;
  }
  uint32_t rem;
  if (rem0 == 0U && nb0 > 0U)
  {
    rem = 64U;
  }
  else
  {
    rem = rem0;
  }
  Hacl_Hash_Blake2s_update_multi(len, wv, hash, prev, blocks, nb);
  Hacl_Hash_Blake2s_update_last(len, wv, hash, prev, rem, blocks);
}

/* SNIPPET_END: update_blocks */

/* SNIPPET_START: update */

static inline void
update(uint32_t *wv, uint32_t *hash, uint32_t kk, uint8_t *k, uint32_t ll, uint8_t *d)
{
  uint64_t lb = (uint64_t)64U;
  if (kk > 0U)
  {
    update_key(wv, hash, kk, k, ll);
    if (!(ll == 0U))
    {
      update_blocks(ll, wv, hash, lb, d);
      return;
    }
    return;
  }
  update_blocks(ll, wv, hash, (uint64_t)0U, d);
}

/* SNIPPET_END: update */

/* SNIPPET_START: Hacl_Hash_Blake2s_finish */

void Hacl_Hash_Blake2s_finish(uint32_t nn, uint8_t *output, uint32_t *hash)
{
  uint8_t b[32U] = { 0U };
  uint8_t *first = b;
  uint8_t *second = b + 16U;
  uint32_t *row0 = hash;
  uint32_t *row1 = hash + 4U;
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, store32_le(first + i * 4U, row0[i]););
  KRML_MAYBE_FOR4(i, 0U, 4U, 1U, store32_le(second + i * 4U, row1[i]););
  uint8_t *final = b;
  memcpy(output, final, nn * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, 32U, uint8_t, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2s_finish */

/* SNIPPET_START: Hacl_Hash_Blake2s_malloc */

/**
  State allocation function when there is no key
*/
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_malloc(void)
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(64U, sizeof (uint8_t));
  uint32_t *wv = (uint32_t *)KRML_HOST_CALLOC(16U, sizeof (uint32_t));
  uint32_t *b = (uint32_t *)KRML_HOST_CALLOC(16U, sizeof (uint32_t));
  Hacl_Hash_Blake2s_block_state_t block_state = { .fst = wv, .snd = b };
  Hacl_Hash_Blake2s_state_t
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  Hacl_Hash_Blake2s_state_t
  *p = (Hacl_Hash_Blake2s_state_t *)KRML_HOST_MALLOC(sizeof (Hacl_Hash_Blake2s_state_t));
  p[0U] = s;
  Hacl_Hash_Blake2s_init(block_state.snd, 0U, 32U);
  return p;
}

/* SNIPPET_END: Hacl_Hash_Blake2s_malloc */

/* SNIPPET_START: Hacl_Hash_Blake2s_reset */

/**
  Re-initialization function when there is no key
*/
void Hacl_Hash_Blake2s_reset(Hacl_Hash_Blake2s_state_t *state)
{
  Hacl_Hash_Blake2s_state_t scrut = *state;
  uint8_t *buf = scrut.buf;
  Hacl_Hash_Blake2s_block_state_t block_state = scrut.block_state;
  Hacl_Hash_Blake2s_init(block_state.snd, 0U, 32U);
  Hacl_Hash_Blake2s_state_t
  tmp = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  state[0U] = tmp;
}

/* SNIPPET_END: Hacl_Hash_Blake2s_reset */

/* SNIPPET_START: Hacl_Hash_Blake2s_update */

/**
  Update function when there is no key; 0 = success, 1 = max length exceeded
*/
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2s_update(Hacl_Hash_Blake2s_state_t *state, uint8_t *chunk, uint32_t chunk_len)
{
  Hacl_Hash_Blake2s_state_t s = *state;
  uint64_t total_len = s.total_len;
  if ((uint64_t)chunk_len > 0xffffffffffffffffULL - total_len)
  {
    return Hacl_Streaming_Types_MaximumLengthExceeded;
  }
  uint32_t sz;
  if (total_len % (uint64_t)64U == 0ULL && total_len > 0ULL)
  {
    sz = 64U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)64U);
  }
  if (chunk_len <= 64U - sz)
  {
    Hacl_Hash_Blake2s_state_t s1 = *state;
    Hacl_Hash_Blake2s_block_state_t block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)64U == 0ULL && total_len1 > 0ULL)
    {
      sz1 = 64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)64U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, chunk, chunk_len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)chunk_len;
    *state
    =
      (
        (Hacl_Hash_Blake2s_state_t){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
  }
  else if (sz == 0U)
  {
    Hacl_Hash_Blake2s_state_t s1 = *state;
    Hacl_Hash_Blake2s_block_state_t block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)64U == 0ULL && total_len1 > 0ULL)
    {
      sz1 = 64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)64U);
    }
    if (!(sz1 == 0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      uint32_t *wv = block_state1.fst;
      uint32_t *hash = block_state1.snd;
      uint32_t nb = 1U;
      Hacl_Hash_Blake2s_update_multi(64U, wv, hash, prevlen, buf, nb);
    }
    uint32_t ite;
    if ((uint64_t)chunk_len % (uint64_t)64U == 0ULL && (uint64_t)chunk_len > 0ULL)
    {
      ite = 64U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)chunk_len % (uint64_t)64U);
    }
    uint32_t n_blocks = (chunk_len - ite) / 64U;
    uint32_t data1_len = n_blocks * 64U;
    uint32_t data2_len = chunk_len - data1_len;
    uint8_t *data1 = chunk;
    uint8_t *data2 = chunk + data1_len;
    uint32_t *wv = block_state1.fst;
    uint32_t *hash = block_state1.snd;
    uint32_t nb = data1_len / 64U;
    Hacl_Hash_Blake2s_update_multi(data1_len, wv, hash, total_len1, data1, nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Hash_Blake2s_state_t){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)chunk_len
        }
      );
  }
  else
  {
    uint32_t diff = 64U - sz;
    uint8_t *chunk1 = chunk;
    uint8_t *chunk2 = chunk + diff;
    Hacl_Hash_Blake2s_state_t s1 = *state;
    Hacl_Hash_Blake2s_block_state_t block_state10 = s1.block_state;
    uint8_t *buf0 = s1.buf;
    uint64_t total_len10 = s1.total_len;
    uint32_t sz10;
    if (total_len10 % (uint64_t)64U == 0ULL && total_len10 > 0ULL)
    {
      sz10 = 64U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)64U);
    }
    uint8_t *buf2 = buf0 + sz10;
    memcpy(buf2, chunk1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *state
    =
      (
        (Hacl_Hash_Blake2s_state_t){
          .block_state = block_state10,
          .buf = buf0,
          .total_len = total_len2
        }
      );
    Hacl_Hash_Blake2s_state_t s10 = *state;
    Hacl_Hash_Blake2s_block_state_t block_state1 = s10.block_state;
    uint8_t *buf = s10.buf;
    uint64_t total_len1 = s10.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)64U == 0ULL && total_len1 > 0ULL)
    {
      sz1 = 64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)64U);
    }
    if (!(sz1 == 0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      uint32_t *wv = block_state1.fst;
      uint32_t *hash = block_state1.snd;
      uint32_t nb = 1U;
      Hacl_Hash_Blake2s_update_multi(64U, wv, hash, prevlen, buf, nb);
    }
    uint32_t ite;
    if
    ((uint64_t)(chunk_len - diff) % (uint64_t)64U == 0ULL && (uint64_t)(chunk_len - diff) > 0ULL)
    {
      ite = 64U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)(chunk_len - diff) % (uint64_t)64U);
    }
    uint32_t n_blocks = (chunk_len - diff - ite) / 64U;
    uint32_t data1_len = n_blocks * 64U;
    uint32_t data2_len = chunk_len - diff - data1_len;
    uint8_t *data1 = chunk2;
    uint8_t *data2 = chunk2 + data1_len;
    uint32_t *wv = block_state1.fst;
    uint32_t *hash = block_state1.snd;
    uint32_t nb = data1_len / 64U;
    Hacl_Hash_Blake2s_update_multi(data1_len, wv, hash, total_len1, data1, nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Hash_Blake2s_state_t){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(chunk_len - diff)
        }
      );
  }
  return Hacl_Streaming_Types_Success;
}

/* SNIPPET_END: Hacl_Hash_Blake2s_update */

/* SNIPPET_START: Hacl_Hash_Blake2s_digest */

/**
  Finish function when there is no key
*/
void Hacl_Hash_Blake2s_digest(Hacl_Hash_Blake2s_state_t *state, uint8_t *output)
{
  Hacl_Hash_Blake2s_state_t scrut = *state;
  Hacl_Hash_Blake2s_block_state_t block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)64U == 0ULL && total_len > 0ULL)
  {
    r = 64U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)64U);
  }
  uint8_t *buf_1 = buf_;
  uint32_t wv0[16U] = { 0U };
  uint32_t b[16U] = { 0U };
  Hacl_Hash_Blake2s_block_state_t tmp_block_state = { .fst = wv0, .snd = b };
  uint32_t *src_b = block_state.snd;
  uint32_t *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, 16U * sizeof (uint32_t));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % 64U == 0U && r > 0U)
  {
    ite = 64U;
  }
  else
  {
    ite = r % 64U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  uint32_t *wv1 = tmp_block_state.fst;
  uint32_t *hash0 = tmp_block_state.snd;
  uint32_t nb = 0U;
  Hacl_Hash_Blake2s_update_multi(0U, wv1, hash0, prev_len, buf_multi, nb);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  uint32_t *wv = tmp_block_state.fst;
  uint32_t *hash = tmp_block_state.snd;
  Hacl_Hash_Blake2s_update_last(r, wv, hash, prev_len_last, r, buf_last);
  Hacl_Hash_Blake2s_finish(32U, output, tmp_block_state.snd);
}

/* SNIPPET_END: Hacl_Hash_Blake2s_digest */

/* SNIPPET_START: Hacl_Hash_Blake2s_free */

/**
  Free state function when there is no key
*/
void Hacl_Hash_Blake2s_free(Hacl_Hash_Blake2s_state_t *state)
{
  Hacl_Hash_Blake2s_state_t scrut = *state;
  uint8_t *buf = scrut.buf;
  Hacl_Hash_Blake2s_block_state_t block_state = scrut.block_state;
  uint32_t *wv = block_state.fst;
  uint32_t *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(state);
}

/* SNIPPET_END: Hacl_Hash_Blake2s_free */

/* SNIPPET_START: Hacl_Hash_Blake2s_hash_with_key */

/**
Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 32.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0.
*/
void
Hacl_Hash_Blake2s_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
)
{
  uint32_t b[16U] = { 0U };
  uint32_t b1[16U] = { 0U };
  Hacl_Hash_Blake2s_init(b, key_len, output_len);
  update(b1, b, key_len, key, input_len, input);
  Hacl_Hash_Blake2s_finish(output_len, output, b);
  Lib_Memzero0_memzero(b1, 16U, uint32_t, void *);
  Lib_Memzero0_memzero(b, 16U, uint32_t, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2s_hash_with_key */

