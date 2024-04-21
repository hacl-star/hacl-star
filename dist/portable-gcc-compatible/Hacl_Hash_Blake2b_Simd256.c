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


#include "internal/Hacl_Hash_Blake2b_Simd256.h"

#include "internal/Hacl_Impl_Blake2_Constants.h"
#include "internal/Hacl_Hash_Blake2b.h"
#include "lib_memzero0.h"

/* SNIPPET_START: update_block */

static inline void
update_block(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  bool flag,
  FStar_UInt128_uint128 totlen,
  uint8_t *d
)
{
  uint64_t m_w[16U] = { 0U };
  KRML_MAYBE_FOR16(i,
    0U,
    16U,
    1U,
    uint64_t *os = m_w;
    uint8_t *bj = d + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
  uint64_t wv_14;
  if (flag)
  {
    wv_14 = 0xFFFFFFFFFFFFFFFFULL;
  }
  else
  {
    wv_14 = 0ULL;
  }
  uint64_t wv_15 = 0ULL;
  mask =
    Lib_IntVector_Intrinsics_vec256_load64s(FStar_UInt128_uint128_to_uint64(totlen),
      FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen, 64U)),
      wv_14,
      wv_15);
  memcpy(wv, hash, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Lib_IntVector_Intrinsics_vec256 *wv3 = wv + 3U;
  wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
  KRML_MAYBE_FOR12(i,
    0U,
    12U,
    1U,
    uint32_t start_idx = i % 10U * 16U;
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 m_st[4U] KRML_POST_ALIGN(32) = { 0U };
    Lib_IntVector_Intrinsics_vec256 *r0 = m_st;
    Lib_IntVector_Intrinsics_vec256 *r1 = m_st + 1U;
    Lib_IntVector_Intrinsics_vec256 *r20 = m_st + 2U;
    Lib_IntVector_Intrinsics_vec256 *r30 = m_st + 3U;
    uint32_t s0 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 0U];
    uint32_t s1 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 1U];
    uint32_t s2 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 2U];
    uint32_t s3 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 3U];
    uint32_t s4 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 4U];
    uint32_t s5 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 5U];
    uint32_t s6 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 6U];
    uint32_t s7 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 7U];
    uint32_t s8 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 8U];
    uint32_t s9 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 9U];
    uint32_t s10 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 10U];
    uint32_t s11 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 11U];
    uint32_t s12 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 12U];
    uint32_t s13 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 13U];
    uint32_t s14 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 14U];
    uint32_t s15 = Hacl_Hash_Blake2b_sigmaTable[start_idx + 15U];
    r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
    r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
    r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
    r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s11], m_w[s13], m_w[s15]);
    Lib_IntVector_Intrinsics_vec256 *x = m_st;
    Lib_IntVector_Intrinsics_vec256 *y = m_st + 1U;
    Lib_IntVector_Intrinsics_vec256 *z = m_st + 2U;
    Lib_IntVector_Intrinsics_vec256 *w = m_st + 3U;
    uint32_t a = 0U;
    uint32_t b0 = 1U;
    uint32_t c0 = 2U;
    uint32_t d10 = 3U;
    Lib_IntVector_Intrinsics_vec256 *wv_a0 = wv + a * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b0 = wv + b0 * 1U;
    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a1 = wv + d10 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b1 = wv + a * 1U;
    wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
    wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], 32U);
    Lib_IntVector_Intrinsics_vec256 *wv_a2 = wv + c0 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b2 = wv + d10 * 1U;
    wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a3 = wv + b0 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b3 = wv + c0 * 1U;
    wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
    wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], 24U);
    Lib_IntVector_Intrinsics_vec256 *wv_a4 = wv + a * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b4 = wv + b0 * 1U;
    wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
    wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a5 = wv + d10 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b5 = wv + a * 1U;
    wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
    wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], 16U);
    Lib_IntVector_Intrinsics_vec256 *wv_a6 = wv + c0 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b6 = wv + d10 * 1U;
    wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a7 = wv + b0 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b7 = wv + c0 * 1U;
    wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
    wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], 63U);
    Lib_IntVector_Intrinsics_vec256 *r10 = wv + 1U;
    Lib_IntVector_Intrinsics_vec256 *r21 = wv + 2U;
    Lib_IntVector_Intrinsics_vec256 *r31 = wv + 3U;
    Lib_IntVector_Intrinsics_vec256 v00 = r10[0U];
    Lib_IntVector_Intrinsics_vec256
    v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, 1U);
    r10[0U] = v1;
    Lib_IntVector_Intrinsics_vec256 v01 = r21[0U];
    Lib_IntVector_Intrinsics_vec256
    v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, 2U);
    r21[0U] = v10;
    Lib_IntVector_Intrinsics_vec256 v02 = r31[0U];
    Lib_IntVector_Intrinsics_vec256
    v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, 3U);
    r31[0U] = v11;
    uint32_t a0 = 0U;
    uint32_t b = 1U;
    uint32_t c = 2U;
    uint32_t d1 = 3U;
    Lib_IntVector_Intrinsics_vec256 *wv_a = wv + a0 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b8 = wv + b * 1U;
    wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
    wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a8 = wv + d1 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b9 = wv + a0 * 1U;
    wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
    wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], 32U);
    Lib_IntVector_Intrinsics_vec256 *wv_a9 = wv + c * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b10 = wv + d1 * 1U;
    wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a10 = wv + b * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b11 = wv + c * 1U;
    wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
    wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], 24U);
    Lib_IntVector_Intrinsics_vec256 *wv_a11 = wv + a0 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b12 = wv + b * 1U;
    wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
    wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a12 = wv + d1 * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b13 = wv + a0 * 1U;
    wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
    wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], 16U);
    Lib_IntVector_Intrinsics_vec256 *wv_a13 = wv + c * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b14 = wv + d1 * 1U;
    wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a14 = wv + b * 1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b = wv + c * 1U;
    wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
    wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], 63U);
    Lib_IntVector_Intrinsics_vec256 *r11 = wv + 1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = wv + 2U;
    Lib_IntVector_Intrinsics_vec256 *r3 = wv + 3U;
    Lib_IntVector_Intrinsics_vec256 v0 = r11[0U];
    Lib_IntVector_Intrinsics_vec256
    v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, 3U);
    r11[0U] = v12;
    Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
    Lib_IntVector_Intrinsics_vec256
    v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, 2U);
    r2[0U] = v13;
    Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
    Lib_IntVector_Intrinsics_vec256
    v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, 1U);
    r3[0U] = v14;);
  Lib_IntVector_Intrinsics_vec256 *s0 = hash;
  Lib_IntVector_Intrinsics_vec256 *s1 = hash + 1U;
  Lib_IntVector_Intrinsics_vec256 *r0 = wv;
  Lib_IntVector_Intrinsics_vec256 *r1 = wv + 1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = wv + 2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = wv + 3U;
  s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
  s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
  s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r1[0U]);
  s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r3[0U]);
}

/* SNIPPET_END: update_block */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_init */

void
Hacl_Hash_Blake2b_Simd256_init(Lib_IntVector_Intrinsics_vec256 *hash, uint32_t kk, uint32_t nn)
{
  uint8_t salt[16U] = { 0U };
  uint8_t personal[16U] = { 0U };
  Hacl_Hash_Blake2b_blake2_params
  p =
    {
      .digest_length = 64U, .key_length = 0U, .fanout = 1U, .depth = 1U, .leaf_length = 0U,
      .node_offset = 0ULL, .node_depth = 0U, .inner_length = 0U, .salt = salt, .personal = personal
    };
  uint64_t tmp[8U] = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r0 = hash;
  Lib_IntVector_Intrinsics_vec256 *r1 = hash + 1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = hash + 2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = hash + 3U;
  uint64_t iv0 = Hacl_Hash_Blake2b_ivTable_B[0U];
  uint64_t iv1 = Hacl_Hash_Blake2b_ivTable_B[1U];
  uint64_t iv2 = Hacl_Hash_Blake2b_ivTable_B[2U];
  uint64_t iv3 = Hacl_Hash_Blake2b_ivTable_B[3U];
  uint64_t iv4 = Hacl_Hash_Blake2b_ivTable_B[4U];
  uint64_t iv5 = Hacl_Hash_Blake2b_ivTable_B[5U];
  uint64_t iv6 = Hacl_Hash_Blake2b_ivTable_B[6U];
  uint64_t iv7 = Hacl_Hash_Blake2b_ivTable_B[7U];
  r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  uint8_t kk1 = (uint8_t)kk;
  uint8_t nn1 = (uint8_t)nn;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint64_t *os = tmp + 4U;
    uint8_t *bj = p.salt + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint64_t *os = tmp + 6U;
    uint8_t *bj = p.personal + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  tmp[0U] =
    (uint64_t)nn1
    ^
      ((uint64_t)kk1
      << 8U
      ^ ((uint64_t)p.fanout << 16U ^ ((uint64_t)p.depth << 24U ^ (uint64_t)p.leaf_length << 32U)));
  tmp[1U] = p.node_offset;
  tmp[2U] = (uint64_t)p.node_depth ^ (uint64_t)p.inner_length << 8U;
  tmp[3U] = 0ULL;
  uint64_t tmp0 = tmp[0U];
  uint64_t tmp1 = tmp[1U];
  uint64_t tmp2 = tmp[2U];
  uint64_t tmp3 = tmp[3U];
  uint64_t tmp4 = tmp[4U];
  uint64_t tmp5 = tmp[5U];
  uint64_t tmp6 = tmp[6U];
  uint64_t tmp7 = tmp[7U];
  uint64_t iv0_ = iv0 ^ tmp0;
  uint64_t iv1_ = iv1 ^ tmp1;
  uint64_t iv2_ = iv2 ^ tmp2;
  uint64_t iv3_ = iv3 ^ tmp3;
  uint64_t iv4_ = iv4 ^ tmp4;
  uint64_t iv5_ = iv5 ^ tmp5;
  uint64_t iv6_ = iv6 ^ tmp6;
  uint64_t iv7_ = iv7 ^ tmp7;
  r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1_, iv2_, iv3_);
  r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4_, iv5_, iv6_, iv7_);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_init */

/* SNIPPET_START: init_with_params */

static void
init_with_params(Lib_IntVector_Intrinsics_vec256 *hash, Hacl_Hash_Blake2b_blake2_params p)
{
  uint64_t tmp[8U] = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r0 = hash;
  Lib_IntVector_Intrinsics_vec256 *r1 = hash + 1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = hash + 2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = hash + 3U;
  uint64_t iv0 = Hacl_Hash_Blake2b_ivTable_B[0U];
  uint64_t iv1 = Hacl_Hash_Blake2b_ivTable_B[1U];
  uint64_t iv2 = Hacl_Hash_Blake2b_ivTable_B[2U];
  uint64_t iv3 = Hacl_Hash_Blake2b_ivTable_B[3U];
  uint64_t iv4 = Hacl_Hash_Blake2b_ivTable_B[4U];
  uint64_t iv5 = Hacl_Hash_Blake2b_ivTable_B[5U];
  uint64_t iv6 = Hacl_Hash_Blake2b_ivTable_B[6U];
  uint64_t iv7 = Hacl_Hash_Blake2b_ivTable_B[7U];
  r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  uint8_t kk = p.key_length;
  uint8_t nn = p.digest_length;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint64_t *os = tmp + 4U;
    uint8_t *bj = p.salt + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint64_t *os = tmp + 6U;
    uint8_t *bj = p.personal + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  tmp[0U] =
    (uint64_t)nn
    ^
      ((uint64_t)kk
      << 8U
      ^ ((uint64_t)p.fanout << 16U ^ ((uint64_t)p.depth << 24U ^ (uint64_t)p.leaf_length << 32U)));
  tmp[1U] = p.node_offset;
  tmp[2U] = (uint64_t)p.node_depth ^ (uint64_t)p.inner_length << 8U;
  tmp[3U] = 0ULL;
  uint64_t tmp0 = tmp[0U];
  uint64_t tmp1 = tmp[1U];
  uint64_t tmp2 = tmp[2U];
  uint64_t tmp3 = tmp[3U];
  uint64_t tmp4 = tmp[4U];
  uint64_t tmp5 = tmp[5U];
  uint64_t tmp6 = tmp[6U];
  uint64_t tmp7 = tmp[7U];
  uint64_t iv0_ = iv0 ^ tmp0;
  uint64_t iv1_ = iv1 ^ tmp1;
  uint64_t iv2_ = iv2 ^ tmp2;
  uint64_t iv3_ = iv3 ^ tmp3;
  uint64_t iv4_ = iv4 ^ tmp4;
  uint64_t iv5_ = iv5 ^ tmp5;
  uint64_t iv6_ = iv6 ^ tmp6;
  uint64_t iv7_ = iv7 ^ tmp7;
  r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1_, iv2_, iv3_);
  r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4_, iv5_, iv6_, iv7_);
}

/* SNIPPET_END: init_with_params */

/* SNIPPET_START: update_key */

static void
update_key(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t ll
)
{
  FStar_UInt128_uint128 lb = FStar_UInt128_uint64_to_uint128((uint64_t)128U);
  uint8_t b[128U] = { 0U };
  memcpy(b, k, kk * sizeof (uint8_t));
  if (ll == 0U)
  {
    update_block(wv, hash, true, lb, b);
  }
  else
  {
    update_block(wv, hash, false, lb, b);
  }
  Lib_Memzero0_memzero(b, 128U, uint8_t, void *);
}

/* SNIPPET_END: update_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_update_multi */

void
Hacl_Hash_Blake2b_Simd256_update_multi(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks,
  uint32_t nb
)
{
  KRML_MAYBE_UNUSED_VAR(len);
  for (uint32_t i = 0U; i < nb; i++)
  {
    FStar_UInt128_uint128
    totlen =
      FStar_UInt128_add_mod(prev,
        FStar_UInt128_uint64_to_uint128((uint64_t)((i + 1U) * 128U)));
    uint8_t *b = blocks + i * 128U;
    update_block(wv, hash, false, totlen, b);
  }
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_update_multi */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_update_last */

void
Hacl_Hash_Blake2b_Simd256_update_last(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint32_t rem,
  uint8_t *d
)
{
  uint8_t b[128U] = { 0U };
  uint8_t *last = d + len - rem;
  memcpy(b, last, rem * sizeof (uint8_t));
  FStar_UInt128_uint128
  totlen = FStar_UInt128_add_mod(prev, FStar_UInt128_uint64_to_uint128((uint64_t)len));
  update_block(wv, hash, true, totlen, b);
  Lib_Memzero0_memzero(b, 128U, uint8_t, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_update_last */

/* SNIPPET_START: update_blocks */

static inline void
update_blocks(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks
)
{
  uint32_t nb0 = len / 128U;
  uint32_t rem0 = len % 128U;
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
    rem = 128U;
  }
  else
  {
    rem = rem0;
  }
  Hacl_Hash_Blake2b_Simd256_update_multi(len, wv, hash, prev, blocks, nb);
  Hacl_Hash_Blake2b_Simd256_update_last(len, wv, hash, prev, rem, blocks);
}

/* SNIPPET_END: update_blocks */

/* SNIPPET_START: update */

static inline void
update(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t ll,
  uint8_t *d
)
{
  FStar_UInt128_uint128 lb = FStar_UInt128_uint64_to_uint128((uint64_t)128U);
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
  update_blocks(ll, wv, hash, FStar_UInt128_uint64_to_uint128((uint64_t)0U), d);
}

/* SNIPPET_END: update */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_finish */

void
Hacl_Hash_Blake2b_Simd256_finish(
  uint32_t nn,
  uint8_t *output,
  Lib_IntVector_Intrinsics_vec256 *hash
)
{
  uint8_t b[64U] = { 0U };
  uint8_t *first = b;
  uint8_t *second = b + 32U;
  Lib_IntVector_Intrinsics_vec256 *row0 = hash;
  Lib_IntVector_Intrinsics_vec256 *row1 = hash + 1U;
  Lib_IntVector_Intrinsics_vec256_store64_le(first, row0[0U]);
  Lib_IntVector_Intrinsics_vec256_store64_le(second, row1[0U]);
  uint8_t *final = b;
  memcpy(output, final, nn * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, 64U, uint8_t, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_finish */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_load_state256b_from_state32 */

void
Hacl_Hash_Blake2b_Simd256_load_state256b_from_state32(
  Lib_IntVector_Intrinsics_vec256 *st,
  uint64_t *st32
)
{
  Lib_IntVector_Intrinsics_vec256 *r0 = st;
  Lib_IntVector_Intrinsics_vec256 *r1 = st + 1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = st + 2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = st + 3U;
  uint64_t *b0 = st32;
  uint64_t *b1 = st32 + 4U;
  uint64_t *b2 = st32 + 8U;
  uint64_t *b3 = st32 + 12U;
  r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(b0[0U], b0[1U], b0[2U], b0[3U]);
  r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(b1[0U], b1[1U], b1[2U], b1[3U]);
  r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(b2[0U], b2[1U], b2[2U], b2[3U]);
  r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(b3[0U], b3[1U], b3[2U], b3[3U]);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_load_state256b_from_state32 */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_store_state256b_to_state32 */

void
Hacl_Hash_Blake2b_Simd256_store_state256b_to_state32(
  uint64_t *st32,
  Lib_IntVector_Intrinsics_vec256 *st
)
{
  Lib_IntVector_Intrinsics_vec256 *r0 = st;
  Lib_IntVector_Intrinsics_vec256 *r1 = st + 1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = st + 2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = st + 3U;
  uint64_t *b0 = st32;
  uint64_t *b1 = st32 + 4U;
  uint64_t *b2 = st32 + 8U;
  uint64_t *b3 = st32 + 12U;
  uint8_t b8[32U] = { 0U };
  Lib_IntVector_Intrinsics_vec256_store64_le(b8, r0[0U]);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = b0;
    uint8_t *bj = b8 + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  uint8_t b80[32U] = { 0U };
  Lib_IntVector_Intrinsics_vec256_store64_le(b80, r1[0U]);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = b1;
    uint8_t *bj = b80 + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  uint8_t b81[32U] = { 0U };
  Lib_IntVector_Intrinsics_vec256_store64_le(b81, r2[0U]);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = b2;
    uint8_t *bj = b81 + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  uint8_t b82[32U] = { 0U };
  Lib_IntVector_Intrinsics_vec256_store64_le(b82, r3[0U]);
  KRML_MAYBE_FOR4(i,
    0U,
    4U,
    1U,
    uint64_t *os = b3;
    uint8_t *bj = b82 + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_store_state256b_to_state32 */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_malloc_with_key */

Lib_IntVector_Intrinsics_vec256 *Hacl_Hash_Blake2b_Simd256_malloc_with_key(void)
{
  Lib_IntVector_Intrinsics_vec256
  *buf =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * 4U);
  memset(buf, 0U, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  return buf;
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_malloc_with_key */

/* SNIPPET_START: malloc_raw */

static Hacl_Hash_Blake2b_Simd256_state_t
*malloc_raw(
  Hacl_Hash_Blake2b_index kk,
  K____Hacl_Impl_Blake2_Core_blake2_params___uint8_t_ key
)
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(128U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256
  *wv =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * 4U);
  memset(wv, 0U, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Lib_IntVector_Intrinsics_vec256
  *b =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * 4U);
  memset(b, 0U, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Hacl_Hash_Blake2b_Simd256_block_state_t
  block_state = { .fst = kk.key_length, .snd = kk.digest_length, .thd = { .fst = wv, .snd = b } };
  uint8_t kk10 = kk.key_length;
  uint32_t ite;
  if (kk10 != 0U)
  {
    ite = 128U;
  }
  else
  {
    ite = 0U;
  }
  Hacl_Hash_Blake2b_Simd256_state_t
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)ite };
  Hacl_Hash_Blake2b_Simd256_state_t
  *p =
    (Hacl_Hash_Blake2b_Simd256_state_t *)KRML_HOST_MALLOC(sizeof (
        Hacl_Hash_Blake2b_Simd256_state_t
      ));
  p[0U] = s;
  Hacl_Hash_Blake2b_blake2_params *p1 = key.fst;
  uint8_t kk1 = p1->key_length;
  uint8_t nn = p1->digest_length;
  Hacl_Hash_Blake2b_index i = { .key_length = kk1, .digest_length = nn };
  uint32_t kk2 = (uint32_t)i.key_length;
  uint8_t *k_1 = key.snd;
  if (!(kk2 == 0U))
  {
    uint8_t *sub_b = buf + kk2;
    memset(sub_b, 0U, (128U - kk2) * sizeof (uint8_t));
    memcpy(buf, k_1, kk2 * sizeof (uint8_t));
  }
  Hacl_Hash_Blake2b_blake2_params pv = p1[0U];
  init_with_params(block_state.thd.snd, pv);
  return p;
}

/* SNIPPET_END: malloc_raw */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key */

/**
 State allocation function when there are parameters and a key. The
length of the key k MUST match the value of the field key_length in the
parameters. Furthermore, there is a static (not dynamically checked) requirement
that key_length does not exceed max_key (256 for S, 64 for B).)
*/
Hacl_Hash_Blake2b_Simd256_state_t
*Hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key(
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
)
{
  Hacl_Hash_Blake2b_blake2_params pv = p[0U];
  Hacl_Hash_Blake2b_index
  i1 = { .key_length = pv.key_length, .digest_length = pv.digest_length };
  return
    malloc_raw(i1,
      ((K____Hacl_Impl_Blake2_Core_blake2_params___uint8_t_){ .fst = p, .snd = k }));
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_malloc_with_key0 */

/**
 State allocation function when there is just a custom key. All
other parameters are set to their respective default values, meaning the output
length is the maximum allowed output (256 for S, 64 for B).
*/
Hacl_Hash_Blake2b_Simd256_state_t
*Hacl_Hash_Blake2b_Simd256_malloc_with_key0(uint8_t *k, uint8_t kk)
{
  uint8_t nn = 64U;
  Hacl_Hash_Blake2b_index i = { .key_length = kk, .digest_length = nn };
  uint8_t *salt = (uint8_t *)KRML_HOST_CALLOC(16U, sizeof (uint8_t));
  uint8_t *personal = (uint8_t *)KRML_HOST_CALLOC(16U, sizeof (uint8_t));
  Hacl_Hash_Blake2b_blake2_params
  p =
    {
      .digest_length = i.digest_length, .key_length = i.key_length, .fanout = 1U, .depth = 1U,
      .leaf_length = 0U, .node_offset = 0ULL, .node_depth = 0U, .inner_length = 0U, .salt = salt,
      .personal = personal
    };
  Hacl_Hash_Blake2b_blake2_params
  *p0 =
    (Hacl_Hash_Blake2b_blake2_params *)KRML_HOST_MALLOC(sizeof (Hacl_Hash_Blake2b_blake2_params));
  p0[0U] = p;
  Hacl_Hash_Blake2b_Simd256_state_t
  *s = Hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key(p0, k);
  Hacl_Hash_Blake2b_blake2_params p1 = p0[0U];
  KRML_HOST_FREE(p1.salt);
  KRML_HOST_FREE(p1.personal);
  KRML_HOST_FREE(p0);
  return s;
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_malloc_with_key0 */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_malloc */

/**
  State allocation function when there is no key
*/
Hacl_Hash_Blake2b_Simd256_state_t *Hacl_Hash_Blake2b_Simd256_malloc(void)
{
  return Hacl_Hash_Blake2b_Simd256_malloc_with_key0(NULL, 0U);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_malloc */

/* SNIPPET_START: index_of_state */

static Hacl_Hash_Blake2b_index index_of_state(Hacl_Hash_Blake2b_Simd256_state_t *s)
{
  Hacl_Hash_Blake2b_Simd256_block_state_t block_state = (*s).block_state;
  uint8_t nn = block_state.snd;
  uint8_t kk1 = block_state.fst;
  return ((Hacl_Hash_Blake2b_index){ .key_length = kk1, .digest_length = nn });
}

/* SNIPPET_END: index_of_state */

/* SNIPPET_START: reset_raw */

static void
reset_raw(
  Hacl_Hash_Blake2b_Simd256_state_t *state,
  K____Hacl_Impl_Blake2_Core_blake2_params___uint8_t_ key
)
{
  Hacl_Hash_Blake2b_Simd256_state_t scrut = *state;
  uint8_t *buf = scrut.buf;
  Hacl_Hash_Blake2b_Simd256_block_state_t block_state = scrut.block_state;
  uint8_t nn0 = block_state.snd;
  uint8_t kk10 = block_state.fst;
  Hacl_Hash_Blake2b_index i = { .key_length = kk10, .digest_length = nn0 };
  KRML_MAYBE_UNUSED_VAR(i);
  Hacl_Hash_Blake2b_blake2_params *p = key.fst;
  uint8_t kk1 = p->key_length;
  uint8_t nn = p->digest_length;
  Hacl_Hash_Blake2b_index i1 = { .key_length = kk1, .digest_length = nn };
  uint32_t kk2 = (uint32_t)i1.key_length;
  uint8_t *k_1 = key.snd;
  if (!(kk2 == 0U))
  {
    uint8_t *sub_b = buf + kk2;
    memset(sub_b, 0U, (128U - kk2) * sizeof (uint8_t));
    memcpy(buf, k_1, kk2 * sizeof (uint8_t));
  }
  Hacl_Hash_Blake2b_blake2_params pv = p[0U];
  init_with_params(block_state.thd.snd, pv);
  uint8_t kk11 = i.key_length;
  uint32_t ite;
  if (kk11 != 0U)
  {
    ite = 128U;
  }
  else
  {
    ite = 0U;
  }
  Hacl_Hash_Blake2b_Simd256_state_t
  tmp = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)ite };
  state[0U] = tmp;
}

/* SNIPPET_END: reset_raw */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_reset_with_key_and_params */

/**
 Re-initialization function. The reinitialization API is tricky --
you MUST reuse the same original parameters for digest (output) length and key
length.
*/
void
Hacl_Hash_Blake2b_Simd256_reset_with_key_and_params(
  Hacl_Hash_Blake2b_Simd256_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
)
{
  index_of_state(s);
  reset_raw(s, ((K____Hacl_Impl_Blake2_Core_blake2_params___uint8_t_){ .fst = p, .snd = k }));
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_reset_with_key_and_params */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_reset_with_key */

/**
 Re-initialization function when there is a key. Note that the key
size is not allowed to change, which is why this function does not take a key
length -- the key has to be same key size that was originally passed to
`malloc_with_key`
*/
void Hacl_Hash_Blake2b_Simd256_reset_with_key(Hacl_Hash_Blake2b_Simd256_state_t *s, uint8_t *k)
{
  Hacl_Hash_Blake2b_index idx = index_of_state(s);
  uint8_t salt[16U] = { 0U };
  uint8_t personal[16U] = { 0U };
  Hacl_Hash_Blake2b_blake2_params
  p =
    {
      .digest_length = idx.digest_length, .key_length = idx.key_length, .fanout = 1U, .depth = 1U,
      .leaf_length = 0U, .node_offset = 0ULL, .node_depth = 0U, .inner_length = 0U, .salt = salt,
      .personal = personal
    };
  Hacl_Hash_Blake2b_blake2_params p0 = p;
  reset_raw(s, ((K____Hacl_Impl_Blake2_Core_blake2_params___uint8_t_){ .fst = &p0, .snd = k }));
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_reset_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_reset */

/**
  Re-initialization function when there is no key
*/
void Hacl_Hash_Blake2b_Simd256_reset(Hacl_Hash_Blake2b_Simd256_state_t *s)
{
  Hacl_Hash_Blake2b_Simd256_reset_with_key(s, NULL);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_reset */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_update */

/**
  Update function when there is no key; 0 = success, 1 = max length exceeded
*/
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2b_Simd256_update(
  Hacl_Hash_Blake2b_Simd256_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
)
{
  Hacl_Hash_Blake2b_Simd256_state_t s = *state;
  uint64_t total_len = s.total_len;
  if ((uint64_t)chunk_len > 0xffffffffffffffffULL - total_len)
  {
    return Hacl_Streaming_Types_MaximumLengthExceeded;
  }
  uint32_t sz;
  if (total_len % (uint64_t)128U == 0ULL && total_len > 0ULL)
  {
    sz = 128U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)128U);
  }
  if (chunk_len <= 128U - sz)
  {
    Hacl_Hash_Blake2b_Simd256_state_t s1 = *state;
    Hacl_Hash_Blake2b_Simd256_block_state_t block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)128U == 0ULL && total_len1 > 0ULL)
    {
      sz1 = 128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)128U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, chunk, chunk_len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)chunk_len;
    *state
    =
      (
        (Hacl_Hash_Blake2b_Simd256_state_t){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
  }
  else if (sz == 0U)
  {
    Hacl_Hash_Blake2b_Simd256_state_t s1 = *state;
    Hacl_Hash_Blake2b_Simd256_block_state_t block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)128U == 0ULL && total_len1 > 0ULL)
    {
      sz1 = 128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)128U);
    }
    if (!(sz1 == 0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
      acc = block_state1.thd;
      Lib_IntVector_Intrinsics_vec256 *wv = acc.fst;
      Lib_IntVector_Intrinsics_vec256 *hash = acc.snd;
      uint32_t nb = 1U;
      Hacl_Hash_Blake2b_Simd256_update_multi(128U,
        wv,
        hash,
        FStar_UInt128_uint64_to_uint128(prevlen),
        buf,
        nb);
    }
    uint32_t ite;
    if ((uint64_t)chunk_len % (uint64_t)128U == 0ULL && (uint64_t)chunk_len > 0ULL)
    {
      ite = 128U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)chunk_len % (uint64_t)128U);
    }
    uint32_t n_blocks = (chunk_len - ite) / 128U;
    uint32_t data1_len = n_blocks * 128U;
    uint32_t data2_len = chunk_len - data1_len;
    uint8_t *data1 = chunk;
    uint8_t *data2 = chunk + data1_len;
    K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_ acc = block_state1.thd;
    Lib_IntVector_Intrinsics_vec256 *wv = acc.fst;
    Lib_IntVector_Intrinsics_vec256 *hash = acc.snd;
    uint32_t nb = data1_len / 128U;
    Hacl_Hash_Blake2b_Simd256_update_multi(data1_len,
      wv,
      hash,
      FStar_UInt128_uint64_to_uint128(total_len1),
      data1,
      nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Hash_Blake2b_Simd256_state_t){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)chunk_len
        }
      );
  }
  else
  {
    uint32_t diff = 128U - sz;
    uint8_t *chunk1 = chunk;
    uint8_t *chunk2 = chunk + diff;
    Hacl_Hash_Blake2b_Simd256_state_t s1 = *state;
    Hacl_Hash_Blake2b_Simd256_block_state_t block_state10 = s1.block_state;
    uint8_t *buf0 = s1.buf;
    uint64_t total_len10 = s1.total_len;
    uint32_t sz10;
    if (total_len10 % (uint64_t)128U == 0ULL && total_len10 > 0ULL)
    {
      sz10 = 128U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)128U);
    }
    uint8_t *buf2 = buf0 + sz10;
    memcpy(buf2, chunk1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *state
    =
      (
        (Hacl_Hash_Blake2b_Simd256_state_t){
          .block_state = block_state10,
          .buf = buf0,
          .total_len = total_len2
        }
      );
    Hacl_Hash_Blake2b_Simd256_state_t s10 = *state;
    Hacl_Hash_Blake2b_Simd256_block_state_t block_state1 = s10.block_state;
    uint8_t *buf = s10.buf;
    uint64_t total_len1 = s10.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)128U == 0ULL && total_len1 > 0ULL)
    {
      sz1 = 128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)128U);
    }
    if (!(sz1 == 0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
      acc = block_state1.thd;
      Lib_IntVector_Intrinsics_vec256 *wv = acc.fst;
      Lib_IntVector_Intrinsics_vec256 *hash = acc.snd;
      uint32_t nb = 1U;
      Hacl_Hash_Blake2b_Simd256_update_multi(128U,
        wv,
        hash,
        FStar_UInt128_uint64_to_uint128(prevlen),
        buf,
        nb);
    }
    uint32_t ite;
    if
    ((uint64_t)(chunk_len - diff) % (uint64_t)128U == 0ULL && (uint64_t)(chunk_len - diff) > 0ULL)
    {
      ite = 128U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)(chunk_len - diff) % (uint64_t)128U);
    }
    uint32_t n_blocks = (chunk_len - diff - ite) / 128U;
    uint32_t data1_len = n_blocks * 128U;
    uint32_t data2_len = chunk_len - diff - data1_len;
    uint8_t *data1 = chunk2;
    uint8_t *data2 = chunk2 + data1_len;
    K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_ acc = block_state1.thd;
    Lib_IntVector_Intrinsics_vec256 *wv = acc.fst;
    Lib_IntVector_Intrinsics_vec256 *hash = acc.snd;
    uint32_t nb = data1_len / 128U;
    Hacl_Hash_Blake2b_Simd256_update_multi(data1_len,
      wv,
      hash,
      FStar_UInt128_uint64_to_uint128(total_len1),
      data1,
      nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Hash_Blake2b_Simd256_state_t){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(chunk_len - diff)
        }
      );
  }
  return Hacl_Streaming_Types_Success;
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_update */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_digest */

/**
  Finish function when there is no key
*/
void
Hacl_Hash_Blake2b_Simd256_digest(Hacl_Hash_Blake2b_Simd256_state_t *state, uint8_t *output)
{
  Hacl_Hash_Blake2b_Simd256_block_state_t block_state0 = (*state).block_state;
  uint8_t nn = block_state0.snd;
  uint8_t kk1 = block_state0.fst;
  Hacl_Hash_Blake2b_index i = { .key_length = kk1, .digest_length = nn };
  Hacl_Hash_Blake2b_Simd256_state_t scrut = *state;
  Hacl_Hash_Blake2b_Simd256_block_state_t block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)128U == 0ULL && total_len > 0ULL)
  {
    r = 128U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)128U);
  }
  uint8_t *buf_1 = buf_;
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv0[4U] KRML_POST_ALIGN(32) = { 0U };
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 b[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Hash_Blake2b_Simd256_block_state_t
  tmp_block_state =
    { .fst = i.key_length, .snd = i.digest_length, .thd = { .fst = wv0, .snd = b } };
  Lib_IntVector_Intrinsics_vec256 *src_b = block_state.thd.snd;
  Lib_IntVector_Intrinsics_vec256 *dst_b = tmp_block_state.thd.snd;
  memcpy(dst_b, src_b, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % 128U == 0U && r > 0U)
  {
    ite = 128U;
  }
  else
  {
    ite = r % 128U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  acc0 = tmp_block_state.thd;
  Lib_IntVector_Intrinsics_vec256 *wv1 = acc0.fst;
  Lib_IntVector_Intrinsics_vec256 *hash0 = acc0.snd;
  uint32_t nb = 0U;
  Hacl_Hash_Blake2b_Simd256_update_multi(0U,
    wv1,
    hash0,
    FStar_UInt128_uint64_to_uint128(prev_len),
    buf_multi,
    nb);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  acc = tmp_block_state.thd;
  Lib_IntVector_Intrinsics_vec256 *wv = acc.fst;
  Lib_IntVector_Intrinsics_vec256 *hash = acc.snd;
  Hacl_Hash_Blake2b_Simd256_update_last(r,
    wv,
    hash,
    FStar_UInt128_uint64_to_uint128(prev_len_last),
    r,
    buf_last);
  uint8_t nn0 = tmp_block_state.snd;
  Hacl_Hash_Blake2b_Simd256_finish((uint32_t)nn0, output, tmp_block_state.thd.snd);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_digest */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_free */

/**
  Free state function when there is no key
*/
void Hacl_Hash_Blake2b_Simd256_free(Hacl_Hash_Blake2b_Simd256_state_t *state)
{
  Hacl_Hash_Blake2b_Simd256_state_t scrut = *state;
  uint8_t *buf = scrut.buf;
  Hacl_Hash_Blake2b_Simd256_block_state_t block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec256 *b = block_state.thd.snd;
  Lib_IntVector_Intrinsics_vec256 *wv = block_state.thd.fst;
  KRML_ALIGNED_FREE(wv);
  KRML_ALIGNED_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(state);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_free */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_copy */

/**
  Copying. The key length (or absence thereof) must match between source and destination.
*/
Hacl_Hash_Blake2b_Simd256_state_t
*Hacl_Hash_Blake2b_Simd256_copy(Hacl_Hash_Blake2b_Simd256_state_t *state)
{
  Hacl_Hash_Blake2b_Simd256_state_t scrut = *state;
  Hacl_Hash_Blake2b_Simd256_block_state_t block_state0 = scrut.block_state;
  uint8_t *buf0 = scrut.buf;
  uint64_t total_len0 = scrut.total_len;
  uint8_t nn = block_state0.snd;
  uint8_t kk1 = block_state0.fst;
  Hacl_Hash_Blake2b_index i = { .key_length = kk1, .digest_length = nn };
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(128U, sizeof (uint8_t));
  memcpy(buf, buf0, 128U * sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256
  *wv =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * 4U);
  memset(wv, 0U, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Lib_IntVector_Intrinsics_vec256
  *b =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * 4U);
  memset(b, 0U, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Hacl_Hash_Blake2b_Simd256_block_state_t
  block_state = { .fst = i.key_length, .snd = i.digest_length, .thd = { .fst = wv, .snd = b } };
  Lib_IntVector_Intrinsics_vec256 *src_b = block_state0.thd.snd;
  Lib_IntVector_Intrinsics_vec256 *dst_b = block_state.thd.snd;
  memcpy(dst_b, src_b, 4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Hacl_Hash_Blake2b_Simd256_state_t
  s = { .block_state = block_state, .buf = buf, .total_len = total_len0 };
  Hacl_Hash_Blake2b_Simd256_state_t
  *p =
    (Hacl_Hash_Blake2b_Simd256_state_t *)KRML_HOST_MALLOC(sizeof (
        Hacl_Hash_Blake2b_Simd256_state_t
      ));
  p[0U] = s;
  return p;
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_copy */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_hash_with_key */

/**
Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0.
*/
void
Hacl_Hash_Blake2b_Simd256_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
)
{
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 b[4U] KRML_POST_ALIGN(32) = { 0U };
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 b1[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Hash_Blake2b_Simd256_init(b, key_len, output_len);
  update(b1, b, key_len, key, input_len, input);
  Hacl_Hash_Blake2b_Simd256_finish(output_len, output, b);
  Lib_Memzero0_memzero(b1, 4U, Lib_IntVector_Intrinsics_vec256, void *);
  Lib_Memzero0_memzero(b, 4U, Lib_IntVector_Intrinsics_vec256, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_hash_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_Simd256_hash_with_key_and_paramas */

void
Hacl_Hash_Blake2b_Simd256_hash_with_key_and_paramas(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
)
{
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 b[4U] KRML_POST_ALIGN(32) = { 0U };
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 b1[4U] KRML_POST_ALIGN(32) = { 0U };
  uint64_t tmp[8U] = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r0 = b;
  Lib_IntVector_Intrinsics_vec256 *r1 = b + 1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = b + 2U;
  Lib_IntVector_Intrinsics_vec256 *r3 = b + 3U;
  uint64_t iv0 = Hacl_Hash_Blake2b_ivTable_B[0U];
  uint64_t iv1 = Hacl_Hash_Blake2b_ivTable_B[1U];
  uint64_t iv2 = Hacl_Hash_Blake2b_ivTable_B[2U];
  uint64_t iv3 = Hacl_Hash_Blake2b_ivTable_B[3U];
  uint64_t iv4 = Hacl_Hash_Blake2b_ivTable_B[4U];
  uint64_t iv5 = Hacl_Hash_Blake2b_ivTable_B[5U];
  uint64_t iv6 = Hacl_Hash_Blake2b_ivTable_B[6U];
  uint64_t iv7 = Hacl_Hash_Blake2b_ivTable_B[7U];
  r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  uint8_t kk = params.key_length;
  uint8_t nn = params.digest_length;
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint64_t *os = tmp + 4U;
    uint8_t *bj = params.salt + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  KRML_MAYBE_FOR2(i,
    0U,
    2U,
    1U,
    uint64_t *os = tmp + 6U;
    uint8_t *bj = params.personal + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;);
  tmp[0U] =
    (uint64_t)nn
    ^
      ((uint64_t)kk
      << 8U
      ^
        ((uint64_t)params.fanout
        << 16U
        ^ ((uint64_t)params.depth << 24U ^ (uint64_t)params.leaf_length << 32U)));
  tmp[1U] = params.node_offset;
  tmp[2U] = (uint64_t)params.node_depth ^ (uint64_t)params.inner_length << 8U;
  tmp[3U] = 0ULL;
  uint64_t tmp0 = tmp[0U];
  uint64_t tmp1 = tmp[1U];
  uint64_t tmp2 = tmp[2U];
  uint64_t tmp3 = tmp[3U];
  uint64_t tmp4 = tmp[4U];
  uint64_t tmp5 = tmp[5U];
  uint64_t tmp6 = tmp[6U];
  uint64_t tmp7 = tmp[7U];
  uint64_t iv0_ = iv0 ^ tmp0;
  uint64_t iv1_ = iv1 ^ tmp1;
  uint64_t iv2_ = iv2 ^ tmp2;
  uint64_t iv3_ = iv3 ^ tmp3;
  uint64_t iv4_ = iv4 ^ tmp4;
  uint64_t iv5_ = iv5 ^ tmp5;
  uint64_t iv6_ = iv6 ^ tmp6;
  uint64_t iv7_ = iv7 ^ tmp7;
  r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1_, iv2_, iv3_);
  r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4_, iv5_, iv6_, iv7_);
  update(b1, b, (uint32_t)params.key_length, key, input_len, input);
  Hacl_Hash_Blake2b_Simd256_finish((uint32_t)params.digest_length, output, b);
  Lib_Memzero0_memzero(b1, 4U, Lib_IntVector_Intrinsics_vec256, void *);
  Lib_Memzero0_memzero(b, 4U, Lib_IntVector_Intrinsics_vec256, void *);
}

/* SNIPPET_END: Hacl_Hash_Blake2b_Simd256_hash_with_key_and_paramas */

