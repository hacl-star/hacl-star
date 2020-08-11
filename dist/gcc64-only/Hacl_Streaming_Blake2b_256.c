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


#include "Hacl_Streaming_Blake2b_256.h"

typedef struct
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_____s
{
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_ block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____;

/*
  State allocation function when there is no key
*/
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
*Hacl_Streaming_Blake2b_256_blake2b_256_no_key_create_in()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256
  *wv = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256) * (uint32_t)4U);
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  Lib_IntVector_Intrinsics_vec256
  *b0 = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256) * (uint32_t)4U);
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    b0[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state = { .fst = wv, .snd = b0 };
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (
      Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
    ),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *p =
    KRML_HOST_MALLOC(sizeof (
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
      ));
  p[0U] = s;
  uint8_t b[128U] = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r00 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r10 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r20 = block_state.snd + (uint32_t)2U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r30 = block_state.snd + (uint32_t)3U * (uint32_t)1U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  uint64_t kk_shift_8 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1, iv2, iv3);
  r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  if (!((uint32_t)0U == (uint32_t)0U))
  {
    memcpy(b, NULL, (uint32_t)0U * sizeof (NULL[0U]));
    uint128_t totlen = (uint128_t)(uint64_t)(uint32_t)0U + (uint128_t)(uint64_t)(uint32_t)128U;
    uint8_t *b1 = b + (uint32_t)0U * (uint32_t)128U;
    uint64_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t *os = m_w;
      uint8_t *bj = b1 + i * (uint32_t)8U;
      uint64_t u = load64_le(bj);
      uint64_t r1 = u;
      uint64_t x = r1;
      os[i] = x;
    }
    Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask =
      Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
        (uint64_t)(totlen >> (uint32_t)64U),
        wv_14,
        wv_15);
    memcpy(block_state.fst,
      block_state.snd,
      (uint32_t)4U * (uint32_t)1U * sizeof (block_state.snd[0U]));
    Lib_IntVector_Intrinsics_vec256 *wv3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
    wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
    {
      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
      Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
      for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
        m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      Lib_IntVector_Intrinsics_vec256 *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
      uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
      uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
      uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
      uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
      uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
      uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
      uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
      uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
      uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
      uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
      uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
      uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
      r01[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
      r11[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
      r21[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
      r31[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s11], m_w[s13], m_w[s15]);
      Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t a = (uint32_t)0U;
      uint32_t b20 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state.fst + b20 * (uint32_t)1U;
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state.fst + a * (uint32_t)1U;
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r02);
      Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state.fst + d0 * (uint32_t)1U;
      wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state.fst + b20 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state.fst + c0 * (uint32_t)1U;
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r12);
      Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state.fst + b20 * (uint32_t)1U;
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state.fst + a * (uint32_t)1U;
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r22);
      Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state.fst + d0 * (uint32_t)1U;
      wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state.fst + b20 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state.fst + c0 * (uint32_t)1U;
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r32);
      Lib_IntVector_Intrinsics_vec256 *r13 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r23 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r33 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v00 = r13[0U];
      Lib_IntVector_Intrinsics_vec256
      v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
      r13[0U] = v1;
      Lib_IntVector_Intrinsics_vec256 v01 = r23[0U];
      Lib_IntVector_Intrinsics_vec256
      v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
      r23[0U] = v10;
      Lib_IntVector_Intrinsics_vec256 v02 = r33[0U];
      Lib_IntVector_Intrinsics_vec256
      v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
      r33[0U] = v11;
      uint32_t a0 = (uint32_t)0U;
      uint32_t b2 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r24 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r34 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a = block_state.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state.fst + b2 * (uint32_t)1U;
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state.fst + a0 * (uint32_t)1U;
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
      Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state.fst + d * (uint32_t)1U;
      wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state.fst + b2 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state.fst + c * (uint32_t)1U;
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
      Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state.fst + b2 * (uint32_t)1U;
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state.fst + a0 * (uint32_t)1U;
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r24);
      Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state.fst + d * (uint32_t)1U;
      wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state.fst + b2 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b = block_state.fst + c * (uint32_t)1U;
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r34);
      Lib_IntVector_Intrinsics_vec256 *r14 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v0 = r14[0U];
      Lib_IntVector_Intrinsics_vec256
      v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
      r14[0U] = v12;
      Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
      Lib_IntVector_Intrinsics_vec256
      v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
      r2[0U] = v13;
      Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
      Lib_IntVector_Intrinsics_vec256
      v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
      r3[0U] = v14;
    }
    Lib_IntVector_Intrinsics_vec256 *s0 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *s1 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r0 = block_state.fst + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r1 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
    s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r1[0U]);
    s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r3[0U]);
  }
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
  return p;
}

/*
  Update function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_update(
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)128U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)128U);
  }
  if (len <= (uint32_t)128U - sz)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)128U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (data[0U]));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)128U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      uint32_t nb = (uint32_t)1U;
      for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
      {
        uint64_t ite;
        if ((uint32_t)0U == (uint32_t)0U)
        {
          ite = prevlen;
        }
        else
        {
          ite = prevlen + (uint64_t)(uint32_t)128U;
        }
        uint128_t
        totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
        uint8_t *b = buf + i0 * (uint32_t)128U;
        uint64_t m_w[16U] = { 0U };
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
        {
          uint64_t *os = m_w;
          uint8_t *bj = b + i * (uint32_t)8U;
          uint64_t u = load64_le(bj);
          uint64_t r = u;
          uint64_t x = r;
          os[i] = x;
        }
        Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
        uint64_t wv_14 = (uint64_t)0U;
        uint64_t wv_15 = (uint64_t)0U;
        mask =
          Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
            (uint64_t)(totlen >> (uint32_t)64U),
            wv_14,
            wv_15);
        memcpy(block_state1.fst,
          block_state1.snd,
          (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
        Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
        {
          uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
          Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
          for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
            m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
          Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
          uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
          uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
          uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
          uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
          uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
          uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
          uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
          uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
          uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
          uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
          uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
          uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
          uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
          uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
          uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
          r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
          r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
          r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
          r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
          Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
          uint32_t a = (uint32_t)0U;
          uint32_t b10 = (uint32_t)1U;
          uint32_t c0 = (uint32_t)2U;
          uint32_t d0 = (uint32_t)3U;
          uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
          uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
          uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
          uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
          Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
          wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
          wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
          wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
          wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
          Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
          wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
          Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
          wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
          wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
          wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
          wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
          Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
          wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
          wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
          wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
          Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
          Lib_IntVector_Intrinsics_vec256
          v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
          r12[0U] = v1;
          Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
          Lib_IntVector_Intrinsics_vec256
          v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
          r22[0U] = v10;
          Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
          Lib_IntVector_Intrinsics_vec256
          v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
          r32[0U] = v11;
          uint32_t a0 = (uint32_t)0U;
          uint32_t b1 = (uint32_t)1U;
          uint32_t c = (uint32_t)2U;
          uint32_t d = (uint32_t)3U;
          uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
          uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
          uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
          uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
          Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
          wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
          wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
          wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
          wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
          Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
          wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
          wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
          wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
          Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
          wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
          wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
          wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
          wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
          Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
          wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
          wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
          wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
          Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
          Lib_IntVector_Intrinsics_vec256
          v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
          r13[0U] = v12;
          Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
          Lib_IntVector_Intrinsics_vec256
          v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
          r2[0U] = v13;
          Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
          Lib_IntVector_Intrinsics_vec256
          v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
          r3[0U] = v14;
        }
        Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
        s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
        s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
        s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
      }
    }
    uint32_t ite0;
    if ((uint64_t)len % (uint64_t)(uint32_t)128U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite0 = (uint32_t)128U;
    }
    else
    {
      ite0 = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U);
    }
    uint32_t n_blocks = (len - ite0) / (uint32_t)128U;
    uint32_t data1_len = n_blocks * (uint32_t)128U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    uint32_t nb = data1_len / (uint32_t)128U;
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
    {
      uint64_t ite;
      if ((uint32_t)0U == (uint32_t)0U)
      {
        ite = total_len1;
      }
      else
      {
        ite = total_len1 + (uint64_t)(uint32_t)128U;
      }
      uint128_t
      totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
      uint8_t *b = data1 + i0 * (uint32_t)128U;
      uint64_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[i] = x;
      }
      Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask =
        Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
          (uint64_t)(totlen >> (uint32_t)64U),
          wv_14,
          wv_15);
      memcpy(block_state1.fst,
        block_state1.snd,
        (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
      Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
        Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
        for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
        uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
        uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
        uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
        uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
        uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
        uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
        uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
        uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
        uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
        uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
        uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
        uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
        uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
        r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
        r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
        r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
        r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
        Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
        Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
        Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
        Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
        Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
        Lib_IntVector_Intrinsics_vec256
        v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
        r12[0U] = v1;
        Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
        Lib_IntVector_Intrinsics_vec256
        v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
        r22[0U] = v10;
        Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
        Lib_IntVector_Intrinsics_vec256
        v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
        r32[0U] = v11;
        uint32_t a0 = (uint32_t)0U;
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
        Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
        wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
        Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
        Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
        wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
        Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
        Lib_IntVector_Intrinsics_vec256
        v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
        r13[0U] = v12;
        Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
        Lib_IntVector_Intrinsics_vec256
        v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
        r2[0U] = v13;
        Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
        Lib_IntVector_Intrinsics_vec256
        v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
        r3[0U] = v14;
      }
      Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (data2[0U]));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)128U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s1 = *p;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state10 = s1.block_state;
  uint8_t *buf0 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)128U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)128U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (data1[0U]));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s16 = *p;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state1 = s16.block_state;
  uint8_t *buf = s16.buf;
  uint64_t total_len1 = s16.total_len;
  uint32_t sz1;
  if (total_len1 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len1 > (uint64_t)0U)
  {
    sz1 = (uint32_t)128U;
  }
  else
  {
    sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)128U);
  }
  if (!(sz1 == (uint32_t)0U))
  {
    uint64_t prevlen = total_len1 - (uint64_t)sz1;
    uint32_t nb = (uint32_t)1U;
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
    {
      uint64_t ite;
      if ((uint32_t)0U == (uint32_t)0U)
      {
        ite = prevlen;
      }
      else
      {
        ite = prevlen + (uint64_t)(uint32_t)128U;
      }
      uint128_t
      totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
      uint8_t *b = buf + i0 * (uint32_t)128U;
      uint64_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[i] = x;
      }
      Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask =
        Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
          (uint64_t)(totlen >> (uint32_t)64U),
          wv_14,
          wv_15);
      memcpy(block_state1.fst,
        block_state1.snd,
        (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
      Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
        Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
        for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
        uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
        uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
        uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
        uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
        uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
        uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
        uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
        uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
        uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
        uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
        uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
        uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
        uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
        r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
        r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
        r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
        r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
        Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
        Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
        Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
        Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
        Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
        Lib_IntVector_Intrinsics_vec256
        v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
        r12[0U] = v1;
        Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
        Lib_IntVector_Intrinsics_vec256
        v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
        r22[0U] = v10;
        Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
        Lib_IntVector_Intrinsics_vec256
        v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
        r32[0U] = v11;
        uint32_t a0 = (uint32_t)0U;
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
        Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
        wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
        Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
        Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
        wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
        Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
        Lib_IntVector_Intrinsics_vec256
        v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
        r13[0U] = v12;
        Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
        Lib_IntVector_Intrinsics_vec256
        v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
        r2[0U] = v13;
        Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
        Lib_IntVector_Intrinsics_vec256
        v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
        r3[0U] = v14;
      }
      Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
    }
  }
  uint32_t ite0;
  if
  (
    (uint64_t)(len - diff)
    % (uint64_t)(uint32_t)128U
    == (uint64_t)0U
    && (uint64_t)(len - diff) > (uint64_t)0U
  )
  {
    ite0 = (uint32_t)128U;
  }
  else
  {
    ite0 = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)128U);
  }
  uint32_t n_blocks = (len - diff - ite0) / (uint32_t)128U;
  uint32_t data1_len = n_blocks * (uint32_t)128U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  uint32_t nb = data1_len / (uint32_t)128U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
  {
    uint64_t ite;
    if ((uint32_t)0U == (uint32_t)0U)
    {
      ite = total_len1;
    }
    else
    {
      ite = total_len1 + (uint64_t)(uint32_t)128U;
    }
    uint128_t
    totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
    uint8_t *b = data11 + i0 * (uint32_t)128U;
    uint64_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t *os = m_w;
      uint8_t *bj = b + i * (uint32_t)8U;
      uint64_t u = load64_le(bj);
      uint64_t r = u;
      uint64_t x = r;
      os[i] = x;
    }
    Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask =
      Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
        (uint64_t)(totlen >> (uint32_t)64U),
        wv_14,
        wv_15);
    memcpy(block_state1.fst,
      block_state1.snd,
      (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
    Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
    wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
    {
      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
      Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
      for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
        m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
      uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
      uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
      uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
      uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
      uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
      uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
      uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
      uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
      uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
      uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
      uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
      uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
      uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
      r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
      r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
      r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
      r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
      Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t a = (uint32_t)0U;
      uint32_t b10 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
      Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
      wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
      Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
      Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
      wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
      Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
      Lib_IntVector_Intrinsics_vec256
      v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
      r12[0U] = v1;
      Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
      Lib_IntVector_Intrinsics_vec256
      v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
      r22[0U] = v10;
      Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
      Lib_IntVector_Intrinsics_vec256
      v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
      r32[0U] = v11;
      uint32_t a0 = (uint32_t)0U;
      uint32_t b1 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
      Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
      wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
      Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
      Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
      wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
      Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
      Lib_IntVector_Intrinsics_vec256
      v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
      r13[0U] = v12;
      Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
      Lib_IntVector_Intrinsics_vec256
      v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
      r2[0U] = v13;
      Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
      Lib_IntVector_Intrinsics_vec256
      v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
      r3[0U] = v14;
    }
    Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
    s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
    s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
  }
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (data21[0U]));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

/*
  Finish function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_finish(
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  scrut = *p;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)128U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)128U);
  }
  uint8_t *buf_1 = buf_;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec256 wv[(uint32_t)4U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
    wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec256 b0[(uint32_t)4U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
    b0[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  tmp_block_state = { .fst = wv, .snd = b0 };
  Lib_IntVector_Intrinsics_vec256 *src_b = block_state.snd;
  Lib_IntVector_Intrinsics_vec256 *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)4U * sizeof (src_b[0U]));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint8_t b2[128U] = { 0U };
  uint8_t *last = buf_1 + r - r;
  memcpy(b2, last, r * sizeof (last[0U]));
  uint64_t ite;
  if ((uint32_t)0U == (uint32_t)0U)
  {
    ite = prev_len;
  }
  else
  {
    ite = prev_len + (uint64_t)(uint32_t)128U;
  }
  uint128_t totlen = (uint128_t)ite + (uint128_t)(uint64_t)r;
  uint64_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t *os = m_w;
    uint8_t *bj = b2 + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
  uint64_t wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t wv_15 = (uint64_t)0U;
  mask =
    Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
      (uint64_t)(totlen >> (uint32_t)64U),
      wv_14,
      wv_15);
  memcpy(tmp_block_state.fst,
    tmp_block_state.snd,
    (uint32_t)4U * (uint32_t)1U * sizeof (tmp_block_state.snd[0U]));
  Lib_IntVector_Intrinsics_vec256 *wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
  wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
  {
    uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
    Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
      m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
    uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
    uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
    uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
    uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
    uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
    uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
    uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
    uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
    uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
    uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
    uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
    uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
    uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
    uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
    uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
    uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
    r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
    r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
    r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
    r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s11], m_w[s13], m_w[s15]);
    Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
    uint32_t a = (uint32_t)0U;
    uint32_t b10 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
    uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
    uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
    uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
    Lib_IntVector_Intrinsics_vec256 *wv_a0 = tmp_block_state.fst + a * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)1U;
    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b1 = tmp_block_state.fst + a * (uint32_t)1U;
    wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
    wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
    Lib_IntVector_Intrinsics_vec256 *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)1U;
    wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)1U;
    wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
    wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
    Lib_IntVector_Intrinsics_vec256 *wv_a4 = tmp_block_state.fst + a * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)1U;
    wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
    wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b5 = tmp_block_state.fst + a * (uint32_t)1U;
    wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
    wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
    Lib_IntVector_Intrinsics_vec256 *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)1U;
    wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)1U;
    wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
    wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
    Lib_IntVector_Intrinsics_vec256 *r12 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r22 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r32 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
    Lib_IntVector_Intrinsics_vec256
    v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
    r12[0U] = v1;
    Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
    Lib_IntVector_Intrinsics_vec256
    v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
    r22[0U] = v10;
    Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
    Lib_IntVector_Intrinsics_vec256
    v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
    r32[0U] = v11;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b1 = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
    uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
    uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
    uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
    Lib_IntVector_Intrinsics_vec256 *wv_a = tmp_block_state.fst + a0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)1U;
    wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
    wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a8 = tmp_block_state.fst + d * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)1U;
    wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
    wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
    Lib_IntVector_Intrinsics_vec256 *wv_a9 = tmp_block_state.fst + c * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b10 = tmp_block_state.fst + d * (uint32_t)1U;
    wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a10 = tmp_block_state.fst + b1 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b11 = tmp_block_state.fst + c * (uint32_t)1U;
    wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
    wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
    Lib_IntVector_Intrinsics_vec256 *wv_a11 = tmp_block_state.fst + a0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b12 = tmp_block_state.fst + b1 * (uint32_t)1U;
    wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
    wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a12 = tmp_block_state.fst + d * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b13 = tmp_block_state.fst + a0 * (uint32_t)1U;
    wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
    wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
    Lib_IntVector_Intrinsics_vec256 *wv_a13 = tmp_block_state.fst + c * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b14 = tmp_block_state.fst + d * (uint32_t)1U;
    wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a14 = tmp_block_state.fst + b1 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b = tmp_block_state.fst + c * (uint32_t)1U;
    wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
    wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
    Lib_IntVector_Intrinsics_vec256 *r13 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
    Lib_IntVector_Intrinsics_vec256
    v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
    r13[0U] = v12;
    Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
    Lib_IntVector_Intrinsics_vec256
    v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
    r2[0U] = v13;
    Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
    Lib_IntVector_Intrinsics_vec256
    v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
    r3[0U] = v14;
  }
  Lib_IntVector_Intrinsics_vec256 *s0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *s1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r0 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r1 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
  s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
  s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
  s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r1[0U]);
  s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r3[0U]);
  Lib_Memzero0_memzero(b2, (uint32_t)128U * sizeof (b2[0U]));
  uint32_t double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)8U;
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (b[0U]));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec256 *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256_store_le(first, row0[0U]);
  Lib_IntVector_Intrinsics_vec256_store_le(second, row1[0U]);
  uint8_t *final = b;
  memcpy(dst, final, (uint32_t)64U * sizeof (final[0U]));
  Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
}

/*
  Free state function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_free(
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *s
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  scrut = *s;
  uint8_t *buf = scrut.buf;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec256 *wv = block_state.fst;
  Lib_IntVector_Intrinsics_vec256 *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

/*
  State allocation function when using a (potentially null) key
*/
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
*Hacl_Streaming_Blake2b_256_blake2b_256_with_key_create_in(uint32_t key_size, uint8_t *k)
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256
  *wv = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256) * (uint32_t)4U);
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  Lib_IntVector_Intrinsics_vec256
  *b0 = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256) * (uint32_t)4U);
  for (uint32_t _i = 0U; _i < (uint32_t)4U; ++_i)
    b0[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state = { .fst = wv, .snd = b0 };
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (
      Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
    ),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *p =
    KRML_HOST_MALLOC(sizeof (
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
      ));
  p[0U] = s;
  uint8_t b[128U] = { 0U };
  Lib_IntVector_Intrinsics_vec256 *r00 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r10 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r20 = block_state.snd + (uint32_t)2U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r30 = block_state.snd + (uint32_t)3U * (uint32_t)1U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
  r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  uint64_t kk_shift_8 = (uint64_t)key_size << (uint32_t)8U;
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1, iv2, iv3);
  r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
  if (!(key_size == (uint32_t)0U))
  {
    memcpy(b, k, key_size * sizeof (k[0U]));
    uint128_t totlen = (uint128_t)(uint64_t)(uint32_t)0U + (uint128_t)(uint64_t)(uint32_t)128U;
    uint8_t *b1 = b + (uint32_t)0U * (uint32_t)128U;
    uint64_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t *os = m_w;
      uint8_t *bj = b1 + i * (uint32_t)8U;
      uint64_t u = load64_le(bj);
      uint64_t r1 = u;
      uint64_t x = r1;
      os[i] = x;
    }
    Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask =
      Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
        (uint64_t)(totlen >> (uint32_t)64U),
        wv_14,
        wv_15);
    memcpy(block_state.fst,
      block_state.snd,
      (uint32_t)4U * (uint32_t)1U * sizeof (block_state.snd[0U]));
    Lib_IntVector_Intrinsics_vec256 *wv3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
    wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
    {
      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
      Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
      for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
        m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      Lib_IntVector_Intrinsics_vec256 *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
      uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
      uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
      uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
      uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
      uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
      uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
      uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
      uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
      uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
      uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
      uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
      uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
      r01[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
      r11[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
      r21[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
      r31[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s11], m_w[s13], m_w[s15]);
      Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t a = (uint32_t)0U;
      uint32_t b20 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state.fst + b20 * (uint32_t)1U;
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state.fst + a * (uint32_t)1U;
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r02);
      Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state.fst + d0 * (uint32_t)1U;
      wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state.fst + b20 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state.fst + c0 * (uint32_t)1U;
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r12);
      Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state.fst + b20 * (uint32_t)1U;
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state.fst + a * (uint32_t)1U;
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r22);
      Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state.fst + d0 * (uint32_t)1U;
      wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state.fst + b20 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state.fst + c0 * (uint32_t)1U;
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r32);
      Lib_IntVector_Intrinsics_vec256 *r13 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r23 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r33 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v00 = r13[0U];
      Lib_IntVector_Intrinsics_vec256
      v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
      r13[0U] = v1;
      Lib_IntVector_Intrinsics_vec256 v01 = r23[0U];
      Lib_IntVector_Intrinsics_vec256
      v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
      r23[0U] = v10;
      Lib_IntVector_Intrinsics_vec256 v02 = r33[0U];
      Lib_IntVector_Intrinsics_vec256
      v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
      r33[0U] = v11;
      uint32_t a0 = (uint32_t)0U;
      uint32_t b2 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r24 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r34 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a = block_state.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state.fst + b2 * (uint32_t)1U;
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state.fst + a0 * (uint32_t)1U;
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
      Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state.fst + d * (uint32_t)1U;
      wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state.fst + b2 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state.fst + c * (uint32_t)1U;
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
      Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state.fst + b2 * (uint32_t)1U;
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state.fst + a0 * (uint32_t)1U;
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r24);
      Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state.fst + d * (uint32_t)1U;
      wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state.fst + b2 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b = block_state.fst + c * (uint32_t)1U;
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r34);
      Lib_IntVector_Intrinsics_vec256 *r14 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v0 = r14[0U];
      Lib_IntVector_Intrinsics_vec256
      v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
      r14[0U] = v12;
      Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
      Lib_IntVector_Intrinsics_vec256
      v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
      r2[0U] = v13;
      Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
      Lib_IntVector_Intrinsics_vec256
      v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
      r3[0U] = v14;
    }
    Lib_IntVector_Intrinsics_vec256 *s0 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *s1 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r0 = block_state.fst + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r1 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
    s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r1[0U]);
    s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r3[0U]);
  }
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
  return p;
}

/*
  Update function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)128U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)128U);
  }
  if (len <= (uint32_t)128U - sz)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)128U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (data[0U]));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)128U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)128U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      uint64_t prevlen = total_len1 - (uint64_t)sz1;
      uint32_t nb = (uint32_t)1U;
      for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
      {
        uint64_t ite;
        if (key_size == (uint32_t)0U)
        {
          ite = prevlen;
        }
        else
        {
          ite = prevlen + (uint64_t)(uint32_t)128U;
        }
        uint128_t
        totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
        uint8_t *b = buf + i0 * (uint32_t)128U;
        uint64_t m_w[16U] = { 0U };
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
        {
          uint64_t *os = m_w;
          uint8_t *bj = b + i * (uint32_t)8U;
          uint64_t u = load64_le(bj);
          uint64_t r = u;
          uint64_t x = r;
          os[i] = x;
        }
        Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
        uint64_t wv_14 = (uint64_t)0U;
        uint64_t wv_15 = (uint64_t)0U;
        mask =
          Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
            (uint64_t)(totlen >> (uint32_t)64U),
            wv_14,
            wv_15);
        memcpy(block_state1.fst,
          block_state1.snd,
          (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
        Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
        {
          uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
          Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
          for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
            m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
          Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
          uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
          uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
          uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
          uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
          uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
          uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
          uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
          uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
          uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
          uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
          uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
          uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
          uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
          uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
          uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
          r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
          r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
          r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
          r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
          Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
          uint32_t a = (uint32_t)0U;
          uint32_t b10 = (uint32_t)1U;
          uint32_t c0 = (uint32_t)2U;
          uint32_t d0 = (uint32_t)3U;
          uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
          uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
          uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
          uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
          Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
          wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
          wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
          wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
          wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
          Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
          wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
          Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
          wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
          wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
          wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
          wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
          Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
          wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
          wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
          wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
          Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
          Lib_IntVector_Intrinsics_vec256
          v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
          r12[0U] = v1;
          Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
          Lib_IntVector_Intrinsics_vec256
          v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
          r22[0U] = v10;
          Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
          Lib_IntVector_Intrinsics_vec256
          v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
          r32[0U] = v11;
          uint32_t a0 = (uint32_t)0U;
          uint32_t b1 = (uint32_t)1U;
          uint32_t c = (uint32_t)2U;
          uint32_t d = (uint32_t)3U;
          uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
          uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
          uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
          uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
          Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
          wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
          wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
          wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
          wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
          Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
          wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
          wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
          wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
          Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
          wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
          wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
          wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
          wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
          Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
          wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
          Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
          wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
          wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
          Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
          Lib_IntVector_Intrinsics_vec256
          v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
          r13[0U] = v12;
          Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
          Lib_IntVector_Intrinsics_vec256
          v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
          r2[0U] = v13;
          Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
          Lib_IntVector_Intrinsics_vec256
          v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
          r3[0U] = v14;
        }
        Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
        s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
        s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
        s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
      }
    }
    uint32_t ite0;
    if ((uint64_t)len % (uint64_t)(uint32_t)128U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite0 = (uint32_t)128U;
    }
    else
    {
      ite0 = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U);
    }
    uint32_t n_blocks = (len - ite0) / (uint32_t)128U;
    uint32_t data1_len = n_blocks * (uint32_t)128U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    uint32_t nb = data1_len / (uint32_t)128U;
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
    {
      uint64_t ite;
      if (key_size == (uint32_t)0U)
      {
        ite = total_len1;
      }
      else
      {
        ite = total_len1 + (uint64_t)(uint32_t)128U;
      }
      uint128_t
      totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
      uint8_t *b = data1 + i0 * (uint32_t)128U;
      uint64_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[i] = x;
      }
      Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask =
        Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
          (uint64_t)(totlen >> (uint32_t)64U),
          wv_14,
          wv_15);
      memcpy(block_state1.fst,
        block_state1.snd,
        (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
      Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
        Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
        for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
        uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
        uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
        uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
        uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
        uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
        uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
        uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
        uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
        uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
        uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
        uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
        uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
        uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
        r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
        r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
        r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
        r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
        Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
        Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
        Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
        Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
        Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
        Lib_IntVector_Intrinsics_vec256
        v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
        r12[0U] = v1;
        Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
        Lib_IntVector_Intrinsics_vec256
        v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
        r22[0U] = v10;
        Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
        Lib_IntVector_Intrinsics_vec256
        v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
        r32[0U] = v11;
        uint32_t a0 = (uint32_t)0U;
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
        Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
        wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
        Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
        Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
        wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
        Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
        Lib_IntVector_Intrinsics_vec256
        v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
        r13[0U] = v12;
        Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
        Lib_IntVector_Intrinsics_vec256
        v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
        r2[0U] = v13;
        Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
        Lib_IntVector_Intrinsics_vec256
        v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
        r3[0U] = v14;
      }
      Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (data2[0U]));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)128U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s1 = *p;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state10 = s1.block_state;
  uint8_t *buf0 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)128U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)128U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (data1[0U]));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  s16 = *p;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state1 = s16.block_state;
  uint8_t *buf = s16.buf;
  uint64_t total_len1 = s16.total_len;
  uint32_t sz1;
  if (total_len1 % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len1 > (uint64_t)0U)
  {
    sz1 = (uint32_t)128U;
  }
  else
  {
    sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)128U);
  }
  if (!(sz1 == (uint32_t)0U))
  {
    uint64_t prevlen = total_len1 - (uint64_t)sz1;
    uint32_t nb = (uint32_t)1U;
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
    {
      uint64_t ite;
      if (key_size == (uint32_t)0U)
      {
        ite = prevlen;
      }
      else
      {
        ite = prevlen + (uint64_t)(uint32_t)128U;
      }
      uint128_t
      totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
      uint8_t *b = buf + i0 * (uint32_t)128U;
      uint64_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)8U;
        uint64_t u = load64_le(bj);
        uint64_t r = u;
        uint64_t x = r;
        os[i] = x;
      }
      Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask =
        Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
          (uint64_t)(totlen >> (uint32_t)64U),
          wv_14,
          wv_15);
      memcpy(block_state1.fst,
        block_state1.snd,
        (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
      Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
      {
        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
        Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
        for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
        uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
        uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
        uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
        uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
        uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
        uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
        uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
        uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
        uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
        uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
        uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
        uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
        uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
        r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
        r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
        r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
        r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
        Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
        wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
        wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
        Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
        wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
        Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
        wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
        wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
        Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
        wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
        wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
        Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
        Lib_IntVector_Intrinsics_vec256
        v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
        r12[0U] = v1;
        Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
        Lib_IntVector_Intrinsics_vec256
        v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
        r22[0U] = v10;
        Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
        Lib_IntVector_Intrinsics_vec256
        v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
        r32[0U] = v11;
        uint32_t a0 = (uint32_t)0U;
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
        uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
        uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
        uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
        Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
        wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
        wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
        Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
        wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
        wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
        Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
        wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
        wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
        Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
        wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
        Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
        wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
        Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
        Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
        Lib_IntVector_Intrinsics_vec256
        v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
        r13[0U] = v12;
        Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
        Lib_IntVector_Intrinsics_vec256
        v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
        r2[0U] = v13;
        Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
        Lib_IntVector_Intrinsics_vec256
        v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
        r3[0U] = v14;
      }
      Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
      s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
      s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
    }
  }
  uint32_t ite0;
  if
  (
    (uint64_t)(len - diff)
    % (uint64_t)(uint32_t)128U
    == (uint64_t)0U
    && (uint64_t)(len - diff) > (uint64_t)0U
  )
  {
    ite0 = (uint32_t)128U;
  }
  else
  {
    ite0 = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)128U);
  }
  uint32_t n_blocks = (len - diff - ite0) / (uint32_t)128U;
  uint32_t data1_len = n_blocks * (uint32_t)128U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  uint32_t nb = data1_len / (uint32_t)128U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
  {
    uint64_t ite;
    if (key_size == (uint32_t)0U)
    {
      ite = total_len1;
    }
    else
    {
      ite = total_len1 + (uint64_t)(uint32_t)128U;
    }
    uint128_t
    totlen = (uint128_t)ite + (uint128_t)(uint64_t)((i0 + (uint32_t)1U) * (uint32_t)128U);
    uint8_t *b = data11 + i0 * (uint32_t)128U;
    uint64_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t *os = m_w;
      uint8_t *bj = b + i * (uint32_t)8U;
      uint64_t u = load64_le(bj);
      uint64_t r = u;
      uint64_t x = r;
      os[i] = x;
    }
    Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask =
      Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
        (uint64_t)(totlen >> (uint32_t)64U),
        wv_14,
        wv_15);
    memcpy(block_state1.fst,
      block_state1.snd,
      (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
    Lib_IntVector_Intrinsics_vec256 *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
    wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
    {
      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
      Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
      for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
        m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
      uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
      uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
      uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
      uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
      uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
      uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
      uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
      uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
      uint32_t s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
      uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
      uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
      uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
      uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
      r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
      r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s11], m_w[s3], m_w[s5], m_w[s7]);
      r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
      r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s111], m_w[s13], m_w[s15]);
      Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
      uint32_t a = (uint32_t)0U;
      uint32_t b10 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a0 = block_state1.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
      wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b1 = block_state1.fst + a * (uint32_t)1U;
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
      Lib_IntVector_Intrinsics_vec256 *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
      wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
      wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
      Lib_IntVector_Intrinsics_vec256 *wv_a4 = block_state1.fst + a * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
      wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b5 = block_state1.fst + a * (uint32_t)1U;
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
      wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
      Lib_IntVector_Intrinsics_vec256 *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
      wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
      wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
      Lib_IntVector_Intrinsics_vec256 *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
      Lib_IntVector_Intrinsics_vec256
      v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
      r12[0U] = v1;
      Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
      Lib_IntVector_Intrinsics_vec256
      v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
      r22[0U] = v10;
      Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
      Lib_IntVector_Intrinsics_vec256
      v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
      r32[0U] = v11;
      uint32_t a0 = (uint32_t)0U;
      uint32_t b1 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
      uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
      uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
      uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
      Lib_IntVector_Intrinsics_vec256 *wv_a = block_state1.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
      wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a8 = block_state1.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
      wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
      Lib_IntVector_Intrinsics_vec256 *wv_a9 = block_state1.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b10 = block_state1.fst + d * (uint32_t)1U;
      wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b11 = block_state1.fst + c * (uint32_t)1U;
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
      wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
      Lib_IntVector_Intrinsics_vec256 *wv_a11 = block_state1.fst + a0 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b12 = block_state1.fst + b1 * (uint32_t)1U;
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
      wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a12 = block_state1.fst + d * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b13 = block_state1.fst + a0 * (uint32_t)1U;
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
      wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
      Lib_IntVector_Intrinsics_vec256 *wv_a13 = block_state1.fst + c * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b14 = block_state1.fst + d * (uint32_t)1U;
      wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
      Lib_IntVector_Intrinsics_vec256 *wv_a14 = block_state1.fst + b1 * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *wv_b = block_state1.fst + c * (uint32_t)1U;
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
      wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
      Lib_IntVector_Intrinsics_vec256 *r13 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
      Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
      Lib_IntVector_Intrinsics_vec256
      v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
      r13[0U] = v12;
      Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
      Lib_IntVector_Intrinsics_vec256
      v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
      r2[0U] = v13;
      Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
      Lib_IntVector_Intrinsics_vec256
      v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
      r3[0U] = v14;
    }
    Lib_IntVector_Intrinsics_vec256 *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
    s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
    s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r1[0U]);
    s11[0U] = Lib_IntVector_Intrinsics_vec256_xor(s11[0U], r3[0U]);
  }
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (data21[0U]));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

/*
  Finish function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_finish(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  scrut = *p;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)128U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)128U);
  }
  uint8_t *buf_1 = buf_;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec256 wv[(uint32_t)4U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
    wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
  Lib_IntVector_Intrinsics_vec256 b0[(uint32_t)4U * (uint32_t)1U];
  for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
    b0[_i] = Lib_IntVector_Intrinsics_vec256_zero;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  tmp_block_state = { .fst = wv, .snd = b0 };
  Lib_IntVector_Intrinsics_vec256 *src_b = block_state.snd;
  Lib_IntVector_Intrinsics_vec256 *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)4U * sizeof (src_b[0U]));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint8_t b2[128U] = { 0U };
  uint8_t *last = buf_1 + r - r;
  memcpy(b2, last, r * sizeof (last[0U]));
  uint64_t ite;
  if (key_size == (uint32_t)0U)
  {
    ite = prev_len;
  }
  else
  {
    ite = prev_len + (uint64_t)(uint32_t)128U;
  }
  uint128_t totlen = (uint128_t)ite + (uint128_t)(uint64_t)r;
  uint64_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t *os = m_w;
    uint8_t *bj = b2 + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
  uint64_t wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t wv_15 = (uint64_t)0U;
  mask =
    Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
      (uint64_t)(totlen >> (uint32_t)64U),
      wv_14,
      wv_15);
  memcpy(tmp_block_state.fst,
    tmp_block_state.snd,
    (uint32_t)4U * (uint32_t)1U * sizeof (tmp_block_state.snd[0U]));
  Lib_IntVector_Intrinsics_vec256 *wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
  wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)12U; i++)
  {
    uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
    Lib_IntVector_Intrinsics_vec256 m_st[(uint32_t)4U * (uint32_t)1U];
    for (uint32_t _i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
      m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    Lib_IntVector_Intrinsics_vec256 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
    uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
    uint32_t s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
    uint32_t s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
    uint32_t s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
    uint32_t s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
    uint32_t s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
    uint32_t s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
    uint32_t s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
    uint32_t s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
    uint32_t s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
    uint32_t s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
    uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
    uint32_t s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
    uint32_t s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
    uint32_t s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
    uint32_t s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
    r00[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
    r10[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
    r20[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s8], m_w[s10], m_w[s12], m_w[s14]);
    r30[0U] = Lib_IntVector_Intrinsics_vec256_load64s(m_w[s9], m_w[s11], m_w[s13], m_w[s15]);
    Lib_IntVector_Intrinsics_vec256 *x = m_st + (uint32_t)0U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *y = m_st + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *z = m_st + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *w = m_st + (uint32_t)3U * (uint32_t)1U;
    uint32_t a = (uint32_t)0U;
    uint32_t b10 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
    uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
    uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
    uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
    Lib_IntVector_Intrinsics_vec256 *wv_a0 = tmp_block_state.fst + a * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)1U;
    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b1 = tmp_block_state.fst + a * (uint32_t)1U;
    wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
    wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r01);
    Lib_IntVector_Intrinsics_vec256 *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)1U;
    wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)1U;
    wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
    wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r11);
    Lib_IntVector_Intrinsics_vec256 *wv_a4 = tmp_block_state.fst + a * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)1U;
    wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
    wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b5 = tmp_block_state.fst + a * (uint32_t)1U;
    wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
    wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U], r21);
    Lib_IntVector_Intrinsics_vec256 *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)1U;
    wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], wv_b6[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)1U;
    wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U], wv_b7[0U]);
    wv_a7[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U], r31);
    Lib_IntVector_Intrinsics_vec256 *r12 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r22 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r32 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 v00 = r12[0U];
    Lib_IntVector_Intrinsics_vec256
    v1 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00, (uint32_t)1U);
    r12[0U] = v1;
    Lib_IntVector_Intrinsics_vec256 v01 = r22[0U];
    Lib_IntVector_Intrinsics_vec256
    v10 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01, (uint32_t)2U);
    r22[0U] = v10;
    Lib_IntVector_Intrinsics_vec256 v02 = r32[0U];
    Lib_IntVector_Intrinsics_vec256
    v11 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02, (uint32_t)3U);
    r32[0U] = v11;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b1 = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint32_t r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
    uint32_t r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
    uint32_t r23 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
    uint32_t r33 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
    Lib_IntVector_Intrinsics_vec256 *wv_a = tmp_block_state.fst + a0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)1U;
    wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], wv_b8[0U]);
    wv_a[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U], z[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a8 = tmp_block_state.fst + d * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)1U;
    wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U], wv_b9[0U]);
    wv_a8[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U], r0);
    Lib_IntVector_Intrinsics_vec256 *wv_a9 = tmp_block_state.fst + c * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b10 = tmp_block_state.fst + d * (uint32_t)1U;
    wv_a9[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U], wv_b10[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a10 = tmp_block_state.fst + b1 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b11 = tmp_block_state.fst + c * (uint32_t)1U;
    wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U], wv_b11[0U]);
    wv_a10[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U], r1);
    Lib_IntVector_Intrinsics_vec256 *wv_a11 = tmp_block_state.fst + a0 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b12 = tmp_block_state.fst + b1 * (uint32_t)1U;
    wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], wv_b12[0U]);
    wv_a11[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U], w[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a12 = tmp_block_state.fst + d * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b13 = tmp_block_state.fst + a0 * (uint32_t)1U;
    wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U], wv_b13[0U]);
    wv_a12[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U], r23);
    Lib_IntVector_Intrinsics_vec256 *wv_a13 = tmp_block_state.fst + c * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b14 = tmp_block_state.fst + d * (uint32_t)1U;
    wv_a13[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U], wv_b14[0U]);
    Lib_IntVector_Intrinsics_vec256 *wv_a14 = tmp_block_state.fst + b1 * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *wv_b = tmp_block_state.fst + c * (uint32_t)1U;
    wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U], wv_b[0U]);
    wv_a14[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U], r33);
    Lib_IntVector_Intrinsics_vec256 *r13 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
    Lib_IntVector_Intrinsics_vec256 v0 = r13[0U];
    Lib_IntVector_Intrinsics_vec256
    v12 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0, (uint32_t)3U);
    r13[0U] = v12;
    Lib_IntVector_Intrinsics_vec256 v03 = r2[0U];
    Lib_IntVector_Intrinsics_vec256
    v13 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03, (uint32_t)2U);
    r2[0U] = v13;
    Lib_IntVector_Intrinsics_vec256 v04 = r3[0U];
    Lib_IntVector_Intrinsics_vec256
    v14 = Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04, (uint32_t)1U);
    r3[0U] = v14;
  }
  Lib_IntVector_Intrinsics_vec256 *s0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *s1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r0 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r1 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
  s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r0[0U]);
  s0[0U] = Lib_IntVector_Intrinsics_vec256_xor(s0[0U], r2[0U]);
  s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r1[0U]);
  s1[0U] = Lib_IntVector_Intrinsics_vec256_xor(s1[0U], r3[0U]);
  Lib_Memzero0_memzero(b2, (uint32_t)128U * sizeof (b2[0U]));
  uint32_t double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)8U;
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (b[0U]));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
  Lib_IntVector_Intrinsics_vec256 *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256 *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec256_store_le(first, row0[0U]);
  Lib_IntVector_Intrinsics_vec256_store_le(second, row1[0U]);
  uint8_t *final = b;
  memcpy(dst, final, (uint32_t)64U * sizeof (final[0U]));
  Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
}

/*
  Free state function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_free(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  *s
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256____
  scrut = *s;
  uint8_t *buf = scrut.buf;
  K____Lib_IntVector_Intrinsics_vec256___Lib_IntVector_Intrinsics_vec256_
  block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec256 *wv = block_state.fst;
  Lib_IntVector_Intrinsics_vec256 *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

