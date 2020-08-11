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


#include "Hacl_Streaming_Blake2s_128.h"

typedef struct
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_____s
{
  K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____;

/*
  State allocation function when there is no key
*/
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
*Hacl_Streaming_Blake2s_128_blake2s_128_no_key_create_in()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec128
  *wv = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec128) * (uint32_t)4U);
  {
    uint32_t _i;
    for (_i = 0U; _i < (uint32_t)4U; ++_i)
      wv[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec128
    *b0 = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec128) * (uint32_t)4U);
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)4U; ++_i)
        b0[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    }
    {
      K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ lit;
      K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ block_state;
      lit.fst = wv;
      lit.snd = b0;
      block_state = lit;
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        s;
        s.block_state = block_state;
        s.buf = buf;
        s.total_len = (uint64_t)0U;
        KRML_CHECK_SIZE(sizeof (
            Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
          ),
          (uint32_t)1U);
        {
          Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
          *p =
            KRML_HOST_MALLOC(sizeof (
                Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
              ));
          p[0U] = s;
          {
            uint8_t b[64U] = { 0U };
            Lib_IntVector_Intrinsics_vec128 *r00 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec128 *r10 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec128 *r20 = block_state.snd + (uint32_t)2U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec128 *r30 = block_state.snd + (uint32_t)3U * (uint32_t)1U;
            uint32_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
            uint32_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
            uint32_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
            uint32_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
            uint32_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
            uint32_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
            uint32_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
            uint32_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
            uint32_t kk_shift_8;
            uint32_t iv0_;
            r20[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
            r30[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
            kk_shift_8 = (uint32_t)0U;
            iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
            r00[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1, iv2, iv3);
            r10[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
            if (!((uint32_t)0U == (uint32_t)0U))
            {
              memcpy(b, NULL, (uint32_t)0U * sizeof (NULL[0U]));
              {
                uint64_t totlen = (uint64_t)(uint32_t)0U + (uint64_t)(uint32_t)64U;
                uint8_t *b1 = b + (uint32_t)0U * (uint32_t)64U;
                uint32_t m_w[16U] = { 0U };
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                  {
                    uint32_t *os = m_w;
                    uint8_t *bj = b1 + i * (uint32_t)4U;
                    uint32_t u = load32_le(bj);
                    uint32_t r1 = u;
                    uint32_t x = r1;
                    os[i] = x;
                  }
                }
                {
                  Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                  uint32_t wv_14 = (uint32_t)0U;
                  uint32_t wv_15 = (uint32_t)0U;
                  mask =
                    Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                      (uint32_t)(totlen >> (uint32_t)32U),
                      wv_14,
                      wv_15);
                  memcpy(block_state.fst,
                    block_state.snd,
                    (uint32_t)4U * (uint32_t)1U * sizeof (block_state.snd[0U]));
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *wv3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
                    wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                      {
                        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                          (uint32_t)4U * (uint32_t)1U);
                        {
                          Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                          {
                            uint32_t _i;
                            for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                              m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                          }
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                            uint32_t
                            s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                            uint32_t
                            s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                            uint32_t
                            s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                            uint32_t
                            s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                            uint32_t
                            s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                            uint32_t
                            s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                            uint32_t
                            s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                            uint32_t
                            s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                            uint32_t
                            s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                            uint32_t
                            s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                            uint32_t
                            s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                            uint32_t
                            s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                            uint32_t
                            s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                            uint32_t
                            s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                            uint32_t
                            s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                            r01[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                                m_w[s2],
                                m_w[s4],
                                m_w[s6]);
                            r11[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s1],
                                m_w[s3],
                                m_w[s5],
                                m_w[s7]);
                            r21[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                                m_w[s10],
                                m_w[s12],
                                m_w[s14]);
                            r31[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                                m_w[s11],
                                m_w[s13],
                                m_w[s15]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *x = m_st + (uint32_t)0U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *y = m_st + (uint32_t)1U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *z = m_st + (uint32_t)2U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *w = m_st + (uint32_t)3U * (uint32_t)1U;
                              uint32_t a = (uint32_t)0U;
                              uint32_t b20 = (uint32_t)1U;
                              uint32_t c0 = (uint32_t)2U;
                              uint32_t d0 = (uint32_t)3U;
                              uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                              uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                              uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                              uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a0 = block_state.fst + a * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b0 = block_state.fst + b20 * (uint32_t)1U;
                              wv_a0[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U],
                                  wv_b0[0U]);
                              wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a1 = block_state.fst + d0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b1 = block_state.fst + a * (uint32_t)1U;
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U],
                                    wv_b1[0U]);
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                    r02);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a2 = block_state.fst + c0 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b2 = block_state.fst + d0 * (uint32_t)1U;
                                  wv_a2[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                      wv_b2[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a3 = block_state.fst + b20 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b3 = block_state.fst + c0 * (uint32_t)1U;
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                        wv_b3[0U]);
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                        r12);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a4 = block_state.fst + a * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b4 = block_state.fst + b20 * (uint32_t)1U;
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          wv_b4[0U]);
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          y[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a5 = block_state.fst + d0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b5 = block_state.fst + a * (uint32_t)1U;
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                            wv_b5[0U]);
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                            r22);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a6 = block_state.fst + c0 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b6 = block_state.fst + d0 * (uint32_t)1U;
                                          wv_a6[0U] =
                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                              wv_b6[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_a7 = block_state.fst + b20 * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_b7 = block_state.fst + c0 * (uint32_t)1U;
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                                wv_b7[0U]);
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                                r32);
                                            {
                                              Lib_IntVector_Intrinsics_vec128
                                              *r13 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r23 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r33 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128 v00 = r13[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v1 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                  (uint32_t)1U);
                                              r13[0U] = v1;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v01 = r23[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v10 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                    (uint32_t)2U);
                                                r23[0U] = v10;
                                                {
                                                  Lib_IntVector_Intrinsics_vec128 v02 = r33[0U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  v11 =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                      (uint32_t)3U);
                                                  r33[0U] = v11;
                                                  {
                                                    uint32_t a0 = (uint32_t)0U;
                                                    uint32_t b2 = (uint32_t)1U;
                                                    uint32_t c = (uint32_t)2U;
                                                    uint32_t d = (uint32_t)3U;
                                                    uint32_t
                                                    r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                    uint32_t
                                                    r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                    uint32_t
                                                    r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                    uint32_t
                                                    r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a = block_state.fst + a0 * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b8 = block_state.fst + b2 * (uint32_t)1U;
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        wv_b8[0U]);
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        z[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a8 = block_state.fst + d * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b9 = block_state.fst + a0 * (uint32_t)1U;
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                          wv_b9[0U]);
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                          r0);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a9 = block_state.fst + c * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b10 = block_state.fst + d * (uint32_t)1U;
                                                        wv_a9[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                            wv_b10[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a10 =
                                                            block_state.fst
                                                            + b2 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b11 =
                                                            block_state.fst
                                                            + c * (uint32_t)1U;
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                              wv_b11[0U]);
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                              r1);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a11 =
                                                              block_state.fst
                                                              + a0 * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b12 =
                                                              block_state.fst
                                                              + b2 * (uint32_t)1U;
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                wv_b12[0U]);
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                w[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a12 =
                                                                block_state.fst
                                                                + d * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b13 =
                                                                block_state.fst
                                                                + a0 * (uint32_t)1U;
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                  wv_b13[0U]);
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                  r24);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a13 =
                                                                  block_state.fst
                                                                  + c * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b14 =
                                                                  block_state.fst
                                                                  + d * (uint32_t)1U;
                                                                wv_a13[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                    wv_b14[0U]);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_a14 =
                                                                    block_state.fst
                                                                    + b2 * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_b =
                                                                    block_state.fst
                                                                    + c * (uint32_t)1U;
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                      wv_b[0U]);
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                      r34);
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r14 =
                                                                      block_state.fst
                                                                      + (uint32_t)1U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r2 =
                                                                      block_state.fst
                                                                      + (uint32_t)2U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r3 =
                                                                      block_state.fst
                                                                      + (uint32_t)3U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v0 = r14[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v12 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                        (uint32_t)3U);
                                                                    r14[0U] = v12;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v03 = r2[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v13 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                          (uint32_t)2U);
                                                                      r2[0U] = v13;
                                                                      {
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v04 = r3[0U];
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v14 =
                                                                          Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                            (uint32_t)1U);
                                                                        r3[0U] = v14;
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
                              }
                            }
                          }
                        }
                      }
                    }
                    {
                      Lib_IntVector_Intrinsics_vec128
                      *s0 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *s1 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r0 = block_state.fst + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r1 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r2 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                      s1[0U] = Lib_IntVector_Intrinsics_vec128_xor(s1[0U], r1[0U]);
                      s1[0U] = Lib_IntVector_Intrinsics_vec128_xor(s1[0U], r3[0U]);
                    }
                  }
                }
              }
            }
            Lib_Memzero0_memzero(b, (uint32_t)64U * sizeof (b[0U]));
            return p;
          }
        }
      }
    }
  }
}

/*
  Update function when there is no key
*/
void
Hacl_Streaming_Blake2s_128_blake2s_128_no_key_update(
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)64U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  if (len <= (uint32_t)64U - sz)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    {
      uint8_t *buf2 = buf + sz1;
      uint64_t total_len2;
      memcpy(buf2, data, len * sizeof (data[0U]));
      total_len2 = total_len1 + (uint64_t)len;
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len2;
        *p = lit;
        return;
      }
    }
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    {
      uint32_t ite0;
      uint32_t n_blocks;
      uint32_t data1_len;
      uint32_t data2_len;
      uint8_t *data1;
      uint8_t *data2;
      uint32_t nb0;
      uint8_t *dst;
      if (!(sz1 == (uint32_t)0U))
      {
        uint64_t prevlen = total_len1 - (uint64_t)sz1;
        uint32_t nb = (uint32_t)1U;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < nb; i0++)
          {
            uint64_t ite;
            if ((uint32_t)0U == (uint32_t)0U)
            {
              ite = prevlen;
            }
            else
            {
              ite = prevlen + (uint64_t)(uint32_t)64U;
            }
            {
              uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
              uint8_t *b = buf + i0 * (uint32_t)64U;
              uint32_t m_w[16U] = { 0U };
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  uint32_t *os = m_w;
                  uint8_t *bj = b + i * (uint32_t)4U;
                  uint32_t u = load32_le(bj);
                  uint32_t r = u;
                  uint32_t x = r;
                  os[i] = x;
                }
              }
              {
                Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                uint32_t wv_14 = (uint32_t)0U;
                uint32_t wv_15 = (uint32_t)0U;
                mask =
                  Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                    (uint32_t)(totlen >> (uint32_t)32U),
                    wv_14,
                    wv_15);
                memcpy(block_state1.fst,
                  block_state1.snd,
                  (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
                {
                  Lib_IntVector_Intrinsics_vec128
                  *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                  wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                  {
                    uint32_t i;
                    for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                    {
                      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                        (uint32_t)4U * (uint32_t)1U);
                      {
                        Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                        {
                          uint32_t _i;
                          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                            m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                        }
                        {
                          Lib_IntVector_Intrinsics_vec128 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                          uint32_t
                          s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                          uint32_t
                          s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                          uint32_t
                          s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                          uint32_t
                          s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                          uint32_t
                          s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                          uint32_t
                          s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                          uint32_t
                          s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                          uint32_t
                          s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                          uint32_t
                          s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                          uint32_t
                          s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                          uint32_t
                          s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                          uint32_t
                          s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                          uint32_t
                          s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                          uint32_t
                          s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                          uint32_t
                          s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                          r00[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                              m_w[s2],
                              m_w[s4],
                              m_w[s6]);
                          r10[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                              m_w[s3],
                              m_w[s5],
                              m_w[s7]);
                          r20[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                              m_w[s10],
                              m_w[s12],
                              m_w[s14]);
                          r30[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                              m_w[s111],
                              m_w[s13],
                              m_w[s15]);
                          {
                            Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t a = (uint32_t)0U;
                            uint32_t b10 = (uint32_t)1U;
                            uint32_t c0 = (uint32_t)2U;
                            uint32_t d0 = (uint32_t)3U;
                            uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                            uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                            uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                            uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                              wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                              wv_a1[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                  r01);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                                wv_a2[0U] =
                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                    wv_b2[0U]);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                      wv_b3[0U]);
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                      r11);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        wv_b4[0U]);
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        y[0U]);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                          wv_b5[0U]);
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                          r21);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                        wv_a6[0U] =
                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                            wv_b6[0U]);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                              wv_b7[0U]);
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                              r31);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v1 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                (uint32_t)1U);
                                            r12[0U] = v1;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v10 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                  (uint32_t)2U);
                                              r22[0U] = v10;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v11 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                    (uint32_t)3U);
                                                r32[0U] = v11;
                                                {
                                                  uint32_t a0 = (uint32_t)0U;
                                                  uint32_t b1 = (uint32_t)1U;
                                                  uint32_t c = (uint32_t)2U;
                                                  uint32_t d = (uint32_t)3U;
                                                  uint32_t
                                                  r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                  uint32_t
                                                  r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                  uint32_t
                                                  r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                  uint32_t
                                                  r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      wv_b8[0U]);
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      z[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                        wv_b9[0U]);
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                        r0);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b10 = block_state1.fst + d * (uint32_t)1U;
                                                      wv_a9[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                          wv_b10[0U]);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a10 =
                                                          block_state1.fst
                                                          + b1 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b11 =
                                                          block_state1.fst
                                                          + c * (uint32_t)1U;
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                            wv_b11[0U]);
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                            r1);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a11 =
                                                            block_state1.fst
                                                            + a0 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b12 =
                                                            block_state1.fst
                                                            + b1 * (uint32_t)1U;
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              wv_b12[0U]);
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              w[0U]);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a12 =
                                                              block_state1.fst
                                                              + d * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b13 =
                                                              block_state1.fst
                                                              + a0 * (uint32_t)1U;
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                wv_b13[0U]);
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                r23);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a13 =
                                                                block_state1.fst
                                                                + c * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b14 =
                                                                block_state1.fst
                                                                + d * (uint32_t)1U;
                                                              wv_a13[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                  wv_b14[0U]);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a14 =
                                                                  block_state1.fst
                                                                  + b1 * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b =
                                                                  block_state1.fst
                                                                  + c * (uint32_t)1U;
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                    wv_b[0U]);
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                    r33);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r13 =
                                                                    block_state1.fst
                                                                    + (uint32_t)1U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r2 =
                                                                    block_state1.fst
                                                                    + (uint32_t)2U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r3 =
                                                                    block_state1.fst
                                                                    + (uint32_t)3U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v0 = r13[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v12 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                      (uint32_t)3U);
                                                                  r13[0U] = v12;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v03 = r2[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v13 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                        (uint32_t)2U);
                                                                    r2[0U] = v13;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v04 = r3[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v14 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                          (uint32_t)1U);
                                                                      r3[0U] = v14;
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
                            }
                          }
                        }
                      }
                    }
                  }
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                  }
                }
              }
            }
          }
        }
      }
      if ((uint64_t)len % (uint64_t)(uint32_t)64U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
      {
        ite0 = (uint32_t)64U;
      }
      else
      {
        ite0 = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)64U);
      }
      n_blocks = (len - ite0) / (uint32_t)64U;
      data1_len = n_blocks * (uint32_t)64U;
      data2_len = len - data1_len;
      data1 = data;
      data2 = data + data1_len;
      nb0 = data1_len / (uint32_t)64U;
      {
        uint32_t i0;
        for (i0 = (uint32_t)0U; i0 < nb0; i0++)
        {
          uint64_t ite;
          if ((uint32_t)0U == (uint32_t)0U)
          {
            ite = total_len1;
          }
          else
          {
            ite = total_len1 + (uint64_t)(uint32_t)64U;
          }
          {
            uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
            uint8_t *b = data1 + i0 * (uint32_t)64U;
            uint32_t m_w[16U] = { 0U };
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                uint32_t *os = m_w;
                uint8_t *bj = b + i * (uint32_t)4U;
                uint32_t u = load32_le(bj);
                uint32_t r = u;
                uint32_t x = r;
                os[i] = x;
              }
            }
            {
              Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
              uint32_t wv_14 = (uint32_t)0U;
              uint32_t wv_15 = (uint32_t)0U;
              mask =
                Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                  (uint32_t)(totlen >> (uint32_t)32U),
                  wv_14,
                  wv_15);
              memcpy(block_state1.fst,
                block_state1.snd,
                (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
              {
                Lib_IntVector_Intrinsics_vec128
                *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                  {
                    uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                      (uint32_t)4U * (uint32_t)1U);
                    {
                      Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                      {
                        uint32_t _i;
                        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                          m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                      }
                      {
                        Lib_IntVector_Intrinsics_vec128 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                        uint32_t
                        s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                        uint32_t
                        s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                        uint32_t
                        s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                        uint32_t
                        s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                        uint32_t
                        s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                        uint32_t
                        s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                        uint32_t
                        s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                        uint32_t
                        s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                        uint32_t
                        s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                        uint32_t
                        s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                        uint32_t
                        s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                        uint32_t
                        s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                        uint32_t
                        s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                        uint32_t
                        s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                        uint32_t
                        s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                        r00[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                            m_w[s2],
                            m_w[s4],
                            m_w[s6]);
                        r10[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                            m_w[s3],
                            m_w[s5],
                            m_w[s7]);
                        r20[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                            m_w[s10],
                            m_w[s12],
                            m_w[s14]);
                        r30[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                            m_w[s111],
                            m_w[s13],
                            m_w[s15]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t a = (uint32_t)0U;
                          uint32_t b10 = (uint32_t)1U;
                          uint32_t c0 = (uint32_t)2U;
                          uint32_t d0 = (uint32_t)3U;
                          uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                          uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                          uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                          uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                          Lib_IntVector_Intrinsics_vec128
                          *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128
                          *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                            wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                            wv_a1[0U] =
                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                r01);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                              wv_a2[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                  wv_b2[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                    wv_b3[0U]);
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                    r11);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      wv_b4[0U]);
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      y[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                        wv_b5[0U]);
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                        r21);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                      wv_a6[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                          wv_b6[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                            wv_b7[0U]);
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                            r31);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                          Lib_IntVector_Intrinsics_vec128
                                          v1 =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                              (uint32_t)1U);
                                          r12[0U] = v1;
                                          {
                                            Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v10 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                (uint32_t)2U);
                                            r22[0U] = v10;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v11 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                  (uint32_t)3U);
                                              r32[0U] = v11;
                                              {
                                                uint32_t a0 = (uint32_t)0U;
                                                uint32_t b1 = (uint32_t)1U;
                                                uint32_t c = (uint32_t)2U;
                                                uint32_t d = (uint32_t)3U;
                                                uint32_t
                                                r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                uint32_t
                                                r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                uint32_t
                                                r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                uint32_t
                                                r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    wv_b8[0U]);
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    z[0U]);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                      wv_b9[0U]);
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                      r0);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b10 = block_state1.fst + d * (uint32_t)1U;
                                                    wv_a9[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                        wv_b10[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b11 = block_state1.fst + c * (uint32_t)1U;
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                          wv_b11[0U]);
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                          r1);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a11 =
                                                          block_state1.fst
                                                          + a0 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b12 =
                                                          block_state1.fst
                                                          + b1 * (uint32_t)1U;
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            wv_b12[0U]);
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            w[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a12 =
                                                            block_state1.fst
                                                            + d * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b13 =
                                                            block_state1.fst
                                                            + a0 * (uint32_t)1U;
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                              wv_b13[0U]);
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                              r23);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a13 =
                                                              block_state1.fst
                                                              + c * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b14 =
                                                              block_state1.fst
                                                              + d * (uint32_t)1U;
                                                            wv_a13[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                wv_b14[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a14 =
                                                                block_state1.fst
                                                                + b1 * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b =
                                                                block_state1.fst
                                                                + c * (uint32_t)1U;
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                  wv_b[0U]);
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                  r33);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r13 =
                                                                  block_state1.fst
                                                                  + (uint32_t)1U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r2 =
                                                                  block_state1.fst
                                                                  + (uint32_t)2U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r3 =
                                                                  block_state1.fst
                                                                  + (uint32_t)3U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v0 = r13[0U];
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v12 =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                    (uint32_t)3U);
                                                                r13[0U] = v12;
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v03 = r2[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v13 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                      (uint32_t)2U);
                                                                  r2[0U] = v13;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v04 = r3[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v14 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                        (uint32_t)1U);
                                                                    r3[0U] = v14;
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
                          }
                        }
                      }
                    }
                  }
                }
                {
                  Lib_IntVector_Intrinsics_vec128
                  *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                  s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                  s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                  s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                  s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                }
              }
            }
          }
        }
      }
      dst = buf;
      memcpy(dst, data2, data2_len * sizeof (data2[0U]));
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len1 + (uint64_t)len;
        *p = lit;
        return;
      }
    }
  }
  {
    uint32_t diff = (uint32_t)64U - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
    s16 = *p;
    K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
    block_state10 = s16.block_state;
    uint8_t *buf0 = s16.buf;
    uint64_t total_len10 = s16.total_len;
    uint32_t sz10;
    if (total_len10 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len10 > (uint64_t)0U)
    {
      sz10 = (uint32_t)64U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)64U);
    }
    {
      uint8_t *buf2 = buf0 + sz10;
      uint64_t total_len2;
      memcpy(buf2, data1, diff * sizeof (data1[0U]));
      total_len2 = total_len10 + (uint64_t)diff;
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        lit;
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        s1;
        K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ block_state1;
        uint8_t *buf;
        uint64_t total_len1;
        uint32_t sz1;
        uint32_t ite0;
        uint32_t n_blocks;
        uint32_t data1_len;
        uint32_t data2_len;
        uint8_t *data11;
        uint8_t *data21;
        uint32_t nb0;
        uint8_t *dst;
        lit.block_state = block_state10;
        lit.buf = buf0;
        lit.total_len = total_len2;
        *p = lit;
        s1 = *p;
        block_state1 = s1.block_state;
        buf = s1.buf;
        total_len1 = s1.total_len;
        if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
        {
          sz1 = (uint32_t)64U;
        }
        else
        {
          sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
        }
        if (!(sz1 == (uint32_t)0U))
        {
          uint64_t prevlen = total_len1 - (uint64_t)sz1;
          uint32_t nb = (uint32_t)1U;
          {
            uint32_t i0;
            for (i0 = (uint32_t)0U; i0 < nb; i0++)
            {
              uint64_t ite;
              if ((uint32_t)0U == (uint32_t)0U)
              {
                ite = prevlen;
              }
              else
              {
                ite = prevlen + (uint64_t)(uint32_t)64U;
              }
              {
                uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
                uint8_t *b = buf + i0 * (uint32_t)64U;
                uint32_t m_w[16U] = { 0U };
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                  {
                    uint32_t *os = m_w;
                    uint8_t *bj = b + i * (uint32_t)4U;
                    uint32_t u = load32_le(bj);
                    uint32_t r = u;
                    uint32_t x = r;
                    os[i] = x;
                  }
                }
                {
                  Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                  uint32_t wv_14 = (uint32_t)0U;
                  uint32_t wv_15 = (uint32_t)0U;
                  mask =
                    Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                      (uint32_t)(totlen >> (uint32_t)32U),
                      wv_14,
                      wv_15);
                  memcpy(block_state1.fst,
                    block_state1.snd,
                    (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                    wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                      {
                        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                          (uint32_t)4U * (uint32_t)1U);
                        {
                          Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                          {
                            uint32_t _i;
                            for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                              m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                          }
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                            uint32_t
                            s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                            uint32_t
                            s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                            uint32_t
                            s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                            uint32_t
                            s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                            uint32_t
                            s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                            uint32_t
                            s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                            uint32_t
                            s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                            uint32_t
                            s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                            uint32_t
                            s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                            uint32_t
                            s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                            uint32_t
                            s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                            uint32_t
                            s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                            uint32_t
                            s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                            uint32_t
                            s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                            uint32_t
                            s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                            r00[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                                m_w[s2],
                                m_w[s4],
                                m_w[s6]);
                            r10[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                                m_w[s3],
                                m_w[s5],
                                m_w[s7]);
                            r20[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                                m_w[s10],
                                m_w[s12],
                                m_w[s14]);
                            r30[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                                m_w[s111],
                                m_w[s13],
                                m_w[s15]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *x = m_st + (uint32_t)0U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *y = m_st + (uint32_t)1U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *z = m_st + (uint32_t)2U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *w = m_st + (uint32_t)3U * (uint32_t)1U;
                              uint32_t a = (uint32_t)0U;
                              uint32_t b10 = (uint32_t)1U;
                              uint32_t c0 = (uint32_t)2U;
                              uint32_t d0 = (uint32_t)3U;
                              uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                              uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                              uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                              uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                              wv_a0[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U],
                                  wv_b0[0U]);
                              wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U],
                                    wv_b1[0U]);
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                    r01);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                                  wv_a2[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                      wv_b2[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                        wv_b3[0U]);
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                        r11);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          wv_b4[0U]);
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          y[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                            wv_b5[0U]);
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                            r21);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                          wv_a6[0U] =
                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                              wv_b6[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                                wv_b7[0U]);
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                                r31);
                                            {
                                              Lib_IntVector_Intrinsics_vec128
                                              *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v1 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                  (uint32_t)1U);
                                              r12[0U] = v1;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v10 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                    (uint32_t)2U);
                                                r22[0U] = v10;
                                                {
                                                  Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  v11 =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                      (uint32_t)3U);
                                                  r32[0U] = v11;
                                                  {
                                                    uint32_t a0 = (uint32_t)0U;
                                                    uint32_t b1 = (uint32_t)1U;
                                                    uint32_t c = (uint32_t)2U;
                                                    uint32_t d = (uint32_t)3U;
                                                    uint32_t
                                                    r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                    uint32_t
                                                    r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                    uint32_t
                                                    r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                    uint32_t
                                                    r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        wv_b8[0U]);
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        z[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                          wv_b9[0U]);
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                          r0);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b10 =
                                                          block_state1.fst
                                                          + d * (uint32_t)1U;
                                                        wv_a9[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                            wv_b10[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a10 =
                                                            block_state1.fst
                                                            + b1 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b11 =
                                                            block_state1.fst
                                                            + c * (uint32_t)1U;
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                              wv_b11[0U]);
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                              r1);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a11 =
                                                              block_state1.fst
                                                              + a0 * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b12 =
                                                              block_state1.fst
                                                              + b1 * (uint32_t)1U;
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                wv_b12[0U]);
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                w[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a12 =
                                                                block_state1.fst
                                                                + d * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b13 =
                                                                block_state1.fst
                                                                + a0 * (uint32_t)1U;
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                  wv_b13[0U]);
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                  r23);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a13 =
                                                                  block_state1.fst
                                                                  + c * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b14 =
                                                                  block_state1.fst
                                                                  + d * (uint32_t)1U;
                                                                wv_a13[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                    wv_b14[0U]);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_a14 =
                                                                    block_state1.fst
                                                                    + b1 * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_b =
                                                                    block_state1.fst
                                                                    + c * (uint32_t)1U;
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                      wv_b[0U]);
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                      r33);
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r13 =
                                                                      block_state1.fst
                                                                      + (uint32_t)1U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r2 =
                                                                      block_state1.fst
                                                                      + (uint32_t)2U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r3 =
                                                                      block_state1.fst
                                                                      + (uint32_t)3U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v0 = r13[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v12 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                        (uint32_t)3U);
                                                                    r13[0U] = v12;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v03 = r2[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v13 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                          (uint32_t)2U);
                                                                      r2[0U] = v13;
                                                                      {
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v04 = r3[0U];
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v14 =
                                                                          Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                            (uint32_t)1U);
                                                                        r3[0U] = v14;
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
                              }
                            }
                          }
                        }
                      }
                    }
                    {
                      Lib_IntVector_Intrinsics_vec128
                      *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                      s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                      s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                    }
                  }
                }
              }
            }
          }
        }
        if
        (
          (uint64_t)(len - diff)
          % (uint64_t)(uint32_t)64U
          == (uint64_t)0U
          && (uint64_t)(len - diff) > (uint64_t)0U
        )
        {
          ite0 = (uint32_t)64U;
        }
        else
        {
          ite0 = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)64U);
        }
        n_blocks = (len - diff - ite0) / (uint32_t)64U;
        data1_len = n_blocks * (uint32_t)64U;
        data2_len = len - diff - data1_len;
        data11 = data2;
        data21 = data2 + data1_len;
        nb0 = data1_len / (uint32_t)64U;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < nb0; i0++)
          {
            uint64_t ite;
            if ((uint32_t)0U == (uint32_t)0U)
            {
              ite = total_len1;
            }
            else
            {
              ite = total_len1 + (uint64_t)(uint32_t)64U;
            }
            {
              uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
              uint8_t *b = data11 + i0 * (uint32_t)64U;
              uint32_t m_w[16U] = { 0U };
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  uint32_t *os = m_w;
                  uint8_t *bj = b + i * (uint32_t)4U;
                  uint32_t u = load32_le(bj);
                  uint32_t r = u;
                  uint32_t x = r;
                  os[i] = x;
                }
              }
              {
                Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                uint32_t wv_14 = (uint32_t)0U;
                uint32_t wv_15 = (uint32_t)0U;
                mask =
                  Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                    (uint32_t)(totlen >> (uint32_t)32U),
                    wv_14,
                    wv_15);
                memcpy(block_state1.fst,
                  block_state1.snd,
                  (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
                {
                  Lib_IntVector_Intrinsics_vec128
                  *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                  wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                  {
                    uint32_t i;
                    for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                    {
                      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                        (uint32_t)4U * (uint32_t)1U);
                      {
                        Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                        {
                          uint32_t _i;
                          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                            m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                        }
                        {
                          Lib_IntVector_Intrinsics_vec128 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                          uint32_t
                          s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                          uint32_t
                          s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                          uint32_t
                          s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                          uint32_t
                          s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                          uint32_t
                          s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                          uint32_t
                          s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                          uint32_t
                          s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                          uint32_t
                          s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                          uint32_t
                          s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                          uint32_t
                          s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                          uint32_t
                          s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                          uint32_t
                          s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                          uint32_t
                          s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                          uint32_t
                          s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                          uint32_t
                          s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                          r00[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                              m_w[s2],
                              m_w[s4],
                              m_w[s6]);
                          r10[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                              m_w[s3],
                              m_w[s5],
                              m_w[s7]);
                          r20[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                              m_w[s10],
                              m_w[s12],
                              m_w[s14]);
                          r30[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                              m_w[s111],
                              m_w[s13],
                              m_w[s15]);
                          {
                            Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t a = (uint32_t)0U;
                            uint32_t b10 = (uint32_t)1U;
                            uint32_t c0 = (uint32_t)2U;
                            uint32_t d0 = (uint32_t)3U;
                            uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                            uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                            uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                            uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                              wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                              wv_a1[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                  r01);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                                wv_a2[0U] =
                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                    wv_b2[0U]);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                      wv_b3[0U]);
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                      r11);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        wv_b4[0U]);
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        y[0U]);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                          wv_b5[0U]);
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                          r21);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                        wv_a6[0U] =
                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                            wv_b6[0U]);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                              wv_b7[0U]);
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                              r31);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v1 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                (uint32_t)1U);
                                            r12[0U] = v1;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v10 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                  (uint32_t)2U);
                                              r22[0U] = v10;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v11 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                    (uint32_t)3U);
                                                r32[0U] = v11;
                                                {
                                                  uint32_t a0 = (uint32_t)0U;
                                                  uint32_t b1 = (uint32_t)1U;
                                                  uint32_t c = (uint32_t)2U;
                                                  uint32_t d = (uint32_t)3U;
                                                  uint32_t
                                                  r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                  uint32_t
                                                  r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                  uint32_t
                                                  r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                  uint32_t
                                                  r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      wv_b8[0U]);
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      z[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                        wv_b9[0U]);
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                        r0);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b10 = block_state1.fst + d * (uint32_t)1U;
                                                      wv_a9[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                          wv_b10[0U]);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a10 =
                                                          block_state1.fst
                                                          + b1 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b11 =
                                                          block_state1.fst
                                                          + c * (uint32_t)1U;
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                            wv_b11[0U]);
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                            r1);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a11 =
                                                            block_state1.fst
                                                            + a0 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b12 =
                                                            block_state1.fst
                                                            + b1 * (uint32_t)1U;
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              wv_b12[0U]);
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              w[0U]);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a12 =
                                                              block_state1.fst
                                                              + d * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b13 =
                                                              block_state1.fst
                                                              + a0 * (uint32_t)1U;
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                wv_b13[0U]);
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                r23);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a13 =
                                                                block_state1.fst
                                                                + c * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b14 =
                                                                block_state1.fst
                                                                + d * (uint32_t)1U;
                                                              wv_a13[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                  wv_b14[0U]);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a14 =
                                                                  block_state1.fst
                                                                  + b1 * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b =
                                                                  block_state1.fst
                                                                  + c * (uint32_t)1U;
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                    wv_b[0U]);
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                    r33);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r13 =
                                                                    block_state1.fst
                                                                    + (uint32_t)1U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r2 =
                                                                    block_state1.fst
                                                                    + (uint32_t)2U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r3 =
                                                                    block_state1.fst
                                                                    + (uint32_t)3U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v0 = r13[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v12 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                      (uint32_t)3U);
                                                                  r13[0U] = v12;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v03 = r2[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v13 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                        (uint32_t)2U);
                                                                    r2[0U] = v13;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v04 = r3[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v14 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                          (uint32_t)1U);
                                                                      r3[0U] = v14;
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
                            }
                          }
                        }
                      }
                    }
                  }
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                  }
                }
              }
            }
          }
        }
        dst = buf;
        memcpy(dst, data21, data2_len * sizeof (data21[0U]));
        {
          Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
          lit0;
          lit0.block_state = block_state1;
          lit0.buf = buf;
          lit0.total_len = total_len1 + (uint64_t)(len - diff);
          *p = lit0;
        }
      }
    }
  }
}

/*
  Finish function when there is no key
*/
void
Hacl_Streaming_Blake2s_128_blake2s_128_no_key_finish(
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  scrut = *p;
  K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
  block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)64U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  {
    uint8_t *buf_1 = buf_;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (uint32_t)4U * (uint32_t)1U);
    {
      Lib_IntVector_Intrinsics_vec128 wv[(uint32_t)4U * (uint32_t)1U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          wv[_i] = Lib_IntVector_Intrinsics_vec128_zero;
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (uint32_t)4U * (uint32_t)1U);
      {
        Lib_IntVector_Intrinsics_vec128 b0[(uint32_t)4U * (uint32_t)1U];
        {
          uint32_t _i;
          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
            b0[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
        {
          K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ lit;
          K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ tmp_block_state;
          Lib_IntVector_Intrinsics_vec128 *src_b;
          Lib_IntVector_Intrinsics_vec128 *dst_b;
          uint64_t prev_len;
          lit.fst = wv;
          lit.snd = b0;
          tmp_block_state = lit;
          src_b = block_state.snd;
          dst_b = tmp_block_state.snd;
          memcpy(dst_b, src_b, (uint32_t)4U * sizeof (src_b[0U]));
          prev_len = total_len - (uint64_t)r;
          {
            uint8_t b2[64U] = { 0U };
            uint8_t *last = buf_1 + r - r;
            uint64_t ite;
            uint64_t totlen;
            memcpy(b2, last, r * sizeof (last[0U]));
            if ((uint32_t)0U == (uint32_t)0U)
            {
              ite = prev_len;
            }
            else
            {
              ite = prev_len + (uint64_t)(uint32_t)64U;
            }
            totlen = ite + (uint64_t)r;
            {
              uint32_t m_w[16U] = { 0U };
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  uint32_t *os = m_w;
                  uint8_t *bj = b2 + i * (uint32_t)4U;
                  uint32_t u = load32_le(bj);
                  uint32_t r1 = u;
                  uint32_t x = r1;
                  os[i] = x;
                }
              }
              {
                Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                uint32_t wv_14 = (uint32_t)0xFFFFFFFFU;
                uint32_t wv_15 = (uint32_t)0U;
                Lib_IntVector_Intrinsics_vec128 *wv3;
                Lib_IntVector_Intrinsics_vec128 *s00;
                Lib_IntVector_Intrinsics_vec128 *s16;
                Lib_IntVector_Intrinsics_vec128 *r00;
                Lib_IntVector_Intrinsics_vec128 *r10;
                Lib_IntVector_Intrinsics_vec128 *r20;
                Lib_IntVector_Intrinsics_vec128 *r30;
                uint32_t double_row;
                mask =
                  Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                    (uint32_t)(totlen >> (uint32_t)32U),
                    wv_14,
                    wv_15);
                memcpy(tmp_block_state.fst,
                  tmp_block_state.snd,
                  (uint32_t)4U * (uint32_t)1U * sizeof (tmp_block_state.snd[0U]));
                wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
                wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                  {
                    uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                      (uint32_t)4U * (uint32_t)1U);
                    {
                      Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                      {
                        uint32_t _i;
                        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                          m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                      }
                      {
                        Lib_IntVector_Intrinsics_vec128 *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
                        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                        uint32_t
                        s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                        uint32_t
                        s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                        uint32_t
                        s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                        uint32_t
                        s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                        uint32_t
                        s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                        uint32_t
                        s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                        uint32_t
                        s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                        uint32_t
                        s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                        uint32_t
                        s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                        uint32_t
                        s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                        uint32_t
                        s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                        uint32_t
                        s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                        uint32_t
                        s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                        uint32_t
                        s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                        uint32_t
                        s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                        r01[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                            m_w[s2],
                            m_w[s4],
                            m_w[s6]);
                        r11[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s1],
                            m_w[s3],
                            m_w[s5],
                            m_w[s7]);
                        r21[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                            m_w[s10],
                            m_w[s12],
                            m_w[s14]);
                        r31[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                            m_w[s11],
                            m_w[s13],
                            m_w[s15]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t a = (uint32_t)0U;
                          uint32_t b10 = (uint32_t)1U;
                          uint32_t c0 = (uint32_t)2U;
                          uint32_t d0 = (uint32_t)3U;
                          uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                          uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                          uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                          uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                          Lib_IntVector_Intrinsics_vec128
                          *wv_a0 = tmp_block_state.fst + a * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128
                          *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)1U;
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b1 = tmp_block_state.fst + a * (uint32_t)1U;
                            wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                            wv_a1[0U] =
                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                r02);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)1U;
                              wv_a2[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                  wv_b2[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)1U;
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                    wv_b3[0U]);
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                    r12);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a4 = tmp_block_state.fst + a * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)1U;
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      wv_b4[0U]);
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      y[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b5 = tmp_block_state.fst + a * (uint32_t)1U;
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                        wv_b5[0U]);
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                        r22);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)1U;
                                      wv_a6[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                          wv_b6[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)1U;
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                            wv_b7[0U]);
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                            r32);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *r13 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r23 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r33 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128 v00 = r13[0U];
                                          Lib_IntVector_Intrinsics_vec128
                                          v1 =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                              (uint32_t)1U);
                                          r13[0U] = v1;
                                          {
                                            Lib_IntVector_Intrinsics_vec128 v01 = r23[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v10 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                (uint32_t)2U);
                                            r23[0U] = v10;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v02 = r33[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v11 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                  (uint32_t)3U);
                                              r33[0U] = v11;
                                              {
                                                uint32_t a0 = (uint32_t)0U;
                                                uint32_t b1 = (uint32_t)1U;
                                                uint32_t c = (uint32_t)2U;
                                                uint32_t d = (uint32_t)3U;
                                                uint32_t
                                                r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                uint32_t
                                                r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                uint32_t
                                                r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                uint32_t
                                                r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a = tmp_block_state.fst + a0 * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)1U;
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    wv_b8[0U]);
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    z[0U]);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a8 = tmp_block_state.fst + d * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)1U;
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                      wv_b9[0U]);
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                      r0);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a9 = tmp_block_state.fst + c * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b10 = tmp_block_state.fst + d * (uint32_t)1U;
                                                    wv_a9[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                        wv_b10[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a10 =
                                                        tmp_block_state.fst
                                                        + b1 * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b11 =
                                                        tmp_block_state.fst
                                                        + c * (uint32_t)1U;
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                          wv_b11[0U]);
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                          r1);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a11 =
                                                          tmp_block_state.fst
                                                          + a0 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b12 =
                                                          tmp_block_state.fst
                                                          + b1 * (uint32_t)1U;
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            wv_b12[0U]);
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            w[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a12 =
                                                            tmp_block_state.fst
                                                            + d * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b13 =
                                                            tmp_block_state.fst
                                                            + a0 * (uint32_t)1U;
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                              wv_b13[0U]);
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                              r24);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a13 =
                                                              tmp_block_state.fst
                                                              + c * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b14 =
                                                              tmp_block_state.fst
                                                              + d * (uint32_t)1U;
                                                            wv_a13[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                wv_b14[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a14 =
                                                                tmp_block_state.fst
                                                                + b1 * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b =
                                                                tmp_block_state.fst
                                                                + c * (uint32_t)1U;
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                  wv_b[0U]);
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                  r34);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r14 =
                                                                  tmp_block_state.fst
                                                                  + (uint32_t)1U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r2 =
                                                                  tmp_block_state.fst
                                                                  + (uint32_t)2U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r3 =
                                                                  tmp_block_state.fst
                                                                  + (uint32_t)3U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v0 = r14[0U];
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v12 =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                    (uint32_t)3U);
                                                                r14[0U] = v12;
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v03 = r2[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v13 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                      (uint32_t)2U);
                                                                  r2[0U] = v13;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v04 = r3[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v14 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                        (uint32_t)1U);
                                                                    r3[0U] = v14;
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
                          }
                        }
                      }
                    }
                  }
                }
                s00 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
                s16 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
                r00 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)1U;
                r10 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
                r20 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
                r30 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
                s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r00[0U]);
                s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r20[0U]);
                s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r10[0U]);
                s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r30[0U]);
                Lib_Memzero0_memzero(b2, (uint32_t)64U * sizeof (b2[0U]));
                double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)4U;
                KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
                {
                  uint8_t b[double_row];
                  memset(b, 0U, double_row * sizeof (b[0U]));
                  {
                    uint8_t *first = b;
                    uint8_t *second = b + (uint32_t)4U * (uint32_t)4U;
                    Lib_IntVector_Intrinsics_vec128
                    *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
                    uint8_t *final;
                    Lib_IntVector_Intrinsics_vec128_store_le(first, row0[0U]);
                    Lib_IntVector_Intrinsics_vec128_store_le(second, row1[0U]);
                    final = b;
                    memcpy(dst, final, (uint32_t)32U * sizeof (final[0U]));
                    Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
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

/*
  Free state function when there is no key
*/
void
Hacl_Streaming_Blake2s_128_blake2s_128_no_key_free(
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  *s
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  scrut = *s;
  uint8_t *buf = scrut.buf;
  K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
  block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec128 *wv = block_state.fst;
  Lib_IntVector_Intrinsics_vec128 *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

/*
  State allocation function when using a (potentially null) key
*/
Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
*Hacl_Streaming_Blake2s_128_blake2s_128_with_key_create_in(uint32_t key_size, uint8_t *k)
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec128
  *wv = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec128) * (uint32_t)4U);
  {
    uint32_t _i;
    for (_i = 0U; _i < (uint32_t)4U; ++_i)
      wv[_i] = Lib_IntVector_Intrinsics_vec128_zero;
  }
  {
    Lib_IntVector_Intrinsics_vec128
    *b0 = KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec128) * (uint32_t)4U);
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)4U; ++_i)
        b0[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    }
    {
      K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ lit;
      K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ block_state;
      lit.fst = wv;
      lit.snd = b0;
      block_state = lit;
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        s;
        s.block_state = block_state;
        s.buf = buf;
        s.total_len = (uint64_t)0U;
        KRML_CHECK_SIZE(sizeof (
            Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
          ),
          (uint32_t)1U);
        {
          Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
          *p =
            KRML_HOST_MALLOC(sizeof (
                Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
              ));
          p[0U] = s;
          {
            uint8_t b[64U] = { 0U };
            Lib_IntVector_Intrinsics_vec128 *r00 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec128 *r10 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec128 *r20 = block_state.snd + (uint32_t)2U * (uint32_t)1U;
            Lib_IntVector_Intrinsics_vec128 *r30 = block_state.snd + (uint32_t)3U * (uint32_t)1U;
            uint32_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
            uint32_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
            uint32_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
            uint32_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
            uint32_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
            uint32_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
            uint32_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
            uint32_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
            uint32_t kk_shift_8;
            uint32_t iv0_;
            r20[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
            r30[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
            kk_shift_8 = key_size << (uint32_t)8U;
            iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
            r00[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1, iv2, iv3);
            r10[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
            if (!(key_size == (uint32_t)0U))
            {
              memcpy(b, k, key_size * sizeof (k[0U]));
              {
                uint64_t totlen = (uint64_t)(uint32_t)0U + (uint64_t)(uint32_t)64U;
                uint8_t *b1 = b + (uint32_t)0U * (uint32_t)64U;
                uint32_t m_w[16U] = { 0U };
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                  {
                    uint32_t *os = m_w;
                    uint8_t *bj = b1 + i * (uint32_t)4U;
                    uint32_t u = load32_le(bj);
                    uint32_t r1 = u;
                    uint32_t x = r1;
                    os[i] = x;
                  }
                }
                {
                  Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                  uint32_t wv_14 = (uint32_t)0U;
                  uint32_t wv_15 = (uint32_t)0U;
                  mask =
                    Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                      (uint32_t)(totlen >> (uint32_t)32U),
                      wv_14,
                      wv_15);
                  memcpy(block_state.fst,
                    block_state.snd,
                    (uint32_t)4U * (uint32_t)1U * sizeof (block_state.snd[0U]));
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *wv3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
                    wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                      {
                        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                          (uint32_t)4U * (uint32_t)1U);
                        {
                          Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                          {
                            uint32_t _i;
                            for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                              m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                          }
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                            uint32_t
                            s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                            uint32_t
                            s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                            uint32_t
                            s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                            uint32_t
                            s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                            uint32_t
                            s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                            uint32_t
                            s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                            uint32_t
                            s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                            uint32_t
                            s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                            uint32_t
                            s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                            uint32_t
                            s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                            uint32_t
                            s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                            uint32_t
                            s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                            uint32_t
                            s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                            uint32_t
                            s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                            uint32_t
                            s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                            r01[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                                m_w[s2],
                                m_w[s4],
                                m_w[s6]);
                            r11[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s1],
                                m_w[s3],
                                m_w[s5],
                                m_w[s7]);
                            r21[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                                m_w[s10],
                                m_w[s12],
                                m_w[s14]);
                            r31[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                                m_w[s11],
                                m_w[s13],
                                m_w[s15]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *x = m_st + (uint32_t)0U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *y = m_st + (uint32_t)1U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *z = m_st + (uint32_t)2U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *w = m_st + (uint32_t)3U * (uint32_t)1U;
                              uint32_t a = (uint32_t)0U;
                              uint32_t b20 = (uint32_t)1U;
                              uint32_t c0 = (uint32_t)2U;
                              uint32_t d0 = (uint32_t)3U;
                              uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                              uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                              uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                              uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a0 = block_state.fst + a * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b0 = block_state.fst + b20 * (uint32_t)1U;
                              wv_a0[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U],
                                  wv_b0[0U]);
                              wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a1 = block_state.fst + d0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b1 = block_state.fst + a * (uint32_t)1U;
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U],
                                    wv_b1[0U]);
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                    r02);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a2 = block_state.fst + c0 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b2 = block_state.fst + d0 * (uint32_t)1U;
                                  wv_a2[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                      wv_b2[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a3 = block_state.fst + b20 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b3 = block_state.fst + c0 * (uint32_t)1U;
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                        wv_b3[0U]);
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                        r12);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a4 = block_state.fst + a * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b4 = block_state.fst + b20 * (uint32_t)1U;
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          wv_b4[0U]);
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          y[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a5 = block_state.fst + d0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b5 = block_state.fst + a * (uint32_t)1U;
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                            wv_b5[0U]);
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                            r22);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a6 = block_state.fst + c0 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b6 = block_state.fst + d0 * (uint32_t)1U;
                                          wv_a6[0U] =
                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                              wv_b6[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_a7 = block_state.fst + b20 * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_b7 = block_state.fst + c0 * (uint32_t)1U;
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                                wv_b7[0U]);
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                                r32);
                                            {
                                              Lib_IntVector_Intrinsics_vec128
                                              *r13 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r23 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r33 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128 v00 = r13[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v1 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                  (uint32_t)1U);
                                              r13[0U] = v1;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v01 = r23[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v10 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                    (uint32_t)2U);
                                                r23[0U] = v10;
                                                {
                                                  Lib_IntVector_Intrinsics_vec128 v02 = r33[0U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  v11 =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                      (uint32_t)3U);
                                                  r33[0U] = v11;
                                                  {
                                                    uint32_t a0 = (uint32_t)0U;
                                                    uint32_t b2 = (uint32_t)1U;
                                                    uint32_t c = (uint32_t)2U;
                                                    uint32_t d = (uint32_t)3U;
                                                    uint32_t
                                                    r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                    uint32_t
                                                    r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                    uint32_t
                                                    r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                    uint32_t
                                                    r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a = block_state.fst + a0 * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b8 = block_state.fst + b2 * (uint32_t)1U;
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        wv_b8[0U]);
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        z[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a8 = block_state.fst + d * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b9 = block_state.fst + a0 * (uint32_t)1U;
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                          wv_b9[0U]);
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                          r0);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a9 = block_state.fst + c * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b10 = block_state.fst + d * (uint32_t)1U;
                                                        wv_a9[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                            wv_b10[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a10 =
                                                            block_state.fst
                                                            + b2 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b11 =
                                                            block_state.fst
                                                            + c * (uint32_t)1U;
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                              wv_b11[0U]);
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                              r1);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a11 =
                                                              block_state.fst
                                                              + a0 * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b12 =
                                                              block_state.fst
                                                              + b2 * (uint32_t)1U;
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                wv_b12[0U]);
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                w[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a12 =
                                                                block_state.fst
                                                                + d * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b13 =
                                                                block_state.fst
                                                                + a0 * (uint32_t)1U;
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                  wv_b13[0U]);
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                  r24);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a13 =
                                                                  block_state.fst
                                                                  + c * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b14 =
                                                                  block_state.fst
                                                                  + d * (uint32_t)1U;
                                                                wv_a13[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                    wv_b14[0U]);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_a14 =
                                                                    block_state.fst
                                                                    + b2 * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_b =
                                                                    block_state.fst
                                                                    + c * (uint32_t)1U;
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                      wv_b[0U]);
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                      r34);
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r14 =
                                                                      block_state.fst
                                                                      + (uint32_t)1U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r2 =
                                                                      block_state.fst
                                                                      + (uint32_t)2U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r3 =
                                                                      block_state.fst
                                                                      + (uint32_t)3U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v0 = r14[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v12 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                        (uint32_t)3U);
                                                                    r14[0U] = v12;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v03 = r2[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v13 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                          (uint32_t)2U);
                                                                      r2[0U] = v13;
                                                                      {
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v04 = r3[0U];
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v14 =
                                                                          Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                            (uint32_t)1U);
                                                                        r3[0U] = v14;
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
                              }
                            }
                          }
                        }
                      }
                    }
                    {
                      Lib_IntVector_Intrinsics_vec128
                      *s0 = block_state.snd + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *s1 = block_state.snd + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r0 = block_state.fst + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r1 = block_state.fst + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r2 = block_state.fst + (uint32_t)2U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r3 = block_state.fst + (uint32_t)3U * (uint32_t)1U;
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                      s1[0U] = Lib_IntVector_Intrinsics_vec128_xor(s1[0U], r1[0U]);
                      s1[0U] = Lib_IntVector_Intrinsics_vec128_xor(s1[0U], r3[0U]);
                    }
                  }
                }
              }
            }
            Lib_Memzero0_memzero(b, (uint32_t)64U * sizeof (b[0U]));
            return p;
          }
        }
      }
    }
  }
}

/*
  Update function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2s_128_blake2s_128_with_key_update(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)64U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  if (len <= (uint32_t)64U - sz)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    {
      uint8_t *buf2 = buf + sz1;
      uint64_t total_len2;
      memcpy(buf2, data, len * sizeof (data[0U]));
      total_len2 = total_len1 + (uint64_t)len;
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len2;
        *p = lit;
        return;
      }
    }
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
    s1 = *p;
    K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
    block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    {
      uint32_t ite0;
      uint32_t n_blocks;
      uint32_t data1_len;
      uint32_t data2_len;
      uint8_t *data1;
      uint8_t *data2;
      uint32_t nb0;
      uint8_t *dst;
      if (!(sz1 == (uint32_t)0U))
      {
        uint64_t prevlen = total_len1 - (uint64_t)sz1;
        uint32_t nb = (uint32_t)1U;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < nb; i0++)
          {
            uint64_t ite;
            if (key_size == (uint32_t)0U)
            {
              ite = prevlen;
            }
            else
            {
              ite = prevlen + (uint64_t)(uint32_t)64U;
            }
            {
              uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
              uint8_t *b = buf + i0 * (uint32_t)64U;
              uint32_t m_w[16U] = { 0U };
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  uint32_t *os = m_w;
                  uint8_t *bj = b + i * (uint32_t)4U;
                  uint32_t u = load32_le(bj);
                  uint32_t r = u;
                  uint32_t x = r;
                  os[i] = x;
                }
              }
              {
                Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                uint32_t wv_14 = (uint32_t)0U;
                uint32_t wv_15 = (uint32_t)0U;
                mask =
                  Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                    (uint32_t)(totlen >> (uint32_t)32U),
                    wv_14,
                    wv_15);
                memcpy(block_state1.fst,
                  block_state1.snd,
                  (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
                {
                  Lib_IntVector_Intrinsics_vec128
                  *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                  wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                  {
                    uint32_t i;
                    for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                    {
                      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                        (uint32_t)4U * (uint32_t)1U);
                      {
                        Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                        {
                          uint32_t _i;
                          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                            m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                        }
                        {
                          Lib_IntVector_Intrinsics_vec128 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                          uint32_t
                          s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                          uint32_t
                          s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                          uint32_t
                          s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                          uint32_t
                          s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                          uint32_t
                          s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                          uint32_t
                          s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                          uint32_t
                          s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                          uint32_t
                          s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                          uint32_t
                          s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                          uint32_t
                          s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                          uint32_t
                          s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                          uint32_t
                          s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                          uint32_t
                          s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                          uint32_t
                          s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                          uint32_t
                          s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                          r00[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                              m_w[s2],
                              m_w[s4],
                              m_w[s6]);
                          r10[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                              m_w[s3],
                              m_w[s5],
                              m_w[s7]);
                          r20[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                              m_w[s10],
                              m_w[s12],
                              m_w[s14]);
                          r30[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                              m_w[s111],
                              m_w[s13],
                              m_w[s15]);
                          {
                            Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t a = (uint32_t)0U;
                            uint32_t b10 = (uint32_t)1U;
                            uint32_t c0 = (uint32_t)2U;
                            uint32_t d0 = (uint32_t)3U;
                            uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                            uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                            uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                            uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                              wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                              wv_a1[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                  r01);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                                wv_a2[0U] =
                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                    wv_b2[0U]);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                      wv_b3[0U]);
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                      r11);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        wv_b4[0U]);
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        y[0U]);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                          wv_b5[0U]);
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                          r21);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                        wv_a6[0U] =
                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                            wv_b6[0U]);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                              wv_b7[0U]);
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                              r31);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v1 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                (uint32_t)1U);
                                            r12[0U] = v1;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v10 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                  (uint32_t)2U);
                                              r22[0U] = v10;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v11 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                    (uint32_t)3U);
                                                r32[0U] = v11;
                                                {
                                                  uint32_t a0 = (uint32_t)0U;
                                                  uint32_t b1 = (uint32_t)1U;
                                                  uint32_t c = (uint32_t)2U;
                                                  uint32_t d = (uint32_t)3U;
                                                  uint32_t
                                                  r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                  uint32_t
                                                  r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                  uint32_t
                                                  r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                  uint32_t
                                                  r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      wv_b8[0U]);
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      z[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                        wv_b9[0U]);
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                        r0);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b10 = block_state1.fst + d * (uint32_t)1U;
                                                      wv_a9[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                          wv_b10[0U]);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a10 =
                                                          block_state1.fst
                                                          + b1 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b11 =
                                                          block_state1.fst
                                                          + c * (uint32_t)1U;
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                            wv_b11[0U]);
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                            r1);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a11 =
                                                            block_state1.fst
                                                            + a0 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b12 =
                                                            block_state1.fst
                                                            + b1 * (uint32_t)1U;
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              wv_b12[0U]);
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              w[0U]);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a12 =
                                                              block_state1.fst
                                                              + d * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b13 =
                                                              block_state1.fst
                                                              + a0 * (uint32_t)1U;
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                wv_b13[0U]);
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                r23);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a13 =
                                                                block_state1.fst
                                                                + c * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b14 =
                                                                block_state1.fst
                                                                + d * (uint32_t)1U;
                                                              wv_a13[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                  wv_b14[0U]);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a14 =
                                                                  block_state1.fst
                                                                  + b1 * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b =
                                                                  block_state1.fst
                                                                  + c * (uint32_t)1U;
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                    wv_b[0U]);
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                    r33);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r13 =
                                                                    block_state1.fst
                                                                    + (uint32_t)1U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r2 =
                                                                    block_state1.fst
                                                                    + (uint32_t)2U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r3 =
                                                                    block_state1.fst
                                                                    + (uint32_t)3U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v0 = r13[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v12 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                      (uint32_t)3U);
                                                                  r13[0U] = v12;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v03 = r2[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v13 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                        (uint32_t)2U);
                                                                    r2[0U] = v13;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v04 = r3[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v14 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                          (uint32_t)1U);
                                                                      r3[0U] = v14;
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
                            }
                          }
                        }
                      }
                    }
                  }
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                  }
                }
              }
            }
          }
        }
      }
      if ((uint64_t)len % (uint64_t)(uint32_t)64U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
      {
        ite0 = (uint32_t)64U;
      }
      else
      {
        ite0 = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)64U);
      }
      n_blocks = (len - ite0) / (uint32_t)64U;
      data1_len = n_blocks * (uint32_t)64U;
      data2_len = len - data1_len;
      data1 = data;
      data2 = data + data1_len;
      nb0 = data1_len / (uint32_t)64U;
      {
        uint32_t i0;
        for (i0 = (uint32_t)0U; i0 < nb0; i0++)
        {
          uint64_t ite;
          if (key_size == (uint32_t)0U)
          {
            ite = total_len1;
          }
          else
          {
            ite = total_len1 + (uint64_t)(uint32_t)64U;
          }
          {
            uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
            uint8_t *b = data1 + i0 * (uint32_t)64U;
            uint32_t m_w[16U] = { 0U };
            {
              uint32_t i;
              for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
              {
                uint32_t *os = m_w;
                uint8_t *bj = b + i * (uint32_t)4U;
                uint32_t u = load32_le(bj);
                uint32_t r = u;
                uint32_t x = r;
                os[i] = x;
              }
            }
            {
              Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
              uint32_t wv_14 = (uint32_t)0U;
              uint32_t wv_15 = (uint32_t)0U;
              mask =
                Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                  (uint32_t)(totlen >> (uint32_t)32U),
                  wv_14,
                  wv_15);
              memcpy(block_state1.fst,
                block_state1.snd,
                (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
              {
                Lib_IntVector_Intrinsics_vec128
                *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                  {
                    uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                      (uint32_t)4U * (uint32_t)1U);
                    {
                      Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                      {
                        uint32_t _i;
                        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                          m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                      }
                      {
                        Lib_IntVector_Intrinsics_vec128 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                        uint32_t
                        s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                        uint32_t
                        s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                        uint32_t
                        s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                        uint32_t
                        s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                        uint32_t
                        s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                        uint32_t
                        s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                        uint32_t
                        s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                        uint32_t
                        s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                        uint32_t
                        s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                        uint32_t
                        s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                        uint32_t
                        s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                        uint32_t
                        s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                        uint32_t
                        s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                        uint32_t
                        s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                        uint32_t
                        s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                        r00[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                            m_w[s2],
                            m_w[s4],
                            m_w[s6]);
                        r10[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                            m_w[s3],
                            m_w[s5],
                            m_w[s7]);
                        r20[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                            m_w[s10],
                            m_w[s12],
                            m_w[s14]);
                        r30[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                            m_w[s111],
                            m_w[s13],
                            m_w[s15]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t a = (uint32_t)0U;
                          uint32_t b10 = (uint32_t)1U;
                          uint32_t c0 = (uint32_t)2U;
                          uint32_t d0 = (uint32_t)3U;
                          uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                          uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                          uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                          uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                          Lib_IntVector_Intrinsics_vec128
                          *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128
                          *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                            wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                            wv_a1[0U] =
                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                r01);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                              wv_a2[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                  wv_b2[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                    wv_b3[0U]);
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                    r11);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      wv_b4[0U]);
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      y[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                        wv_b5[0U]);
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                        r21);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                      wv_a6[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                          wv_b6[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                            wv_b7[0U]);
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                            r31);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                          Lib_IntVector_Intrinsics_vec128
                                          v1 =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                              (uint32_t)1U);
                                          r12[0U] = v1;
                                          {
                                            Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v10 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                (uint32_t)2U);
                                            r22[0U] = v10;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v11 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                  (uint32_t)3U);
                                              r32[0U] = v11;
                                              {
                                                uint32_t a0 = (uint32_t)0U;
                                                uint32_t b1 = (uint32_t)1U;
                                                uint32_t c = (uint32_t)2U;
                                                uint32_t d = (uint32_t)3U;
                                                uint32_t
                                                r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                uint32_t
                                                r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                uint32_t
                                                r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                uint32_t
                                                r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    wv_b8[0U]);
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    z[0U]);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                      wv_b9[0U]);
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                      r0);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b10 = block_state1.fst + d * (uint32_t)1U;
                                                    wv_a9[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                        wv_b10[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a10 = block_state1.fst + b1 * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b11 = block_state1.fst + c * (uint32_t)1U;
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                          wv_b11[0U]);
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                          r1);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a11 =
                                                          block_state1.fst
                                                          + a0 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b12 =
                                                          block_state1.fst
                                                          + b1 * (uint32_t)1U;
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            wv_b12[0U]);
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            w[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a12 =
                                                            block_state1.fst
                                                            + d * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b13 =
                                                            block_state1.fst
                                                            + a0 * (uint32_t)1U;
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                              wv_b13[0U]);
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                              r23);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a13 =
                                                              block_state1.fst
                                                              + c * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b14 =
                                                              block_state1.fst
                                                              + d * (uint32_t)1U;
                                                            wv_a13[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                wv_b14[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a14 =
                                                                block_state1.fst
                                                                + b1 * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b =
                                                                block_state1.fst
                                                                + c * (uint32_t)1U;
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                  wv_b[0U]);
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                  r33);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r13 =
                                                                  block_state1.fst
                                                                  + (uint32_t)1U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r2 =
                                                                  block_state1.fst
                                                                  + (uint32_t)2U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r3 =
                                                                  block_state1.fst
                                                                  + (uint32_t)3U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v0 = r13[0U];
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v12 =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                    (uint32_t)3U);
                                                                r13[0U] = v12;
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v03 = r2[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v13 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                      (uint32_t)2U);
                                                                  r2[0U] = v13;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v04 = r3[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v14 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                        (uint32_t)1U);
                                                                    r3[0U] = v14;
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
                          }
                        }
                      }
                    }
                  }
                }
                {
                  Lib_IntVector_Intrinsics_vec128
                  *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128
                  *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                  s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                  s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                  s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                  s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                }
              }
            }
          }
        }
      }
      dst = buf;
      memcpy(dst, data2, data2_len * sizeof (data2[0U]));
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len1 + (uint64_t)len;
        *p = lit;
        return;
      }
    }
  }
  {
    uint32_t diff = (uint32_t)64U - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
    s16 = *p;
    K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
    block_state10 = s16.block_state;
    uint8_t *buf0 = s16.buf;
    uint64_t total_len10 = s16.total_len;
    uint32_t sz10;
    if (total_len10 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len10 > (uint64_t)0U)
    {
      sz10 = (uint32_t)64U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)64U);
    }
    {
      uint8_t *buf2 = buf0 + sz10;
      uint64_t total_len2;
      memcpy(buf2, data1, diff * sizeof (data1[0U]));
      total_len2 = total_len10 + (uint64_t)diff;
      {
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        lit;
        Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
        s1;
        K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ block_state1;
        uint8_t *buf;
        uint64_t total_len1;
        uint32_t sz1;
        uint32_t ite0;
        uint32_t n_blocks;
        uint32_t data1_len;
        uint32_t data2_len;
        uint8_t *data11;
        uint8_t *data21;
        uint32_t nb0;
        uint8_t *dst;
        lit.block_state = block_state10;
        lit.buf = buf0;
        lit.total_len = total_len2;
        *p = lit;
        s1 = *p;
        block_state1 = s1.block_state;
        buf = s1.buf;
        total_len1 = s1.total_len;
        if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
        {
          sz1 = (uint32_t)64U;
        }
        else
        {
          sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
        }
        if (!(sz1 == (uint32_t)0U))
        {
          uint64_t prevlen = total_len1 - (uint64_t)sz1;
          uint32_t nb = (uint32_t)1U;
          {
            uint32_t i0;
            for (i0 = (uint32_t)0U; i0 < nb; i0++)
            {
              uint64_t ite;
              if (key_size == (uint32_t)0U)
              {
                ite = prevlen;
              }
              else
              {
                ite = prevlen + (uint64_t)(uint32_t)64U;
              }
              {
                uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
                uint8_t *b = buf + i0 * (uint32_t)64U;
                uint32_t m_w[16U] = { 0U };
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                  {
                    uint32_t *os = m_w;
                    uint8_t *bj = b + i * (uint32_t)4U;
                    uint32_t u = load32_le(bj);
                    uint32_t r = u;
                    uint32_t x = r;
                    os[i] = x;
                  }
                }
                {
                  Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                  uint32_t wv_14 = (uint32_t)0U;
                  uint32_t wv_15 = (uint32_t)0U;
                  mask =
                    Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                      (uint32_t)(totlen >> (uint32_t)32U),
                      wv_14,
                      wv_15);
                  memcpy(block_state1.fst,
                    block_state1.snd,
                    (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                    wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                      {
                        uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                          (uint32_t)4U * (uint32_t)1U);
                        {
                          Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                          {
                            uint32_t _i;
                            for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                              m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                          }
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                            uint32_t
                            s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                            uint32_t
                            s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                            uint32_t
                            s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                            uint32_t
                            s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                            uint32_t
                            s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                            uint32_t
                            s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                            uint32_t
                            s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                            uint32_t
                            s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                            uint32_t
                            s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                            uint32_t
                            s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                            uint32_t
                            s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                            uint32_t
                            s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                            uint32_t
                            s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                            uint32_t
                            s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                            uint32_t
                            s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                            r00[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                                m_w[s2],
                                m_w[s4],
                                m_w[s6]);
                            r10[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                                m_w[s3],
                                m_w[s5],
                                m_w[s7]);
                            r20[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                                m_w[s10],
                                m_w[s12],
                                m_w[s14]);
                            r30[0U] =
                              Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                                m_w[s111],
                                m_w[s13],
                                m_w[s15]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *x = m_st + (uint32_t)0U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *y = m_st + (uint32_t)1U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *z = m_st + (uint32_t)2U * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *w = m_st + (uint32_t)3U * (uint32_t)1U;
                              uint32_t a = (uint32_t)0U;
                              uint32_t b10 = (uint32_t)1U;
                              uint32_t c0 = (uint32_t)2U;
                              uint32_t d0 = (uint32_t)3U;
                              uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                              uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                              uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                              uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                              wv_a0[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U],
                                  wv_b0[0U]);
                              wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U],
                                    wv_b1[0U]);
                                wv_a1[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                    r01);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                                  wv_a2[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                      wv_b2[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                        wv_b3[0U]);
                                    wv_a3[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                        r11);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          wv_b4[0U]);
                                      wv_a4[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                          y[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                            wv_b5[0U]);
                                        wv_a5[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                            r21);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                          wv_a6[0U] =
                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                              wv_b6[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                                wv_b7[0U]);
                                            wv_a7[0U] =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                                r31);
                                            {
                                              Lib_IntVector_Intrinsics_vec128
                                              *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v1 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                  (uint32_t)1U);
                                              r12[0U] = v1;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v10 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                    (uint32_t)2U);
                                                r22[0U] = v10;
                                                {
                                                  Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  v11 =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                      (uint32_t)3U);
                                                  r32[0U] = v11;
                                                  {
                                                    uint32_t a0 = (uint32_t)0U;
                                                    uint32_t b1 = (uint32_t)1U;
                                                    uint32_t c = (uint32_t)2U;
                                                    uint32_t d = (uint32_t)3U;
                                                    uint32_t
                                                    r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                    uint32_t
                                                    r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                    uint32_t
                                                    r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                    uint32_t
                                                    r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        wv_b8[0U]);
                                                    wv_a[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                        z[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                          wv_b9[0U]);
                                                      wv_a8[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                          r0);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b10 =
                                                          block_state1.fst
                                                          + d * (uint32_t)1U;
                                                        wv_a9[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                            wv_b10[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a10 =
                                                            block_state1.fst
                                                            + b1 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b11 =
                                                            block_state1.fst
                                                            + c * (uint32_t)1U;
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                              wv_b11[0U]);
                                                          wv_a10[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                              r1);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a11 =
                                                              block_state1.fst
                                                              + a0 * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b12 =
                                                              block_state1.fst
                                                              + b1 * (uint32_t)1U;
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                wv_b12[0U]);
                                                            wv_a11[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                                w[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a12 =
                                                                block_state1.fst
                                                                + d * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b13 =
                                                                block_state1.fst
                                                                + a0 * (uint32_t)1U;
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                  wv_b13[0U]);
                                                              wv_a12[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                  r23);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a13 =
                                                                  block_state1.fst
                                                                  + c * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b14 =
                                                                  block_state1.fst
                                                                  + d * (uint32_t)1U;
                                                                wv_a13[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                    wv_b14[0U]);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_a14 =
                                                                    block_state1.fst
                                                                    + b1 * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *wv_b =
                                                                    block_state1.fst
                                                                    + c * (uint32_t)1U;
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                      wv_b[0U]);
                                                                  wv_a14[0U] =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                      r33);
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r13 =
                                                                      block_state1.fst
                                                                      + (uint32_t)1U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r2 =
                                                                      block_state1.fst
                                                                      + (uint32_t)2U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    *r3 =
                                                                      block_state1.fst
                                                                      + (uint32_t)3U * (uint32_t)1U;
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v0 = r13[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v12 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                        (uint32_t)3U);
                                                                    r13[0U] = v12;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v03 = r2[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v13 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                          (uint32_t)2U);
                                                                      r2[0U] = v13;
                                                                      {
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v04 = r3[0U];
                                                                        Lib_IntVector_Intrinsics_vec128
                                                                        v14 =
                                                                          Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                            (uint32_t)1U);
                                                                        r3[0U] = v14;
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
                              }
                            }
                          }
                        }
                      }
                    }
                    {
                      Lib_IntVector_Intrinsics_vec128
                      *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128
                      *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                      s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                      s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                      s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                    }
                  }
                }
              }
            }
          }
        }
        if
        (
          (uint64_t)(len - diff)
          % (uint64_t)(uint32_t)64U
          == (uint64_t)0U
          && (uint64_t)(len - diff) > (uint64_t)0U
        )
        {
          ite0 = (uint32_t)64U;
        }
        else
        {
          ite0 = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)64U);
        }
        n_blocks = (len - diff - ite0) / (uint32_t)64U;
        data1_len = n_blocks * (uint32_t)64U;
        data2_len = len - diff - data1_len;
        data11 = data2;
        data21 = data2 + data1_len;
        nb0 = data1_len / (uint32_t)64U;
        {
          uint32_t i0;
          for (i0 = (uint32_t)0U; i0 < nb0; i0++)
          {
            uint64_t ite;
            if (key_size == (uint32_t)0U)
            {
              ite = total_len1;
            }
            else
            {
              ite = total_len1 + (uint64_t)(uint32_t)64U;
            }
            {
              uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
              uint8_t *b = data11 + i0 * (uint32_t)64U;
              uint32_t m_w[16U] = { 0U };
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  uint32_t *os = m_w;
                  uint8_t *bj = b + i * (uint32_t)4U;
                  uint32_t u = load32_le(bj);
                  uint32_t r = u;
                  uint32_t x = r;
                  os[i] = x;
                }
              }
              {
                Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                uint32_t wv_14 = (uint32_t)0U;
                uint32_t wv_15 = (uint32_t)0U;
                mask =
                  Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                    (uint32_t)(totlen >> (uint32_t)32U),
                    wv_14,
                    wv_15);
                memcpy(block_state1.fst,
                  block_state1.snd,
                  (uint32_t)4U * (uint32_t)1U * sizeof (block_state1.snd[0U]));
                {
                  Lib_IntVector_Intrinsics_vec128
                  *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                  wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                  {
                    uint32_t i;
                    for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                    {
                      uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                        (uint32_t)4U * (uint32_t)1U);
                      {
                        Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                        {
                          uint32_t _i;
                          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                            m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                        }
                        {
                          Lib_IntVector_Intrinsics_vec128 *r00 = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r10 = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r20 = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *r30 = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                          uint32_t
                          s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                          uint32_t
                          s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                          uint32_t
                          s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                          uint32_t
                          s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                          uint32_t
                          s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                          uint32_t
                          s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                          uint32_t
                          s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                          uint32_t
                          s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                          uint32_t
                          s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                          uint32_t
                          s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                          uint32_t
                          s111 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                          uint32_t
                          s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                          uint32_t
                          s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                          uint32_t
                          s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                          uint32_t
                          s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                          r00[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                              m_w[s2],
                              m_w[s4],
                              m_w[s6]);
                          r10[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s11],
                              m_w[s3],
                              m_w[s5],
                              m_w[s7]);
                          r20[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                              m_w[s10],
                              m_w[s12],
                              m_w[s14]);
                          r30[0U] =
                            Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                              m_w[s111],
                              m_w[s13],
                              m_w[s15]);
                          {
                            Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                            uint32_t a = (uint32_t)0U;
                            uint32_t b10 = (uint32_t)1U;
                            uint32_t c0 = (uint32_t)2U;
                            uint32_t d0 = (uint32_t)3U;
                            uint32_t r01 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                            uint32_t r11 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                            uint32_t r21 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                            uint32_t r31 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a0 = block_state1.fst + a * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b0 = block_state1.fst + b10 * (uint32_t)1U;
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                            wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a1 = block_state1.fst + d0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b1 = block_state1.fst + a * (uint32_t)1U;
                              wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                              wv_a1[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                  r01);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a2 = block_state1.fst + c0 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b2 = block_state1.fst + d0 * (uint32_t)1U;
                                wv_a2[0U] =
                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                    wv_b2[0U]);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a3 = block_state1.fst + b10 * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b3 = block_state1.fst + c0 * (uint32_t)1U;
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                      wv_b3[0U]);
                                  wv_a3[0U] =
                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                      r11);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a4 = block_state1.fst + a * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b4 = block_state1.fst + b10 * (uint32_t)1U;
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        wv_b4[0U]);
                                    wv_a4[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                        y[0U]);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a5 = block_state1.fst + d0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b5 = block_state1.fst + a * (uint32_t)1U;
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                          wv_b5[0U]);
                                      wv_a5[0U] =
                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                          r21);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a6 = block_state1.fst + c0 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b6 = block_state1.fst + d0 * (uint32_t)1U;
                                        wv_a6[0U] =
                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                            wv_b6[0U]);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a7 = block_state1.fst + b10 * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b7 = block_state1.fst + c0 * (uint32_t)1U;
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                              wv_b7[0U]);
                                          wv_a7[0U] =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                              r31);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *r12 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r22 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *r32 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128 v00 = r12[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v1 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                                (uint32_t)1U);
                                            r12[0U] = v1;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v01 = r22[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v10 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                  (uint32_t)2U);
                                              r22[0U] = v10;
                                              {
                                                Lib_IntVector_Intrinsics_vec128 v02 = r32[0U];
                                                Lib_IntVector_Intrinsics_vec128
                                                v11 =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                    (uint32_t)3U);
                                                r32[0U] = v11;
                                                {
                                                  uint32_t a0 = (uint32_t)0U;
                                                  uint32_t b1 = (uint32_t)1U;
                                                  uint32_t c = (uint32_t)2U;
                                                  uint32_t d = (uint32_t)3U;
                                                  uint32_t
                                                  r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                  uint32_t
                                                  r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                  uint32_t
                                                  r23 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                  uint32_t
                                                  r33 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a = block_state1.fst + a0 * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b8 = block_state1.fst + b1 * (uint32_t)1U;
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      wv_b8[0U]);
                                                  wv_a[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                      z[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a8 = block_state1.fst + d * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b9 = block_state1.fst + a0 * (uint32_t)1U;
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                        wv_b9[0U]);
                                                    wv_a8[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                        r0);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a9 = block_state1.fst + c * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b10 = block_state1.fst + d * (uint32_t)1U;
                                                      wv_a9[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                          wv_b10[0U]);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a10 =
                                                          block_state1.fst
                                                          + b1 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b11 =
                                                          block_state1.fst
                                                          + c * (uint32_t)1U;
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                            wv_b11[0U]);
                                                        wv_a10[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                            r1);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a11 =
                                                            block_state1.fst
                                                            + a0 * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b12 =
                                                            block_state1.fst
                                                            + b1 * (uint32_t)1U;
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              wv_b12[0U]);
                                                          wv_a11[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                              w[0U]);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a12 =
                                                              block_state1.fst
                                                              + d * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b13 =
                                                              block_state1.fst
                                                              + a0 * (uint32_t)1U;
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                                wv_b13[0U]);
                                                            wv_a12[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                                r23);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a13 =
                                                                block_state1.fst
                                                                + c * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b14 =
                                                                block_state1.fst
                                                                + d * (uint32_t)1U;
                                                              wv_a13[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                  wv_b14[0U]);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_a14 =
                                                                  block_state1.fst
                                                                  + b1 * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *wv_b =
                                                                  block_state1.fst
                                                                  + c * (uint32_t)1U;
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                    wv_b[0U]);
                                                                wv_a14[0U] =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                    r33);
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r13 =
                                                                    block_state1.fst
                                                                    + (uint32_t)1U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r2 =
                                                                    block_state1.fst
                                                                    + (uint32_t)2U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  *r3 =
                                                                    block_state1.fst
                                                                    + (uint32_t)3U * (uint32_t)1U;
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v0 = r13[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v12 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                      (uint32_t)3U);
                                                                  r13[0U] = v12;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v03 = r2[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v13 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                        (uint32_t)2U);
                                                                    r2[0U] = v13;
                                                                    {
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v04 = r3[0U];
                                                                      Lib_IntVector_Intrinsics_vec128
                                                                      v14 =
                                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                          (uint32_t)1U);
                                                                      r3[0U] = v14;
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
                            }
                          }
                        }
                      }
                    }
                  }
                  {
                    Lib_IntVector_Intrinsics_vec128
                    *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)1U;
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r0[0U]);
                    s0[0U] = Lib_IntVector_Intrinsics_vec128_xor(s0[0U], r2[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r1[0U]);
                    s11[0U] = Lib_IntVector_Intrinsics_vec128_xor(s11[0U], r3[0U]);
                  }
                }
              }
            }
          }
        }
        dst = buf;
        memcpy(dst, data21, data2_len * sizeof (data21[0U]));
        {
          Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
          lit0;
          lit0.block_state = block_state1;
          lit0.buf = buf;
          lit0.total_len = total_len1 + (uint64_t)(len - diff);
          *p = lit0;
        }
      }
    }
  }
}

/*
  Finish function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2s_128_blake2s_128_with_key_finish(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  scrut = *p;
  K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
  block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)64U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  {
    uint8_t *buf_1 = buf_;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (uint32_t)4U * (uint32_t)1U);
    {
      Lib_IntVector_Intrinsics_vec128 wv[(uint32_t)4U * (uint32_t)1U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          wv[_i] = Lib_IntVector_Intrinsics_vec128_zero;
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (uint32_t)4U * (uint32_t)1U);
      {
        Lib_IntVector_Intrinsics_vec128 b0[(uint32_t)4U * (uint32_t)1U];
        {
          uint32_t _i;
          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
            b0[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
        {
          K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ lit;
          K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_ tmp_block_state;
          Lib_IntVector_Intrinsics_vec128 *src_b;
          Lib_IntVector_Intrinsics_vec128 *dst_b;
          uint64_t prev_len;
          lit.fst = wv;
          lit.snd = b0;
          tmp_block_state = lit;
          src_b = block_state.snd;
          dst_b = tmp_block_state.snd;
          memcpy(dst_b, src_b, (uint32_t)4U * sizeof (src_b[0U]));
          prev_len = total_len - (uint64_t)r;
          {
            uint8_t b2[64U] = { 0U };
            uint8_t *last = buf_1 + r - r;
            uint64_t ite;
            uint64_t totlen;
            memcpy(b2, last, r * sizeof (last[0U]));
            if (key_size == (uint32_t)0U)
            {
              ite = prev_len;
            }
            else
            {
              ite = prev_len + (uint64_t)(uint32_t)64U;
            }
            totlen = ite + (uint64_t)r;
            {
              uint32_t m_w[16U] = { 0U };
              {
                uint32_t i;
                for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
                {
                  uint32_t *os = m_w;
                  uint8_t *bj = b2 + i * (uint32_t)4U;
                  uint32_t u = load32_le(bj);
                  uint32_t r1 = u;
                  uint32_t x = r1;
                  os[i] = x;
                }
              }
              {
                Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
                uint32_t wv_14 = (uint32_t)0xFFFFFFFFU;
                uint32_t wv_15 = (uint32_t)0U;
                Lib_IntVector_Intrinsics_vec128 *wv3;
                Lib_IntVector_Intrinsics_vec128 *s00;
                Lib_IntVector_Intrinsics_vec128 *s16;
                Lib_IntVector_Intrinsics_vec128 *r00;
                Lib_IntVector_Intrinsics_vec128 *r10;
                Lib_IntVector_Intrinsics_vec128 *r20;
                Lib_IntVector_Intrinsics_vec128 *r30;
                uint32_t double_row;
                mask =
                  Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
                    (uint32_t)(totlen >> (uint32_t)32U),
                    wv_14,
                    wv_15);
                memcpy(tmp_block_state.fst,
                  tmp_block_state.snd,
                  (uint32_t)4U * (uint32_t)1U * sizeof (tmp_block_state.snd[0U]));
                wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
                wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
                  {
                    uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
                    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128),
                      (uint32_t)4U * (uint32_t)1U);
                    {
                      Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
                      {
                        uint32_t _i;
                        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                          m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
                      }
                      {
                        Lib_IntVector_Intrinsics_vec128 *r01 = m_st + (uint32_t)0U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r11 = m_st + (uint32_t)1U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
                        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
                        uint32_t
                        s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
                        uint32_t
                        s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
                        uint32_t
                        s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)3U];
                        uint32_t
                        s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)4U];
                        uint32_t
                        s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)5U];
                        uint32_t
                        s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)6U];
                        uint32_t
                        s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)7U];
                        uint32_t
                        s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)8U];
                        uint32_t
                        s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)9U];
                        uint32_t
                        s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)10U];
                        uint32_t
                        s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)11U];
                        uint32_t
                        s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)12U];
                        uint32_t
                        s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)13U];
                        uint32_t
                        s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)14U];
                        uint32_t
                        s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)15U];
                        r01[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0],
                            m_w[s2],
                            m_w[s4],
                            m_w[s6]);
                        r11[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s1],
                            m_w[s3],
                            m_w[s5],
                            m_w[s7]);
                        r21[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s8],
                            m_w[s10],
                            m_w[s12],
                            m_w[s14]);
                        r31[0U] =
                          Lib_IntVector_Intrinsics_vec128_load32s(m_w[s9],
                            m_w[s11],
                            m_w[s13],
                            m_w[s15]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *x = m_st + (uint32_t)0U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *y = m_st + (uint32_t)1U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *z = m_st + (uint32_t)2U * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *w = m_st + (uint32_t)3U * (uint32_t)1U;
                          uint32_t a = (uint32_t)0U;
                          uint32_t b10 = (uint32_t)1U;
                          uint32_t c0 = (uint32_t)2U;
                          uint32_t d0 = (uint32_t)3U;
                          uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                          uint32_t r12 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                          uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                          uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                          Lib_IntVector_Intrinsics_vec128
                          *wv_a0 = tmp_block_state.fst + a * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128
                          *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)1U;
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                          wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                          {
                            Lib_IntVector_Intrinsics_vec128
                            *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128
                            *wv_b1 = tmp_block_state.fst + a * (uint32_t)1U;
                            wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                            wv_a1[0U] =
                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                                r02);
                            {
                              Lib_IntVector_Intrinsics_vec128
                              *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128
                              *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)1U;
                              wv_a2[0U] =
                                Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U],
                                  wv_b2[0U]);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)1U;
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U],
                                    wv_b3[0U]);
                                wv_a3[0U] =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                    r12);
                                {
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_a4 = tmp_block_state.fst + a * (uint32_t)1U;
                                  Lib_IntVector_Intrinsics_vec128
                                  *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)1U;
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      wv_b4[0U]);
                                  wv_a4[0U] =
                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                      y[0U]);
                                  {
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)1U;
                                    Lib_IntVector_Intrinsics_vec128
                                    *wv_b5 = tmp_block_state.fst + a * (uint32_t)1U;
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                        wv_b5[0U]);
                                    wv_a5[0U] =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                        r22);
                                    {
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)1U;
                                      wv_a6[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                          wv_b6[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)1U;
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                            wv_b7[0U]);
                                        wv_a7[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                            r32);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *r13 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r23 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *r33 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128 v00 = r13[0U];
                                          Lib_IntVector_Intrinsics_vec128
                                          v1 =
                                            Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                              (uint32_t)1U);
                                          r13[0U] = v1;
                                          {
                                            Lib_IntVector_Intrinsics_vec128 v01 = r23[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v10 =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                                (uint32_t)2U);
                                            r23[0U] = v10;
                                            {
                                              Lib_IntVector_Intrinsics_vec128 v02 = r33[0U];
                                              Lib_IntVector_Intrinsics_vec128
                                              v11 =
                                                Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                                  (uint32_t)3U);
                                              r33[0U] = v11;
                                              {
                                                uint32_t a0 = (uint32_t)0U;
                                                uint32_t b1 = (uint32_t)1U;
                                                uint32_t c = (uint32_t)2U;
                                                uint32_t d = (uint32_t)3U;
                                                uint32_t
                                                r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                uint32_t
                                                r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                uint32_t
                                                r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                uint32_t
                                                r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a = tmp_block_state.fst + a0 * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)1U;
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    wv_b8[0U]);
                                                wv_a[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                    z[0U]);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a8 = tmp_block_state.fst + d * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)1U;
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                      wv_b9[0U]);
                                                  wv_a8[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                      r0);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a9 = tmp_block_state.fst + c * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b10 = tmp_block_state.fst + d * (uint32_t)1U;
                                                    wv_a9[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                        wv_b10[0U]);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a10 =
                                                        tmp_block_state.fst
                                                        + b1 * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b11 =
                                                        tmp_block_state.fst
                                                        + c * (uint32_t)1U;
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                          wv_b11[0U]);
                                                      wv_a10[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                          r1);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a11 =
                                                          tmp_block_state.fst
                                                          + a0 * (uint32_t)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b12 =
                                                          tmp_block_state.fst
                                                          + b1 * (uint32_t)1U;
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            wv_b12[0U]);
                                                        wv_a11[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                            w[0U]);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a12 =
                                                            tmp_block_state.fst
                                                            + d * (uint32_t)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b13 =
                                                            tmp_block_state.fst
                                                            + a0 * (uint32_t)1U;
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                              wv_b13[0U]);
                                                          wv_a12[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                              r24);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a13 =
                                                              tmp_block_state.fst
                                                              + c * (uint32_t)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b14 =
                                                              tmp_block_state.fst
                                                              + d * (uint32_t)1U;
                                                            wv_a13[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                                wv_b14[0U]);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_a14 =
                                                                tmp_block_state.fst
                                                                + b1 * (uint32_t)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *wv_b =
                                                                tmp_block_state.fst
                                                                + c * (uint32_t)1U;
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                  wv_b[0U]);
                                                              wv_a14[0U] =
                                                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                  r34);
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r14 =
                                                                  tmp_block_state.fst
                                                                  + (uint32_t)1U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r2 =
                                                                  tmp_block_state.fst
                                                                  + (uint32_t)2U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                *r3 =
                                                                  tmp_block_state.fst
                                                                  + (uint32_t)3U * (uint32_t)1U;
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v0 = r14[0U];
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v12 =
                                                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                                    (uint32_t)3U);
                                                                r14[0U] = v12;
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v03 = r2[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v13 =
                                                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                                      (uint32_t)2U);
                                                                  r2[0U] = v13;
                                                                  {
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v04 = r3[0U];
                                                                    Lib_IntVector_Intrinsics_vec128
                                                                    v14 =
                                                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                                        (uint32_t)1U);
                                                                    r3[0U] = v14;
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
                          }
                        }
                      }
                    }
                  }
                }
                s00 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
                s16 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
                r00 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)1U;
                r10 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)1U;
                r20 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)1U;
                r30 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)1U;
                s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r00[0U]);
                s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r20[0U]);
                s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r10[0U]);
                s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r30[0U]);
                Lib_Memzero0_memzero(b2, (uint32_t)64U * sizeof (b2[0U]));
                double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)4U;
                KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
                {
                  uint8_t b[double_row];
                  memset(b, 0U, double_row * sizeof (b[0U]));
                  {
                    uint8_t *first = b;
                    uint8_t *second = b + (uint32_t)4U * (uint32_t)4U;
                    Lib_IntVector_Intrinsics_vec128
                    *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128
                    *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)1U;
                    uint8_t *final;
                    Lib_IntVector_Intrinsics_vec128_store_le(first, row0[0U]);
                    Lib_IntVector_Intrinsics_vec128_store_le(second, row1[0U]);
                    final = b;
                    memcpy(dst, final, (uint32_t)32U * sizeof (final[0U]));
                    Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
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

/*
  Free state function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2s_128_blake2s_128_with_key_free(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  *s
)
{
  Hacl_Streaming_Functor_state_s__K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128____
  scrut = *s;
  uint8_t *buf = scrut.buf;
  K____Lib_IntVector_Intrinsics_vec128___Lib_IntVector_Intrinsics_vec128_
  block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec128 *wv = block_state.fst;
  Lib_IntVector_Intrinsics_vec128 *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

