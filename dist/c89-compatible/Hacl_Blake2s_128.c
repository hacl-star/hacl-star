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


#include "Hacl_Blake2s_128.h"

static inline void
blake2s_update_block(
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  bool flag,
  uint64_t totlen,
  uint8_t *d
)
{
  uint32_t m_w[16U] = { 0U };
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t *os = m_w;
      uint8_t *bj = d + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
  }
  {
    Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
    uint32_t wv_14;
    if (flag)
    {
      wv_14 = (uint32_t)0xFFFFFFFFU;
    }
    else
    {
      wv_14 = (uint32_t)0U;
    }
    {
      uint32_t wv_15 = (uint32_t)0U;
      Lib_IntVector_Intrinsics_vec128 *wv3;
      Lib_IntVector_Intrinsics_vec128 *s00;
      Lib_IntVector_Intrinsics_vec128 *s16;
      Lib_IntVector_Intrinsics_vec128 *r00;
      Lib_IntVector_Intrinsics_vec128 *r10;
      Lib_IntVector_Intrinsics_vec128 *r20;
      Lib_IntVector_Intrinsics_vec128 *r30;
      mask =
        Lib_IntVector_Intrinsics_vec128_load32s((uint32_t)totlen,
          (uint32_t)(totlen >> (uint32_t)32U),
          wv_14,
          wv_15);
      memcpy(wv, hash, (uint32_t)4U * (uint32_t)1U * sizeof (Lib_IntVector_Intrinsics_vec128));
      wv3 = wv + (uint32_t)3U * (uint32_t)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < (uint32_t)10U; i++)
        {
          uint32_t start_idx = i % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (uint32_t)4U * (uint32_t)1U);
          {
            Lib_IntVector_Intrinsics_vec128 m_st[(uint32_t)4U * (uint32_t)1U];
            {
              uint32_t _i;
              for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
                m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
            }
            {
              Lib_IntVector_Intrinsics_vec128 *r0 = m_st + (uint32_t)0U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec128 *r1 = m_st + (uint32_t)1U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec128 *r21 = m_st + (uint32_t)2U * (uint32_t)1U;
              Lib_IntVector_Intrinsics_vec128 *r31 = m_st + (uint32_t)3U * (uint32_t)1U;
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
              r0[0U] = Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
              r1[0U] = Lib_IntVector_Intrinsics_vec128_load32s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
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
                uint32_t b0 = (uint32_t)1U;
                uint32_t c0 = (uint32_t)2U;
                uint32_t d10 = (uint32_t)3U;
                Lib_IntVector_Intrinsics_vec128 *wv_a0 = wv + a * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec128 *wv_b0 = wv + b0 * (uint32_t)1U;
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                {
                  Lib_IntVector_Intrinsics_vec128 *wv_a1 = wv + d10 * (uint32_t)1U;
                  Lib_IntVector_Intrinsics_vec128 *wv_b1 = wv + a * (uint32_t)1U;
                  wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                  wv_a1[0U] =
                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U],
                      (uint32_t)16U);
                  {
                    Lib_IntVector_Intrinsics_vec128 *wv_a2 = wv + c0 * (uint32_t)1U;
                    Lib_IntVector_Intrinsics_vec128 *wv_b2 = wv + d10 * (uint32_t)1U;
                    wv_a2[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U], wv_b2[0U]);
                    {
                      Lib_IntVector_Intrinsics_vec128 *wv_a3 = wv + b0 * (uint32_t)1U;
                      Lib_IntVector_Intrinsics_vec128 *wv_b3 = wv + c0 * (uint32_t)1U;
                      wv_a3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U], wv_b3[0U]);
                      wv_a3[0U] =
                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                          (uint32_t)12U);
                      {
                        Lib_IntVector_Intrinsics_vec128 *wv_a4 = wv + a * (uint32_t)1U;
                        Lib_IntVector_Intrinsics_vec128 *wv_b4 = wv + b0 * (uint32_t)1U;
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U], wv_b4[0U]);
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U], y[0U]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *wv_a5 = wv + d10 * (uint32_t)1U;
                          Lib_IntVector_Intrinsics_vec128 *wv_b5 = wv + a * (uint32_t)1U;
                          wv_a5[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U], wv_b5[0U]);
                          wv_a5[0U] =
                            Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                              (uint32_t)8U);
                          {
                            Lib_IntVector_Intrinsics_vec128 *wv_a6 = wv + c0 * (uint32_t)1U;
                            Lib_IntVector_Intrinsics_vec128 *wv_b6 = wv + d10 * (uint32_t)1U;
                            wv_a6[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U], wv_b6[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec128 *wv_a7 = wv + b0 * (uint32_t)1U;
                              Lib_IntVector_Intrinsics_vec128 *wv_b7 = wv + c0 * (uint32_t)1U;
                              wv_a7[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U], wv_b7[0U]);
                              wv_a7[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                  (uint32_t)7U);
                              {
                                Lib_IntVector_Intrinsics_vec128
                                *r11 = wv + (uint32_t)1U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *r22 = wv + (uint32_t)2U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128
                                *r32 = wv + (uint32_t)3U * (uint32_t)1U;
                                Lib_IntVector_Intrinsics_vec128 v00 = r11[0U];
                                Lib_IntVector_Intrinsics_vec128
                                v1 =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                    (uint32_t)1U);
                                r11[0U] = v1;
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
                                      uint32_t b = (uint32_t)1U;
                                      uint32_t c = (uint32_t)2U;
                                      uint32_t d1 = (uint32_t)3U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_a = wv + a0 * (uint32_t)1U;
                                      Lib_IntVector_Intrinsics_vec128
                                      *wv_b8 = wv + b * (uint32_t)1U;
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                          wv_b8[0U]);
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                          z[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_a8 = wv + d1 * (uint32_t)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *wv_b9 = wv + a0 * (uint32_t)1U;
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                            wv_b9[0U]);
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                            (uint32_t)16U);
                                        {
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_a9 = wv + c * (uint32_t)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b10 = wv + d1 * (uint32_t)1U;
                                          wv_a9[0U] =
                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                              wv_b10[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_a10 = wv + b * (uint32_t)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_b11 = wv + c * (uint32_t)1U;
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                wv_b11[0U]);
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                (uint32_t)12U);
                                            {
                                              Lib_IntVector_Intrinsics_vec128
                                              *wv_a11 = wv + a0 * (uint32_t)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *wv_b12 = wv + b * (uint32_t)1U;
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                  wv_b12[0U]);
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                  w[0U]);
                                              {
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a12 = wv + d1 * (uint32_t)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b13 = wv + a0 * (uint32_t)1U;
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                    wv_b13[0U]);
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                    (uint32_t)8U);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a13 = wv + c * (uint32_t)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b14 = wv + d1 * (uint32_t)1U;
                                                  wv_a13[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                      wv_b14[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a14 = wv + b * (uint32_t)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b = wv + c * (uint32_t)1U;
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                        wv_b[0U]);
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                        (uint32_t)7U);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *r12 = wv + (uint32_t)1U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *r2 = wv + (uint32_t)2U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *r3 = wv + (uint32_t)3U * (uint32_t)1U;
                                                      Lib_IntVector_Intrinsics_vec128 v0 = r12[0U];
                                                      Lib_IntVector_Intrinsics_vec128
                                                      v12 =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                          (uint32_t)3U);
                                                      r12[0U] = v12;
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
      s00 = hash + (uint32_t)0U * (uint32_t)1U;
      s16 = hash + (uint32_t)1U * (uint32_t)1U;
      r00 = wv + (uint32_t)0U * (uint32_t)1U;
      r10 = wv + (uint32_t)1U * (uint32_t)1U;
      r20 = wv + (uint32_t)2U * (uint32_t)1U;
      r30 = wv + (uint32_t)3U * (uint32_t)1U;
      s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r00[0U]);
      s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r20[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r10[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r30[0U]);
    }
  }
}

void
Hacl_Blake2s_128_blake2s(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
)
{
  uint32_t stlen = (uint32_t)4U * (uint32_t)1U;
  Lib_IntVector_Intrinsics_vec128 stzero = Lib_IntVector_Intrinsics_vec128_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), stlen);
  {
    Lib_IntVector_Intrinsics_vec128 b[stlen];
    {
      uint32_t _i;
      for (_i = 0U; _i < stlen; ++_i)
        b[_i] = stzero;
    }
    {
      uint64_t prev0;
      if (kk == (uint32_t)0U)
      {
        prev0 = (uint64_t)(uint32_t)0U;
      }
      else
      {
        prev0 = (uint64_t)(uint32_t)64U;
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), stlen);
      {
        Lib_IntVector_Intrinsics_vec128 b1[stlen];
        {
          uint32_t _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        {
          uint8_t b20[64U] = { 0U };
          Lib_IntVector_Intrinsics_vec128 *r0 = b + (uint32_t)0U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec128 *r1 = b + (uint32_t)1U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec128 *r2 = b + (uint32_t)2U * (uint32_t)1U;
          Lib_IntVector_Intrinsics_vec128 *r3 = b + (uint32_t)3U * (uint32_t)1U;
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
          uint32_t nb0;
          uint32_t rem0;
          K___uint32_t_uint32_t scrut;
          uint32_t nb;
          uint32_t rem;
          r2[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
          r3[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
          kk_shift_8 = kk << (uint32_t)8U;
          iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ nn));
          r0[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1, iv2, iv3);
          r1[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
          if (!(kk == (uint32_t)0U))
          {
            memcpy(b20, k, kk * sizeof (uint8_t));
            {
              uint64_t totlen = (uint64_t)(uint32_t)0U + (uint64_t)(uint32_t)64U;
              uint8_t *b3 = b20 + (uint32_t)0U * (uint32_t)64U;
              blake2s_update_block(b1, b, false, totlen, b3);
            }
          }
          Lib_Memzero0_memzero(b20, (uint32_t)64U * sizeof (b20[0U]));
          nb0 = ll / (uint32_t)64U;
          rem0 = ll % (uint32_t)64U;
          if (rem0 == (uint32_t)0U && nb0 > (uint32_t)0U)
          {
            uint32_t nb_ = nb0 - (uint32_t)1U;
            uint32_t rem_ = (uint32_t)64U;
            K___uint32_t_uint32_t lit;
            lit.fst = nb_;
            lit.snd = rem_;
            scrut = lit;
          }
          else
          {
            K___uint32_t_uint32_t lit;
            lit.fst = nb0;
            lit.snd = rem0;
            scrut = lit;
          }
          nb = scrut.fst;
          rem = scrut.snd;
          {
            uint32_t i;
            for (i = (uint32_t)0U; i < nb; i++)
            {
              uint64_t totlen = prev0 + (uint64_t)((i + (uint32_t)1U) * (uint32_t)64U);
              uint8_t *b2 = d + i * (uint32_t)64U;
              blake2s_update_block(b1, b, false, totlen, b2);
            }
          }
          {
            uint8_t b21[64U] = { 0U };
            uint8_t *last = d + ll - rem;
            uint64_t totlen;
            uint32_t double_row;
            memcpy(b21, last, rem * sizeof (uint8_t));
            totlen = prev0 + (uint64_t)ll;
            blake2s_update_block(b1, b, true, totlen, b21);
            Lib_Memzero0_memzero(b21, (uint32_t)64U * sizeof (b21[0U]));
            double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)4U;
            KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
            {
              uint8_t b2[double_row];
              memset(b2, 0U, double_row * sizeof (uint8_t));
              {
                uint8_t *first = b2;
                uint8_t *second = b2 + (uint32_t)4U * (uint32_t)4U;
                Lib_IntVector_Intrinsics_vec128 *row0 = b + (uint32_t)0U * (uint32_t)1U;
                Lib_IntVector_Intrinsics_vec128 *row1 = b + (uint32_t)1U * (uint32_t)1U;
                uint8_t *final;
                Lib_IntVector_Intrinsics_vec128_store_le(first, row0[0U]);
                Lib_IntVector_Intrinsics_vec128_store_le(second, row1[0U]);
                final = b2;
                memcpy(output, final, nn * sizeof (uint8_t));
                Lib_Memzero0_memzero(b2, double_row * sizeof (b2[0U]));
                Lib_Memzero0_memzero(b1, stlen * sizeof (b1[0U]));
                Lib_Memzero0_memzero(b, stlen * sizeof (b[0U]));
              }
            }
          }
        }
      }
    }
  }
}

