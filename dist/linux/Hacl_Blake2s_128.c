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
  u64 totlen,
  u8 *d
)
{
  u32 m_w[16U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)16U; i++)
    {
      u32 *os = m_w;
      u8 *bj = d + i * (u32)4U;
      u32 u = load32_le(bj);
      u32 r = u;
      u32 x = r;
      os[i] = x;
    }
  }
  {
    Lib_IntVector_Intrinsics_vec128 mask = Lib_IntVector_Intrinsics_vec128_zero;
    u32 wv_14;
    if (flag)
      wv_14 = (u32)0xFFFFFFFFU;
    else
      wv_14 = (u32)0U;
    {
      u32 wv_15 = (u32)0U;
      Lib_IntVector_Intrinsics_vec128 *wv3;
      Lib_IntVector_Intrinsics_vec128 *s00;
      Lib_IntVector_Intrinsics_vec128 *s16;
      Lib_IntVector_Intrinsics_vec128 *r00;
      Lib_IntVector_Intrinsics_vec128 *r10;
      Lib_IntVector_Intrinsics_vec128 *r20;
      Lib_IntVector_Intrinsics_vec128 *r30;
      mask =
        Lib_IntVector_Intrinsics_vec128_load32s((u32)totlen,
          (u32)(totlen >> (u32)32U),
          wv_14,
          wv_15);
      memcpy(wv, hash, (u32)4U * (u32)1U * sizeof (hash[0U]));
      wv3 = wv + (u32)3U * (u32)1U;
      wv3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv3[0U], mask);
      {
        u32 i;
        for (i = (u32)0U; i < (u32)10U; i++)
        {
          u32 start_idx = i % (u32)10U * (u32)16U;
          KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (u32)4U * (u32)1U);
          {
            Lib_IntVector_Intrinsics_vec128 m_st[(u32)4U * (u32)1U];
            {
              u32 _i;
              for (_i = 0U; _i < (u32)4U * (u32)1U; ++_i)
                m_st[_i] = Lib_IntVector_Intrinsics_vec128_zero;
            }
            {
              Lib_IntVector_Intrinsics_vec128 *r01 = m_st + (u32)0U * (u32)1U;
              Lib_IntVector_Intrinsics_vec128 *r11 = m_st + (u32)1U * (u32)1U;
              Lib_IntVector_Intrinsics_vec128 *r21 = m_st + (u32)2U * (u32)1U;
              Lib_IntVector_Intrinsics_vec128 *r31 = m_st + (u32)3U * (u32)1U;
              u32 s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
              u32 s1 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)1U];
              u32 s2 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)2U];
              u32 s3 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)3U];
              u32 s4 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)4U];
              u32 s5 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)5U];
              u32 s6 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)6U];
              u32 s7 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)7U];
              u32 s8 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)8U];
              u32 s9 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)9U];
              u32 s10 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)10U];
              u32 s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)11U];
              u32 s12 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)12U];
              u32 s13 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)13U];
              u32 s14 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)14U];
              u32 s15 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (u32)15U];
              r01[0U] = Lib_IntVector_Intrinsics_vec128_load32s(m_w[s0], m_w[s2], m_w[s4], m_w[s6]);
              r11[0U] = Lib_IntVector_Intrinsics_vec128_load32s(m_w[s1], m_w[s3], m_w[s5], m_w[s7]);
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
                Lib_IntVector_Intrinsics_vec128 *x = m_st + (u32)0U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *y = m_st + (u32)1U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *z = m_st + (u32)2U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *w = m_st + (u32)3U * (u32)1U;
                u32 a = (u32)0U;
                u32 b0 = (u32)1U;
                u32 c0 = (u32)2U;
                u32 d10 = (u32)3U;
                u32 r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                u32 r12 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                u32 r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                u32 r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                Lib_IntVector_Intrinsics_vec128 *wv_a0 = wv + a * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *wv_b0 = wv + b0 * (u32)1U;
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                {
                  Lib_IntVector_Intrinsics_vec128 *wv_a1 = wv + d10 * (u32)1U;
                  Lib_IntVector_Intrinsics_vec128 *wv_b1 = wv + a * (u32)1U;
                  wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                  wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U], r02);
                  {
                    Lib_IntVector_Intrinsics_vec128 *wv_a2 = wv + c0 * (u32)1U;
                    Lib_IntVector_Intrinsics_vec128 *wv_b2 = wv + d10 * (u32)1U;
                    wv_a2[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U], wv_b2[0U]);
                    {
                      Lib_IntVector_Intrinsics_vec128 *wv_a3 = wv + b0 * (u32)1U;
                      Lib_IntVector_Intrinsics_vec128 *wv_b3 = wv + c0 * (u32)1U;
                      wv_a3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U], wv_b3[0U]);
                      wv_a3[0U] = Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U], r12);
                      {
                        Lib_IntVector_Intrinsics_vec128 *wv_a4 = wv + a * (u32)1U;
                        Lib_IntVector_Intrinsics_vec128 *wv_b4 = wv + b0 * (u32)1U;
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U], wv_b4[0U]);
                        wv_a4[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U], y[0U]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *wv_a5 = wv + d10 * (u32)1U;
                          Lib_IntVector_Intrinsics_vec128 *wv_b5 = wv + a * (u32)1U;
                          wv_a5[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U], wv_b5[0U]);
                          wv_a5[0U] = Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U], r22);
                          {
                            Lib_IntVector_Intrinsics_vec128 *wv_a6 = wv + c0 * (u32)1U;
                            Lib_IntVector_Intrinsics_vec128 *wv_b6 = wv + d10 * (u32)1U;
                            wv_a6[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U], wv_b6[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec128 *wv_a7 = wv + b0 * (u32)1U;
                              Lib_IntVector_Intrinsics_vec128 *wv_b7 = wv + c0 * (u32)1U;
                              wv_a7[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U], wv_b7[0U]);
                              wv_a7[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                  r32);
                              {
                                Lib_IntVector_Intrinsics_vec128 *r13 = wv + (u32)1U * (u32)1U;
                                Lib_IntVector_Intrinsics_vec128 *r23 = wv + (u32)2U * (u32)1U;
                                Lib_IntVector_Intrinsics_vec128 *r33 = wv + (u32)3U * (u32)1U;
                                Lib_IntVector_Intrinsics_vec128 v00 = r13[0U];
                                Lib_IntVector_Intrinsics_vec128
                                v1 =
                                  Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v00,
                                    (u32)1U);
                                r13[0U] = v1;
                                {
                                  Lib_IntVector_Intrinsics_vec128 v01 = r23[0U];
                                  Lib_IntVector_Intrinsics_vec128
                                  v10 =
                                    Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v01,
                                      (u32)2U);
                                  r23[0U] = v10;
                                  {
                                    Lib_IntVector_Intrinsics_vec128 v02 = r33[0U];
                                    Lib_IntVector_Intrinsics_vec128
                                    v11 =
                                      Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v02,
                                        (u32)3U);
                                    r33[0U] = v11;
                                    {
                                      u32 a0 = (u32)0U;
                                      u32 b = (u32)1U;
                                      u32 c = (u32)2U;
                                      u32 d1 = (u32)3U;
                                      u32 r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                      u32 r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                      u32 r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                      u32 r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                      Lib_IntVector_Intrinsics_vec128 *wv_a = wv + a0 * (u32)1U;
                                      Lib_IntVector_Intrinsics_vec128 *wv_b8 = wv + b * (u32)1U;
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                          wv_b8[0U]);
                                      wv_a[0U] =
                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                          z[0U]);
                                      {
                                        Lib_IntVector_Intrinsics_vec128 *wv_a8 = wv + d1 * (u32)1U;
                                        Lib_IntVector_Intrinsics_vec128 *wv_b9 = wv + a0 * (u32)1U;
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                            wv_b9[0U]);
                                        wv_a8[0U] =
                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                            r0);
                                        {
                                          Lib_IntVector_Intrinsics_vec128 *wv_a9 = wv + c * (u32)1U;
                                          Lib_IntVector_Intrinsics_vec128
                                          *wv_b10 = wv + d1 * (u32)1U;
                                          wv_a9[0U] =
                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                              wv_b10[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_a10 = wv + b * (u32)1U;
                                            Lib_IntVector_Intrinsics_vec128
                                            *wv_b11 = wv + c * (u32)1U;
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                wv_b11[0U]);
                                            wv_a10[0U] =
                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                r1);
                                            {
                                              Lib_IntVector_Intrinsics_vec128
                                              *wv_a11 = wv + a0 * (u32)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *wv_b12 = wv + b * (u32)1U;
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                  wv_b12[0U]);
                                              wv_a11[0U] =
                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                  w[0U]);
                                              {
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a12 = wv + d1 * (u32)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b13 = wv + a0 * (u32)1U;
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                    wv_b13[0U]);
                                                wv_a12[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                    r24);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a13 = wv + c * (u32)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b14 = wv + d1 * (u32)1U;
                                                  wv_a13[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                      wv_b14[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a14 = wv + b * (u32)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b = wv + c * (u32)1U;
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                        wv_b[0U]);
                                                    wv_a14[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                        r34);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *r14 = wv + (u32)1U * (u32)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *r2 = wv + (u32)2U * (u32)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *r3 = wv + (u32)3U * (u32)1U;
                                                      Lib_IntVector_Intrinsics_vec128 v0 = r14[0U];
                                                      Lib_IntVector_Intrinsics_vec128
                                                      v12 =
                                                        Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v0,
                                                          (u32)3U);
                                                      r14[0U] = v12;
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        v03 = r2[0U];
                                                        Lib_IntVector_Intrinsics_vec128
                                                        v13 =
                                                          Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v03,
                                                            (u32)2U);
                                                        r2[0U] = v13;
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          v04 = r3[0U];
                                                          Lib_IntVector_Intrinsics_vec128
                                                          v14 =
                                                            Lib_IntVector_Intrinsics_vec128_rotate_right_lanes32(v04,
                                                              (u32)1U);
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
      s00 = hash + (u32)0U * (u32)1U;
      s16 = hash + (u32)1U * (u32)1U;
      r00 = wv + (u32)0U * (u32)1U;
      r10 = wv + (u32)1U * (u32)1U;
      r20 = wv + (u32)2U * (u32)1U;
      r30 = wv + (u32)3U * (u32)1U;
      s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r00[0U]);
      s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r20[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r10[0U]);
      s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r30[0U]);
    }
  }
}

void Hacl_Blake2s_128_blake2s(u32 nn, u8 *output, u32 ll, u8 *d, u32 kk, u8 *k)
{
  u32 stlen = (u32)4U * (u32)1U;
  Lib_IntVector_Intrinsics_vec128 stzero = Lib_IntVector_Intrinsics_vec128_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), stlen);
  {
    Lib_IntVector_Intrinsics_vec128 b[stlen];
    {
      u32 _i;
      for (_i = 0U; _i < stlen; ++_i)
        b[_i] = stzero;
    }
    {
      u64 prev0;
      if (kk == (u32)0U)
        prev0 = (u64)(u32)0U;
      else
        prev0 = (u64)(u32)64U;
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), stlen);
      {
        Lib_IntVector_Intrinsics_vec128 b1[stlen];
        {
          u32 _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        {
          u8 b20[64U] = { 0U };
          Lib_IntVector_Intrinsics_vec128 *r0 = b + (u32)0U * (u32)1U;
          Lib_IntVector_Intrinsics_vec128 *r1 = b + (u32)1U * (u32)1U;
          Lib_IntVector_Intrinsics_vec128 *r2 = b + (u32)2U * (u32)1U;
          Lib_IntVector_Intrinsics_vec128 *r3 = b + (u32)3U * (u32)1U;
          u32 iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
          u32 iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
          u32 iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
          u32 iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
          u32 iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
          u32 iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
          u32 iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
          u32 iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
          u32 kk_shift_8;
          u32 iv0_;
          u32 nb0;
          u32 rem0;
          K___u32_u32 scrut;
          u32 nb;
          u32 rem;
          r2[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
          r3[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
          kk_shift_8 = kk << (u32)8U;
          iv0_ = iv0 ^ ((u32)0x01010000U ^ (kk_shift_8 ^ nn));
          r0[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1, iv2, iv3);
          r1[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
          if (!(kk == (u32)0U))
          {
            memcpy(b20, k, kk * sizeof (k[0U]));
            {
              u64 totlen = (u64)(u32)0U + (u64)(u32)64U;
              u8 *b3 = b20 + (u32)0U * (u32)64U;
              blake2s_update_block(b1, b, false, totlen, b3);
            }
          }
          memset(b20, 0U, (u32)64U * sizeof (b20[0U]));
          nb0 = ll / (u32)64U;
          rem0 = ll % (u32)64U;
          if (rem0 == (u32)0U && nb0 > (u32)0U)
          {
            u32 nb_ = nb0 - (u32)1U;
            u32 rem_ = (u32)64U;
            scrut = ((K___u32_u32){ .fst = nb_, .snd = rem_ });
          }
          else
            scrut = ((K___u32_u32){ .fst = nb0, .snd = rem0 });
          nb = scrut.fst;
          rem = scrut.snd;
          {
            u32 i;
            for (i = (u32)0U; i < nb; i++)
            {
              u64 totlen = prev0 + (u64)((i + (u32)1U) * (u32)64U);
              u8 *b2 = d + i * (u32)64U;
              blake2s_update_block(b1, b, false, totlen, b2);
            }
          }
          {
            u8 b21[64U] = { 0U };
            u8 *last = d + ll - rem;
            u64 totlen;
            u32 double_row;
            memcpy(b21, last, rem * sizeof (last[0U]));
            totlen = prev0 + (u64)ll;
            blake2s_update_block(b1, b, true, totlen, b21);
            memset(b21, 0U, (u32)64U * sizeof (b21[0U]));
            double_row = (u32)2U * (u32)4U * (u32)4U;
            KRML_CHECK_SIZE(sizeof (u8), double_row);
            {
              u8 b2[double_row];
              memset(b2, 0U, double_row * sizeof (b2[0U]));
              {
                u8 *first = b2;
                u8 *second = b2 + (u32)4U * (u32)4U;
                Lib_IntVector_Intrinsics_vec128 *row0 = b + (u32)0U * (u32)1U;
                Lib_IntVector_Intrinsics_vec128 *row1 = b + (u32)1U * (u32)1U;
                u8 *final;
                Lib_IntVector_Intrinsics_vec128_store_le(first, row0[0U]);
                Lib_IntVector_Intrinsics_vec128_store_le(second, row1[0U]);
                final = b2;
                memcpy(output, final, nn * sizeof (final[0U]));
                memset(b2, 0U, double_row * sizeof (b2[0U]));
                {
                  u32 _i;
                  for (_i = 0U; _i < stlen; ++_i)
                    b1[_i] = stzero;
                }
                {
                  u32 _i;
                  for (_i = 0U; _i < stlen; ++_i)
                    b[_i] = stzero;
                }
              }
            }
          }
        }
      }
    }
  }
}

