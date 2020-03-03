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


#include "Hacl_Blake2s_256.h"

static inline void
blake2s_update_block(Lib_IntVector_Intrinsics_vec128 *hash, bool flag, u64 totlen, u8 *d)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (u32)4U * (u32)1U);
  {
    Lib_IntVector_Intrinsics_vec128 b[(u32)4U * (u32)1U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)4U * (u32)1U; ++_i)
        b[_i] = Lib_IntVector_Intrinsics_vec128_zero;
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
        memcpy(b, hash, (u32)4U * (u32)1U * sizeof (hash[0U]));
        wv3 = b + (u32)3U * (u32)1U;
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
                u32 nb = (u32)4U;
                u8 *b00 = d + s0 * nb;
                u8 *b10 = d + s2 * nb;
                u8 *b20 = d + s4 * nb;
                u8 *b30 = d + s6 * nb;
                u32 u0 = load32_le(b00);
                u32 u00 = u0;
                u32 u1 = load32_le(b10);
                u32 u11 = u1;
                u32 u2 = load32_le(b20);
                u32 u20 = u2;
                u32 u3 = load32_le(b30);
                u32 u30 = u3;
                r01[0U] = Lib_IntVector_Intrinsics_vec128_load32s(u00, u11, u20, u30);
                {
                  u32 nb0 = (u32)4U;
                  u8 *b01 = d + s1 * nb0;
                  u8 *b11 = d + s3 * nb0;
                  u8 *b21 = d + s5 * nb0;
                  u8 *b31 = d + s7 * nb0;
                  u32 u4 = load32_le(b01);
                  u32 u01 = u4;
                  u32 u5 = load32_le(b11);
                  u32 u110 = u5;
                  u32 u6 = load32_le(b21);
                  u32 u21 = u6;
                  u32 u7 = load32_le(b31);
                  u32 u31 = u7;
                  r11[0U] = Lib_IntVector_Intrinsics_vec128_load32s(u01, u110, u21, u31);
                  {
                    u32 nb1 = (u32)4U;
                    u8 *b02 = d + s8 * nb1;
                    u8 *b12 = d + s10 * nb1;
                    u8 *b22 = d + s12 * nb1;
                    u8 *b32 = d + s14 * nb1;
                    u32 u8 = load32_le(b02);
                    u32 u02 = u8;
                    u32 u9 = load32_le(b12);
                    u32 u111 = u9;
                    u32 u10 = load32_le(b22);
                    u32 u22 = u10;
                    u32 u12 = load32_le(b32);
                    u32 u32 = u12;
                    r21[0U] = Lib_IntVector_Intrinsics_vec128_load32s(u02, u111, u22, u32);
                    {
                      u32 nb2 = (u32)4U;
                      u8 *b0 = d + s9 * nb2;
                      u8 *b13 = d + s11 * nb2;
                      u8 *b2 = d + s13 * nb2;
                      u8 *b3 = d + s15 * nb2;
                      u32 u13 = load32_le(b0);
                      u32 u03 = u13;
                      u32 u14 = load32_le(b13);
                      u32 u112 = u14;
                      u32 u15 = load32_le(b2);
                      u32 u23 = u15;
                      u32 u = load32_le(b3);
                      u32 u33 = u;
                      r31[0U] = Lib_IntVector_Intrinsics_vec128_load32s(u03, u112, u23, u33);
                      {
                        Lib_IntVector_Intrinsics_vec128 *x = m_st + (u32)0U * (u32)1U;
                        Lib_IntVector_Intrinsics_vec128 *y = m_st + (u32)1U * (u32)1U;
                        Lib_IntVector_Intrinsics_vec128 *z = m_st + (u32)2U * (u32)1U;
                        Lib_IntVector_Intrinsics_vec128 *w = m_st + (u32)3U * (u32)1U;
                        u32 a = (u32)0U;
                        u32 b14 = (u32)1U;
                        u32 c0 = (u32)2U;
                        u32 d10 = (u32)3U;
                        u32 r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                        u32 r12 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                        u32 r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                        u32 r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                        Lib_IntVector_Intrinsics_vec128 zz0 = Lib_IntVector_Intrinsics_vec128_zero;
                        Lib_IntVector_Intrinsics_vec128 *wv_a0 = b + a * (u32)1U;
                        Lib_IntVector_Intrinsics_vec128 *wv_b0 = b + b14 * (u32)1U;
                        wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], wv_b0[0U]);
                        wv_a0[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a0[0U], x[0U]);
                        {
                          Lib_IntVector_Intrinsics_vec128 *wv_a1 = b + d10 * (u32)1U;
                          Lib_IntVector_Intrinsics_vec128 *wv_b1 = b + a * (u32)1U;
                          wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a1[0U], wv_b1[0U]);
                          wv_a1[0U] = Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a1[0U], r02);
                          {
                            Lib_IntVector_Intrinsics_vec128 *wv_a2 = b + c0 * (u32)1U;
                            Lib_IntVector_Intrinsics_vec128 *wv_b2 = b + d10 * (u32)1U;
                            wv_a2[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U], wv_b2[0U]);
                            wv_a2[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a2[0U], zz0);
                            {
                              Lib_IntVector_Intrinsics_vec128 *wv_a3 = b + b14 * (u32)1U;
                              Lib_IntVector_Intrinsics_vec128 *wv_b3 = b + c0 * (u32)1U;
                              wv_a3[0U] = Lib_IntVector_Intrinsics_vec128_xor(wv_a3[0U], wv_b3[0U]);
                              wv_a3[0U] =
                                Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a3[0U],
                                  r12);
                              {
                                Lib_IntVector_Intrinsics_vec128 *wv_a4 = b + a * (u32)1U;
                                Lib_IntVector_Intrinsics_vec128 *wv_b4 = b + b14 * (u32)1U;
                                wv_a4[0U] =
                                  Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U],
                                    wv_b4[0U]);
                                wv_a4[0U] = Lib_IntVector_Intrinsics_vec128_add32(wv_a4[0U], y[0U]);
                                {
                                  Lib_IntVector_Intrinsics_vec128 *wv_a5 = b + d10 * (u32)1U;
                                  Lib_IntVector_Intrinsics_vec128 *wv_b5 = b + a * (u32)1U;
                                  wv_a5[0U] =
                                    Lib_IntVector_Intrinsics_vec128_xor(wv_a5[0U],
                                      wv_b5[0U]);
                                  wv_a5[0U] =
                                    Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a5[0U],
                                      r22);
                                  {
                                    Lib_IntVector_Intrinsics_vec128 *wv_a6 = b + c0 * (u32)1U;
                                    Lib_IntVector_Intrinsics_vec128 *wv_b6 = b + d10 * (u32)1U;
                                    wv_a6[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                        wv_b6[0U]);
                                    wv_a6[0U] =
                                      Lib_IntVector_Intrinsics_vec128_add32(wv_a6[0U],
                                        zz0);
                                    {
                                      Lib_IntVector_Intrinsics_vec128 *wv_a7 = b + b14 * (u32)1U;
                                      Lib_IntVector_Intrinsics_vec128 *wv_b7 = b + c0 * (u32)1U;
                                      wv_a7[0U] =
                                        Lib_IntVector_Intrinsics_vec128_xor(wv_a7[0U],
                                          wv_b7[0U]);
                                      wv_a7[0U] =
                                        Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a7[0U],
                                          r32);
                                      {
                                        Lib_IntVector_Intrinsics_vec128
                                        *r13 = b + (u32)1U * (u32)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *r23 = b + (u32)2U * (u32)1U;
                                        Lib_IntVector_Intrinsics_vec128
                                        *r33 = b + (u32)3U * (u32)1U;
                                        Lib_IntVector_Intrinsics_vec128 v00 = r13[0U];
                                        Lib_IntVector_Intrinsics_vec128
                                        v1 =
                                          Lib_IntVector_Intrinsics_vec128_shuffle32(v00,
                                            (u32)1U,
                                            ((u32)1U + (u32)1U) % (u32)4U,
                                            ((u32)1U + (u32)2U) % (u32)4U,
                                            ((u32)1U + (u32)3U) % (u32)4U);
                                        r13[0U] = v1;
                                        {
                                          Lib_IntVector_Intrinsics_vec128 v01 = r23[0U];
                                          Lib_IntVector_Intrinsics_vec128
                                          v10 =
                                            Lib_IntVector_Intrinsics_vec128_shuffle32(v01,
                                              (u32)2U,
                                              ((u32)2U + (u32)1U) % (u32)4U,
                                              ((u32)2U + (u32)2U) % (u32)4U,
                                              ((u32)2U + (u32)3U) % (u32)4U);
                                          r23[0U] = v10;
                                          {
                                            Lib_IntVector_Intrinsics_vec128 v02 = r33[0U];
                                            Lib_IntVector_Intrinsics_vec128
                                            v11 =
                                              Lib_IntVector_Intrinsics_vec128_shuffle32(v02,
                                                (u32)3U,
                                                ((u32)3U + (u32)1U) % (u32)4U,
                                                ((u32)3U + (u32)2U) % (u32)4U,
                                                ((u32)3U + (u32)3U) % (u32)4U);
                                            r33[0U] = v11;
                                            {
                                              u32 a0 = (u32)0U;
                                              u32 b1 = (u32)1U;
                                              u32 c = (u32)2U;
                                              u32 d1 = (u32)3U;
                                              u32 r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                              u32 r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                              u32 r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                              u32 r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                              Lib_IntVector_Intrinsics_vec128
                                              zz = Lib_IntVector_Intrinsics_vec128_zero;
                                              Lib_IntVector_Intrinsics_vec128
                                              *wv_a = b + a0 * (u32)1U;
                                              Lib_IntVector_Intrinsics_vec128
                                              *wv_b8 = b + b1 * (u32)1U;
                                              wv_a[0U] =
                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                  wv_b8[0U]);
                                              wv_a[0U] =
                                                Lib_IntVector_Intrinsics_vec128_add32(wv_a[0U],
                                                  z[0U]);
                                              {
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_a8 = b + d1 * (u32)1U;
                                                Lib_IntVector_Intrinsics_vec128
                                                *wv_b9 = b + a0 * (u32)1U;
                                                wv_a8[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_xor(wv_a8[0U],
                                                    wv_b9[0U]);
                                                wv_a8[0U] =
                                                  Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a8[0U],
                                                    r0);
                                                {
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_a9 = b + c * (u32)1U;
                                                  Lib_IntVector_Intrinsics_vec128
                                                  *wv_b10 = b + d1 * (u32)1U;
                                                  wv_a9[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                      wv_b10[0U]);
                                                  wv_a9[0U] =
                                                    Lib_IntVector_Intrinsics_vec128_add32(wv_a9[0U],
                                                      zz);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_a10 = b + b1 * (u32)1U;
                                                    Lib_IntVector_Intrinsics_vec128
                                                    *wv_b11 = b + c * (u32)1U;
                                                    wv_a10[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_xor(wv_a10[0U],
                                                        wv_b11[0U]);
                                                    wv_a10[0U] =
                                                      Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a10[0U],
                                                        r1);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_a11 = b + a0 * (u32)1U;
                                                      Lib_IntVector_Intrinsics_vec128
                                                      *wv_b12 = b + b1 * (u32)1U;
                                                      wv_a11[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                          wv_b12[0U]);
                                                      wv_a11[0U] =
                                                        Lib_IntVector_Intrinsics_vec128_add32(wv_a11[0U],
                                                          w[0U]);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_a12 = b + d1 * (u32)1U;
                                                        Lib_IntVector_Intrinsics_vec128
                                                        *wv_b13 = b + a0 * (u32)1U;
                                                        wv_a12[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_xor(wv_a12[0U],
                                                            wv_b13[0U]);
                                                        wv_a12[0U] =
                                                          Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a12[0U],
                                                            r24);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_a13 = b + c * (u32)1U;
                                                          Lib_IntVector_Intrinsics_vec128
                                                          *wv_b14 = b + d1 * (u32)1U;
                                                          wv_a13[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                              wv_b14[0U]);
                                                          wv_a13[0U] =
                                                            Lib_IntVector_Intrinsics_vec128_add32(wv_a13[0U],
                                                              zz);
                                                          {
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_a14 = b + b1 * (u32)1U;
                                                            Lib_IntVector_Intrinsics_vec128
                                                            *wv_b = b + c * (u32)1U;
                                                            wv_a14[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_xor(wv_a14[0U],
                                                                wv_b[0U]);
                                                            wv_a14[0U] =
                                                              Lib_IntVector_Intrinsics_vec128_rotate_right32(wv_a14[0U],
                                                                r34);
                                                            {
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *r14 = b + (u32)1U * (u32)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *r2 = b + (u32)2U * (u32)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              *r3 = b + (u32)3U * (u32)1U;
                                                              Lib_IntVector_Intrinsics_vec128
                                                              v0 = r14[0U];
                                                              Lib_IntVector_Intrinsics_vec128
                                                              v12 =
                                                                Lib_IntVector_Intrinsics_vec128_shuffle32(v0,
                                                                  (u32)3U,
                                                                  ((u32)3U + (u32)1U) % (u32)4U,
                                                                  ((u32)3U + (u32)2U) % (u32)4U,
                                                                  ((u32)3U + (u32)3U) % (u32)4U);
                                                              r14[0U] = v12;
                                                              {
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v03 = r2[0U];
                                                                Lib_IntVector_Intrinsics_vec128
                                                                v13 =
                                                                  Lib_IntVector_Intrinsics_vec128_shuffle32(v03,
                                                                    (u32)2U,
                                                                    ((u32)2U + (u32)1U) % (u32)4U,
                                                                    ((u32)2U + (u32)2U) % (u32)4U,
                                                                    ((u32)2U + (u32)3U) % (u32)4U);
                                                                r2[0U] = v13;
                                                                {
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v04 = r3[0U];
                                                                  Lib_IntVector_Intrinsics_vec128
                                                                  v14 =
                                                                    Lib_IntVector_Intrinsics_vec128_shuffle32(v04,
                                                                      (u32)1U,
                                                                      ((u32)1U + (u32)1U) % (u32)4U,
                                                                      ((u32)1U + (u32)2U) % (u32)4U,
                                                                      ((u32)1U + (u32)3U) % (u32)4U);
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
            }
          }
        }
        s00 = hash + (u32)0U * (u32)1U;
        s16 = hash + (u32)1U * (u32)1U;
        r00 = b + (u32)0U * (u32)1U;
        r10 = b + (u32)1U * (u32)1U;
        r20 = b + (u32)2U * (u32)1U;
        r30 = b + (u32)3U * (u32)1U;
        s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r00[0U]);
        s00[0U] = Lib_IntVector_Intrinsics_vec128_xor(s00[0U], r20[0U]);
        s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r10[0U]);
        s16[0U] = Lib_IntVector_Intrinsics_vec128_xor(s16[0U], r30[0U]);
        {
          u32 _i;
          for (_i = 0U; _i < (u32)4U * (u32)1U; ++_i)
            b[_i] = Lib_IntVector_Intrinsics_vec128_zero;
        }
      }
    }
  }
}

void Hacl_Blake2s_256_blake2s(u32 nn, u8 *output, u32 ll, u8 *d, u32 kk, u8 *k)
{
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec128), (u32)4U * (u32)1U);
  {
    Lib_IntVector_Intrinsics_vec128 h[(u32)4U * (u32)1U];
    {
      u32 _i;
      for (_i = 0U; _i < (u32)4U * (u32)1U; ++_i)
        h[_i] = Lib_IntVector_Intrinsics_vec128_zero;
    }
    {
      u64 prev0;
      if (kk == (u32)0U)
        prev0 = (u64)(u32)0U;
      else
        prev0 = (u64)(u32)64U;
      {
        u8 b0[64U] = { 0U };
        Lib_IntVector_Intrinsics_vec128 *r0 = h + (u32)0U * (u32)1U;
        Lib_IntVector_Intrinsics_vec128 *r1 = h + (u32)1U * (u32)1U;
        Lib_IntVector_Intrinsics_vec128 *r2 = h + (u32)2U * (u32)1U;
        Lib_IntVector_Intrinsics_vec128 *r3 = h + (u32)3U * (u32)1U;
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
        u32 rem1;
        K___u32_u32 scrut;
        u32 nb;
        r2[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
        r3[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
        kk_shift_8 = kk << (u32)8U;
        iv0_ = iv0 ^ ((u32)0x01010000U ^ (kk_shift_8 ^ nn));
        r0[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1, iv2, iv3);
        r1[0U] = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
        if (!(kk == (u32)0U))
        {
          memcpy(b0, k, kk * sizeof (k[0U]));
          {
            u64 totlen = (u64)(u32)0U + (u64)(u32)64U;
            u8 *b1 = b0 + (u32)0U * (u32)64U;
            blake2s_update_block(h, false, totlen, b1);
          }
        }
        memset(b0, 0U, (u32)64U * sizeof (b0[0U]));
        nb0 = ll / (u32)64U;
        rem1 = ll % (u32)64U;
        if (rem1 == (u32)0U && nb0 > (u32)0U)
        {
          u32 nb_ = nb0 - (u32)1U;
          u32 rem_ = (u32)64U;
          scrut = ((K___u32_u32){ .fst = nb_, .snd = rem_ });
        }
        else
          scrut = ((K___u32_u32){ .fst = nb0, .snd = rem1 });
        nb = scrut.fst;
        {
          u32 i;
          for (i = (u32)0U; i < nb; i++)
          {
            u64 totlen = prev0 + (u64)((i + (u32)1U) * (u32)64U);
            u8 *b = d + i * (u32)64U;
            blake2s_update_block(h, false, totlen, b);
          }
        }
        {
          u32 rem2 = ll % (u32)64U;
          u8 *last1 = d + ll - rem2;
          u8 last_block[64U] = { 0U };
          u64 totlen;
          memcpy(last_block, last1, rem2 * sizeof (last1[0U]));
          totlen = prev0 + (u64)ll;
          blake2s_update_block(h, true, totlen, last_block);
          KRML_CHECK_SIZE(sizeof (u8), (u32)2U * (u32)4U * (u32)4U);
          {
            u8 b[(u32)2U * (u32)4U * (u32)4U];
            memset(b, 0U, (u32)2U * (u32)4U * (u32)4U * sizeof (b[0U]));
            {
              u8 *final;
              Lib_IntVector_Intrinsics_vec128_store_le(b, (h + (u32)0U * (u32)1U)[0U]);
              Lib_IntVector_Intrinsics_vec128_store_le(b + (u32)4U * (u32)4U,
                (h + (u32)1U * (u32)1U)[0U]);
              final = b;
              memcpy(output, final, nn * sizeof (final[0U]));
              memset(b, 0U, (u32)2U * (u32)4U * (u32)4U * sizeof (b[0U]));
            }
          }
        }
      }
    }
  }
}

