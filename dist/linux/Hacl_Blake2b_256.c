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


#include "Hacl_Blake2b_256.h"

static inline void
blake2b_update_block(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  bool flag,
  uint128_t totlen,
  u8 *d
)
{
  Lib_IntVector_Intrinsics_vec256 mask = Lib_IntVector_Intrinsics_vec256_zero;
  u64 wv_14;
  if (flag)
    wv_14 = (u64)0xFFFFFFFFFFFFFFFFU;
  else
    wv_14 = (u64)0U;
  {
    u64 wv_15 = (u64)0U;
    Lib_IntVector_Intrinsics_vec256 *wv3;
    Lib_IntVector_Intrinsics_vec256 *s00;
    Lib_IntVector_Intrinsics_vec256 *s16;
    Lib_IntVector_Intrinsics_vec256 *r00;
    Lib_IntVector_Intrinsics_vec256 *r10;
    Lib_IntVector_Intrinsics_vec256 *r20;
    Lib_IntVector_Intrinsics_vec256 *r30;
    mask =
      Lib_IntVector_Intrinsics_vec256_load64s((uint64_t)totlen,
        (uint64_t)(totlen >> (u32)64U),
        wv_14,
        wv_15);
    memcpy(wv, hash, (u32)4U * (u32)1U * sizeof (hash[0U]));
    wv3 = wv + (u32)3U * (u32)1U;
    wv3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv3[0U], mask);
    {
      u32 i;
      for (i = (u32)0U; i < (u32)12U; i++)
      {
        u32 start_idx = i % (u32)10U * (u32)16U;
        KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (u32)4U * (u32)1U);
        {
          Lib_IntVector_Intrinsics_vec256 m_st[(u32)4U * (u32)1U];
          {
            u32 _i;
            for (_i = 0U; _i < (u32)4U * (u32)1U; ++_i)
              m_st[_i] = Lib_IntVector_Intrinsics_vec256_zero;
          }
          {
            Lib_IntVector_Intrinsics_vec256 *r01 = m_st + (u32)0U * (u32)1U;
            Lib_IntVector_Intrinsics_vec256 *r11 = m_st + (u32)1U * (u32)1U;
            Lib_IntVector_Intrinsics_vec256 *r21 = m_st + (u32)2U * (u32)1U;
            Lib_IntVector_Intrinsics_vec256 *r31 = m_st + (u32)3U * (u32)1U;
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
            u32 nb = (u32)8U;
            u8 *b00 = d + s0 * nb;
            u8 *b10 = d + s2 * nb;
            u8 *b20 = d + s4 * nb;
            u8 *b30 = d + s6 * nb;
            u64 u0 = load64_le(b00);
            u64 u00 = u0;
            u64 u1 = load64_le(b10);
            u64 u10 = u1;
            u64 u2 = load64_le(b20);
            u64 u20 = u2;
            u64 u3 = load64_le(b30);
            u64 u30 = u3;
            r01[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u00, u10, u20, u30);
            {
              u32 nb0 = (u32)8U;
              u8 *b01 = d + s1 * nb0;
              u8 *b11 = d + s3 * nb0;
              u8 *b21 = d + s5 * nb0;
              u8 *b31 = d + s7 * nb0;
              u64 u4 = load64_le(b01);
              u64 u01 = u4;
              u64 u5 = load64_le(b11);
              u64 u11 = u5;
              u64 u6 = load64_le(b21);
              u64 u21 = u6;
              u64 u7 = load64_le(b31);
              u64 u31 = u7;
              r11[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u01, u11, u21, u31);
              {
                u32 nb1 = (u32)8U;
                u8 *b02 = d + s8 * nb1;
                u8 *b12 = d + s10 * nb1;
                u8 *b22 = d + s12 * nb1;
                u8 *b32 = d + s14 * nb1;
                u64 u8 = load64_le(b02);
                u64 u02 = u8;
                u64 u9 = load64_le(b12);
                u64 u12 = u9;
                u64 u13 = load64_le(b22);
                u64 u22 = u13;
                u64 u14 = load64_le(b32);
                u64 u32 = u14;
                r21[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u02, u12, u22, u32);
                {
                  u32 nb2 = (u32)8U;
                  u8 *b0 = d + s9 * nb2;
                  u8 *b1 = d + s11 * nb2;
                  u8 *b2 = d + s13 * nb2;
                  u8 *b3 = d + s15 * nb2;
                  u64 u15 = load64_le(b0);
                  u64 u03 = u15;
                  u64 u16 = load64_le(b1);
                  u64 u17 = u16;
                  u64 u18 = load64_le(b2);
                  u64 u23 = u18;
                  u64 u = load64_le(b3);
                  u64 u33 = u;
                  r31[0U] = Lib_IntVector_Intrinsics_vec256_load64s(u03, u17, u23, u33);
                  {
                    Lib_IntVector_Intrinsics_vec256 *x = m_st + (u32)0U * (u32)1U;
                    Lib_IntVector_Intrinsics_vec256 *y = m_st + (u32)1U * (u32)1U;
                    Lib_IntVector_Intrinsics_vec256 *z = m_st + (u32)2U * (u32)1U;
                    Lib_IntVector_Intrinsics_vec256 *w = m_st + (u32)3U * (u32)1U;
                    u32 a = (u32)0U;
                    u32 b4 = (u32)1U;
                    u32 c0 = (u32)2U;
                    u32 d10 = (u32)3U;
                    u32 r02 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
                    u32 r12 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
                    u32 r22 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
                    u32 r32 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
                    Lib_IntVector_Intrinsics_vec256 zz0 = Lib_IntVector_Intrinsics_vec256_zero;
                    Lib_IntVector_Intrinsics_vec256 *wv_a0 = wv + a * (u32)1U;
                    Lib_IntVector_Intrinsics_vec256 *wv_b0 = wv + b4 * (u32)1U;
                    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], wv_b0[0U]);
                    wv_a0[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a0[0U], x[0U]);
                    {
                      Lib_IntVector_Intrinsics_vec256 *wv_a1 = wv + d10 * (u32)1U;
                      Lib_IntVector_Intrinsics_vec256 *wv_b1 = wv + a * (u32)1U;
                      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a1[0U], wv_b1[0U]);
                      wv_a1[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a1[0U], r02);
                      {
                        Lib_IntVector_Intrinsics_vec256 *wv_a2 = wv + c0 * (u32)1U;
                        Lib_IntVector_Intrinsics_vec256 *wv_b2 = wv + d10 * (u32)1U;
                        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], wv_b2[0U]);
                        wv_a2[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a2[0U], zz0);
                        {
                          Lib_IntVector_Intrinsics_vec256 *wv_a3 = wv + b4 * (u32)1U;
                          Lib_IntVector_Intrinsics_vec256 *wv_b3 = wv + c0 * (u32)1U;
                          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a3[0U], wv_b3[0U]);
                          wv_a3[0U] = Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a3[0U], r12);
                          {
                            Lib_IntVector_Intrinsics_vec256 *wv_a4 = wv + a * (u32)1U;
                            Lib_IntVector_Intrinsics_vec256 *wv_b4 = wv + b4 * (u32)1U;
                            wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], wv_b4[0U]);
                            wv_a4[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a4[0U], y[0U]);
                            {
                              Lib_IntVector_Intrinsics_vec256 *wv_a5 = wv + d10 * (u32)1U;
                              Lib_IntVector_Intrinsics_vec256 *wv_b5 = wv + a * (u32)1U;
                              wv_a5[0U] = Lib_IntVector_Intrinsics_vec256_xor(wv_a5[0U], wv_b5[0U]);
                              wv_a5[0U] =
                                Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a5[0U],
                                  r22);
                              {
                                Lib_IntVector_Intrinsics_vec256 *wv_a6 = wv + c0 * (u32)1U;
                                Lib_IntVector_Intrinsics_vec256 *wv_b6 = wv + d10 * (u32)1U;
                                wv_a6[0U] =
                                  Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U],
                                    wv_b6[0U]);
                                wv_a6[0U] = Lib_IntVector_Intrinsics_vec256_add64(wv_a6[0U], zz0);
                                {
                                  Lib_IntVector_Intrinsics_vec256 *wv_a7 = wv + b4 * (u32)1U;
                                  Lib_IntVector_Intrinsics_vec256 *wv_b7 = wv + c0 * (u32)1U;
                                  wv_a7[0U] =
                                    Lib_IntVector_Intrinsics_vec256_xor(wv_a7[0U],
                                      wv_b7[0U]);
                                  wv_a7[0U] =
                                    Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a7[0U],
                                      r32);
                                  {
                                    Lib_IntVector_Intrinsics_vec256 *r13 = wv + (u32)1U * (u32)1U;
                                    Lib_IntVector_Intrinsics_vec256 *r23 = wv + (u32)2U * (u32)1U;
                                    Lib_IntVector_Intrinsics_vec256 *r33 = wv + (u32)3U * (u32)1U;
                                    Lib_IntVector_Intrinsics_vec256 v00 = r13[0U];
                                    Lib_IntVector_Intrinsics_vec256
                                    v1 =
                                      Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v00,
                                        (u32)1U);
                                    r13[0U] = v1;
                                    {
                                      Lib_IntVector_Intrinsics_vec256 v01 = r23[0U];
                                      Lib_IntVector_Intrinsics_vec256
                                      v10 =
                                        Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v01,
                                          (u32)2U);
                                      r23[0U] = v10;
                                      {
                                        Lib_IntVector_Intrinsics_vec256 v02 = r33[0U];
                                        Lib_IntVector_Intrinsics_vec256
                                        v11 =
                                          Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v02,
                                            (u32)3U);
                                        r33[0U] = v11;
                                        {
                                          u32 a0 = (u32)0U;
                                          u32 b = (u32)1U;
                                          u32 c = (u32)2U;
                                          u32 d1 = (u32)3U;
                                          u32 r0 = Hacl_Impl_Blake2_Constants_rTable_B[0U];
                                          u32 r1 = Hacl_Impl_Blake2_Constants_rTable_B[1U];
                                          u32 r24 = Hacl_Impl_Blake2_Constants_rTable_B[2U];
                                          u32 r34 = Hacl_Impl_Blake2_Constants_rTable_B[3U];
                                          Lib_IntVector_Intrinsics_vec256
                                          zz = Lib_IntVector_Intrinsics_vec256_zero;
                                          Lib_IntVector_Intrinsics_vec256 *wv_a = wv + a0 * (u32)1U;
                                          Lib_IntVector_Intrinsics_vec256 *wv_b8 = wv + b * (u32)1U;
                                          wv_a[0U] =
                                            Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                              wv_b8[0U]);
                                          wv_a[0U] =
                                            Lib_IntVector_Intrinsics_vec256_add64(wv_a[0U],
                                              z[0U]);
                                          {
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_a8 = wv + d1 * (u32)1U;
                                            Lib_IntVector_Intrinsics_vec256
                                            *wv_b9 = wv + a0 * (u32)1U;
                                            wv_a8[0U] =
                                              Lib_IntVector_Intrinsics_vec256_xor(wv_a8[0U],
                                                wv_b9[0U]);
                                            wv_a8[0U] =
                                              Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a8[0U],
                                                r0);
                                            {
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_a9 = wv + c * (u32)1U;
                                              Lib_IntVector_Intrinsics_vec256
                                              *wv_b10 = wv + d1 * (u32)1U;
                                              wv_a9[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                                  wv_b10[0U]);
                                              wv_a9[0U] =
                                                Lib_IntVector_Intrinsics_vec256_add64(wv_a9[0U],
                                                  zz);
                                              {
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_a10 = wv + b * (u32)1U;
                                                Lib_IntVector_Intrinsics_vec256
                                                *wv_b11 = wv + c * (u32)1U;
                                                wv_a10[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_xor(wv_a10[0U],
                                                    wv_b11[0U]);
                                                wv_a10[0U] =
                                                  Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a10[0U],
                                                    r1);
                                                {
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_a11 = wv + a0 * (u32)1U;
                                                  Lib_IntVector_Intrinsics_vec256
                                                  *wv_b12 = wv + b * (u32)1U;
                                                  wv_a11[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                      wv_b12[0U]);
                                                  wv_a11[0U] =
                                                    Lib_IntVector_Intrinsics_vec256_add64(wv_a11[0U],
                                                      w[0U]);
                                                  {
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_a12 = wv + d1 * (u32)1U;
                                                    Lib_IntVector_Intrinsics_vec256
                                                    *wv_b13 = wv + a0 * (u32)1U;
                                                    wv_a12[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_xor(wv_a12[0U],
                                                        wv_b13[0U]);
                                                    wv_a12[0U] =
                                                      Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a12[0U],
                                                        r24);
                                                    {
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *wv_a13 = wv + c * (u32)1U;
                                                      Lib_IntVector_Intrinsics_vec256
                                                      *wv_b14 = wv + d1 * (u32)1U;
                                                      wv_a13[0U] =
                                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                          wv_b14[0U]);
                                                      wv_a13[0U] =
                                                        Lib_IntVector_Intrinsics_vec256_add64(wv_a13[0U],
                                                          zz);
                                                      {
                                                        Lib_IntVector_Intrinsics_vec256
                                                        *wv_a14 = wv + b * (u32)1U;
                                                        Lib_IntVector_Intrinsics_vec256
                                                        *wv_b = wv + c * (u32)1U;
                                                        wv_a14[0U] =
                                                          Lib_IntVector_Intrinsics_vec256_xor(wv_a14[0U],
                                                            wv_b[0U]);
                                                        wv_a14[0U] =
                                                          Lib_IntVector_Intrinsics_vec256_rotate_right64(wv_a14[0U],
                                                            r34);
                                                        {
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *r14 = wv + (u32)1U * (u32)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *r2 = wv + (u32)2U * (u32)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          *r3 = wv + (u32)3U * (u32)1U;
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v0 = r14[0U];
                                                          Lib_IntVector_Intrinsics_vec256
                                                          v12 =
                                                            Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v0,
                                                              (u32)3U);
                                                          r14[0U] = v12;
                                                          {
                                                            Lib_IntVector_Intrinsics_vec256
                                                            v03 = r2[0U];
                                                            Lib_IntVector_Intrinsics_vec256
                                                            v13 =
                                                              Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v03,
                                                                (u32)2U);
                                                            r2[0U] = v13;
                                                            {
                                                              Lib_IntVector_Intrinsics_vec256
                                                              v04 = r3[0U];
                                                              Lib_IntVector_Intrinsics_vec256
                                                              v14 =
                                                                Lib_IntVector_Intrinsics_vec256_rotate_right_lanes64(v04,
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
        }
      }
    }
    s00 = hash + (u32)0U * (u32)1U;
    s16 = hash + (u32)1U * (u32)1U;
    r00 = wv + (u32)0U * (u32)1U;
    r10 = wv + (u32)1U * (u32)1U;
    r20 = wv + (u32)2U * (u32)1U;
    r30 = wv + (u32)3U * (u32)1U;
    s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r00[0U]);
    s00[0U] = Lib_IntVector_Intrinsics_vec256_xor(s00[0U], r20[0U]);
    s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r10[0U]);
    s16[0U] = Lib_IntVector_Intrinsics_vec256_xor(s16[0U], r30[0U]);
  }
}

void Hacl_Blake2b_256_blake2b(u32 nn, u8 *output, u32 ll, u8 *d, u32 kk, u8 *k)
{
  u32 stlen = (u32)4U * (u32)1U;
  Lib_IntVector_Intrinsics_vec256 stzero = Lib_IntVector_Intrinsics_vec256_zero;
  KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), stlen);
  {
    Lib_IntVector_Intrinsics_vec256 b[stlen];
    {
      u32 _i;
      for (_i = 0U; _i < stlen; ++_i)
        b[_i] = stzero;
    }
    {
      uint128_t prev0;
      if (kk == (u32)0U)
        prev0 = (uint128_t)(u64)(u32)0U;
      else
        prev0 = (uint128_t)(u64)(u32)128U;
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), stlen);
      {
        Lib_IntVector_Intrinsics_vec256 b1[stlen];
        {
          u32 _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        {
          u8 b20[128U] = { 0U };
          Lib_IntVector_Intrinsics_vec256 *r0 = b + (u32)0U * (u32)1U;
          Lib_IntVector_Intrinsics_vec256 *r1 = b + (u32)1U * (u32)1U;
          Lib_IntVector_Intrinsics_vec256 *r2 = b + (u32)2U * (u32)1U;
          Lib_IntVector_Intrinsics_vec256 *r3 = b + (u32)3U * (u32)1U;
          u64 iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
          u64 iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
          u64 iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
          u64 iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
          u64 iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
          u64 iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
          u64 iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
          u64 iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
          u64 kk_shift_8;
          u64 iv0_;
          u32 nb0;
          u32 rem0;
          K___u32_u32 scrut;
          u32 nb;
          u32 rem;
          r2[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0, iv1, iv2, iv3);
          r3[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
          kk_shift_8 = (u64)kk << (u32)8U;
          iv0_ = iv0 ^ ((u64)0x01010000U ^ (kk_shift_8 ^ (u64)nn));
          r0[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv0_, iv1, iv2, iv3);
          r1[0U] = Lib_IntVector_Intrinsics_vec256_load64s(iv4, iv5, iv6, iv7);
          if (!(kk == (u32)0U))
          {
            memcpy(b20, k, kk * sizeof (k[0U]));
            {
              uint128_t totlen = (uint128_t)(u64)(u32)0U + (uint128_t)(u64)(u32)128U;
              u8 *b3 = b20 + (u32)0U * (u32)128U;
              blake2b_update_block(b1, b, false, totlen, b3);
            }
          }
          memset(b20, 0U, (u32)128U * sizeof (b20[0U]));
          nb0 = ll / (u32)128U;
          rem0 = ll % (u32)128U;
          if (rem0 == (u32)0U && nb0 > (u32)0U)
          {
            u32 nb_ = nb0 - (u32)1U;
            u32 rem_ = (u32)128U;
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
              uint128_t totlen = prev0 + (uint128_t)(u64)((i + (u32)1U) * (u32)128U);
              u8 *b2 = d + i * (u32)128U;
              blake2b_update_block(b1, b, false, totlen, b2);
            }
          }
          {
            u8 b21[128U] = { 0U };
            u8 *last = d + ll - rem;
            uint128_t totlen;
            u32 double_row;
            memcpy(b21, last, rem * sizeof (last[0U]));
            totlen = prev0 + (uint128_t)(u64)ll;
            blake2b_update_block(b1, b, true, totlen, b21);
            memset(b21, 0U, (u32)128U * sizeof (b21[0U]));
            double_row = (u32)2U * (u32)4U * (u32)8U;
            KRML_CHECK_SIZE(sizeof (u8), double_row);
            {
              u8 b2[double_row];
              memset(b2, 0U, double_row * sizeof (b2[0U]));
              {
                u8 *first = b2;
                u8 *second = b2 + (u32)4U * (u32)8U;
                Lib_IntVector_Intrinsics_vec256 *row0 = b + (u32)0U * (u32)1U;
                Lib_IntVector_Intrinsics_vec256 *row1 = b + (u32)1U * (u32)1U;
                u8 *final;
                Lib_IntVector_Intrinsics_vec256_store_le(first, row0[0U]);
                Lib_IntVector_Intrinsics_vec256_store_le(second, row1[0U]);
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

