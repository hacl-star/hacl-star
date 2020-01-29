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


#include "Hacl_Blake2s_32.h"

static inline void blake2s_update_block(u32 *hash, bool flag, u64 totlen, u8 *d)
{
  KRML_CHECK_SIZE(sizeof (u32), (u32)4U * (u32)4U);
  {
    u32 b[(u32)4U * (u32)4U];
    memset(b, 0U, (u32)4U * (u32)4U * sizeof (b[0U]));
    {
      u32 mask[4U] = { 0U };
      u32 wv_14;
      if (flag)
        wv_14 = (u32)0xFFFFFFFFU;
      else
        wv_14 = (u32)0U;
      {
        u32 wv_15 = (u32)0U;
        u32 *wv3;
        u32 *s00;
        u32 *s16;
        u32 *r00;
        u32 *r10;
        u32 *r20;
        u32 *r30;
        mask[0U] = (u32)totlen;
        mask[1U] = (u32)(totlen >> (u32)32U);
        mask[2U] = wv_14;
        mask[3U] = wv_15;
        memcpy(b, hash, (u32)4U * (u32)4U * sizeof (hash[0U]));
        wv3 = b + (u32)3U * (u32)4U;
        {
          u32 i;
          for (i = (u32)0U; i < (u32)4U; i++)
          {
            u32 *os = wv3;
            u32 x = wv3[i] ^ mask[i];
            os[i] = x;
          }
        }
        {
          u32 i0;
          for (i0 = (u32)0U; i0 < (u32)10U; i0++)
          {
            u32 start_idx = i0 % (u32)10U * (u32)16U;
            KRML_CHECK_SIZE(sizeof (u32), (u32)4U * (u32)4U);
            {
              u32 m_st[(u32)4U * (u32)4U];
              memset(m_st, 0U, (u32)4U * (u32)4U * sizeof (m_st[0U]));
              {
                u32 *r01 = m_st + (u32)0U * (u32)4U;
                u32 *r12 = m_st + (u32)1U * (u32)4U;
                u32 *r21 = m_st + (u32)2U * (u32)4U;
                u32 *r31 = m_st + (u32)3U * (u32)4U;
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
                r01[0U] = u00;
                r01[1U] = u11;
                r01[2U] = u20;
                r01[3U] = u30;
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
                  r12[0U] = u01;
                  r12[1U] = u110;
                  r12[2U] = u21;
                  r12[3U] = u31;
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
                    r21[0U] = u02;
                    r21[1U] = u111;
                    r21[2U] = u22;
                    r21[3U] = u32;
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
                      r31[0U] = u03;
                      r31[1U] = u112;
                      r31[2U] = u23;
                      r31[3U] = u33;
                      {
                        u32 *x = m_st + (u32)0U * (u32)4U;
                        u32 *y = m_st + (u32)1U * (u32)4U;
                        u32 *z = m_st + (u32)2U * (u32)4U;
                        u32 *w = m_st + (u32)3U * (u32)4U;
                        u32 a = (u32)0U;
                        u32 b14 = (u32)1U;
                        u32 c0 = (u32)2U;
                        u32 d10 = (u32)3U;
                        u32 r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                        u32 r13 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                        u32 r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                        u32 r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                        u32 zz0[4U] = { 0U };
                        u32 *wv_a0 = b + a * (u32)4U;
                        u32 *wv_b0 = b + b14 * (u32)4U;
                        {
                          u32 i;
                          for (i = (u32)0U; i < (u32)4U; i++)
                          {
                            u32 *os = wv_a0;
                            u32 x1 = wv_a0[i] + wv_b0[i];
                            os[i] = x1;
                          }
                        }
                        {
                          u32 i;
                          for (i = (u32)0U; i < (u32)4U; i++)
                          {
                            u32 *os = wv_a0;
                            u32 x1 = wv_a0[i] + x[i];
                            os[i] = x1;
                          }
                        }
                        {
                          u32 *wv_a1 = b + d10 * (u32)4U;
                          u32 *wv_b1 = b + a * (u32)4U;
                          {
                            u32 i;
                            for (i = (u32)0U; i < (u32)4U; i++)
                            {
                              u32 *os = wv_a1;
                              u32 x1 = wv_a1[i] ^ wv_b1[i];
                              os[i] = x1;
                            }
                          }
                          {
                            u32 *r110 = wv_a1;
                            {
                              u32 i;
                              for (i = (u32)0U; i < (u32)4U; i++)
                              {
                                u32 *os = r110;
                                u32 x1 = r110[i];
                                u32 x10 = x1 >> r02 | x1 << ((u32)32U - r02);
                                os[i] = x10;
                              }
                            }
                            {
                              u32 *wv_a2 = b + c0 * (u32)4U;
                              u32 *wv_b2 = b + d10 * (u32)4U;
                              {
                                u32 i;
                                for (i = (u32)0U; i < (u32)4U; i++)
                                {
                                  u32 *os = wv_a2;
                                  u32 x1 = wv_a2[i] + wv_b2[i];
                                  os[i] = x1;
                                }
                              }
                              {
                                u32 i;
                                for (i = (u32)0U; i < (u32)4U; i++)
                                {
                                  u32 *os = wv_a2;
                                  u32 x1 = wv_a2[i] + zz0[i];
                                  os[i] = x1;
                                }
                              }
                              {
                                u32 *wv_a3 = b + b14 * (u32)4U;
                                u32 *wv_b3 = b + c0 * (u32)4U;
                                {
                                  u32 i;
                                  for (i = (u32)0U; i < (u32)4U; i++)
                                  {
                                    u32 *os = wv_a3;
                                    u32 x1 = wv_a3[i] ^ wv_b3[i];
                                    os[i] = x1;
                                  }
                                }
                                {
                                  u32 *r111 = wv_a3;
                                  {
                                    u32 i;
                                    for (i = (u32)0U; i < (u32)4U; i++)
                                    {
                                      u32 *os = r111;
                                      u32 x1 = r111[i];
                                      u32 x10 = x1 >> r13 | x1 << ((u32)32U - r13);
                                      os[i] = x10;
                                    }
                                  }
                                  {
                                    u32 *wv_a4 = b + a * (u32)4U;
                                    u32 *wv_b4 = b + b14 * (u32)4U;
                                    {
                                      u32 i;
                                      for (i = (u32)0U; i < (u32)4U; i++)
                                      {
                                        u32 *os = wv_a4;
                                        u32 x1 = wv_a4[i] + wv_b4[i];
                                        os[i] = x1;
                                      }
                                    }
                                    {
                                      u32 i;
                                      for (i = (u32)0U; i < (u32)4U; i++)
                                      {
                                        u32 *os = wv_a4;
                                        u32 x1 = wv_a4[i] + y[i];
                                        os[i] = x1;
                                      }
                                    }
                                    {
                                      u32 *wv_a5 = b + d10 * (u32)4U;
                                      u32 *wv_b5 = b + a * (u32)4U;
                                      {
                                        u32 i;
                                        for (i = (u32)0U; i < (u32)4U; i++)
                                        {
                                          u32 *os = wv_a5;
                                          u32 x1 = wv_a5[i] ^ wv_b5[i];
                                          os[i] = x1;
                                        }
                                      }
                                      {
                                        u32 *r112 = wv_a5;
                                        {
                                          u32 i;
                                          for (i = (u32)0U; i < (u32)4U; i++)
                                          {
                                            u32 *os = r112;
                                            u32 x1 = r112[i];
                                            u32 x10 = x1 >> r22 | x1 << ((u32)32U - r22);
                                            os[i] = x10;
                                          }
                                        }
                                        {
                                          u32 *wv_a6 = b + c0 * (u32)4U;
                                          u32 *wv_b6 = b + d10 * (u32)4U;
                                          {
                                            u32 i;
                                            for (i = (u32)0U; i < (u32)4U; i++)
                                            {
                                              u32 *os = wv_a6;
                                              u32 x1 = wv_a6[i] + wv_b6[i];
                                              os[i] = x1;
                                            }
                                          }
                                          {
                                            u32 i;
                                            for (i = (u32)0U; i < (u32)4U; i++)
                                            {
                                              u32 *os = wv_a6;
                                              u32 x1 = wv_a6[i] + zz0[i];
                                              os[i] = x1;
                                            }
                                          }
                                          {
                                            u32 *wv_a7 = b + b14 * (u32)4U;
                                            u32 *wv_b7 = b + c0 * (u32)4U;
                                            {
                                              u32 i;
                                              for (i = (u32)0U; i < (u32)4U; i++)
                                              {
                                                u32 *os = wv_a7;
                                                u32 x1 = wv_a7[i] ^ wv_b7[i];
                                                os[i] = x1;
                                              }
                                            }
                                            {
                                              u32 *r113 = wv_a7;
                                              {
                                                u32 i;
                                                for (i = (u32)0U; i < (u32)4U; i++)
                                                {
                                                  u32 *os = r113;
                                                  u32 x1 = r113[i];
                                                  u32 x10 = x1 >> r32 | x1 << ((u32)32U - r32);
                                                  os[i] = x10;
                                                }
                                              }
                                              {
                                                u32 *r14 = b + (u32)1U * (u32)4U;
                                                u32 *r23 = b + (u32)2U * (u32)4U;
                                                u32 *r33 = b + (u32)3U * (u32)4U;
                                                u32 n00 = (u32)1U;
                                                u32 n10 = ((u32)1U + (u32)1U) % (u32)4U;
                                                u32 n20 = ((u32)1U + (u32)2U) % (u32)4U;
                                                u32 n30 = ((u32)1U + (u32)3U) % (u32)4U;
                                                u32 *r114 = r14;
                                                u32 x00 = r114[n00];
                                                u32 x10 = r114[n10];
                                                u32 x20 = r114[n20];
                                                u32 x30 = r114[n30];
                                                r114[0U] = x00;
                                                r114[1U] = x10;
                                                r114[2U] = x20;
                                                r114[3U] = x30;
                                                {
                                                  u32 n01 = (u32)2U;
                                                  u32 n11 = ((u32)2U + (u32)1U) % (u32)4U;
                                                  u32 n21 = ((u32)2U + (u32)2U) % (u32)4U;
                                                  u32 n31 = ((u32)2U + (u32)3U) % (u32)4U;
                                                  u32 *r115 = r23;
                                                  u32 x01 = r115[n01];
                                                  u32 x11 = r115[n11];
                                                  u32 x21 = r115[n21];
                                                  u32 x31 = r115[n31];
                                                  r115[0U] = x01;
                                                  r115[1U] = x11;
                                                  r115[2U] = x21;
                                                  r115[3U] = x31;
                                                  {
                                                    u32 n02 = (u32)3U;
                                                    u32 n12 = ((u32)3U + (u32)1U) % (u32)4U;
                                                    u32 n22 = ((u32)3U + (u32)2U) % (u32)4U;
                                                    u32 n32 = ((u32)3U + (u32)3U) % (u32)4U;
                                                    u32 *r116 = r33;
                                                    u32 x02 = r116[n02];
                                                    u32 x12 = r116[n12];
                                                    u32 x22 = r116[n22];
                                                    u32 x32 = r116[n32];
                                                    r116[0U] = x02;
                                                    r116[1U] = x12;
                                                    r116[2U] = x22;
                                                    r116[3U] = x32;
                                                    {
                                                      u32 a0 = (u32)0U;
                                                      u32 b1 = (u32)1U;
                                                      u32 c = (u32)2U;
                                                      u32 d1 = (u32)3U;
                                                      u32
                                                      r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                      u32
                                                      r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                      u32
                                                      r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                      u32
                                                      r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                      u32 zz[4U] = { 0U };
                                                      u32 *wv_a = b + a0 * (u32)4U;
                                                      u32 *wv_b8 = b + b1 * (u32)4U;
                                                      {
                                                        u32 i;
                                                        for (i = (u32)0U; i < (u32)4U; i++)
                                                        {
                                                          u32 *os = wv_a;
                                                          u32 x1 = wv_a[i] + wv_b8[i];
                                                          os[i] = x1;
                                                        }
                                                      }
                                                      {
                                                        u32 i;
                                                        for (i = (u32)0U; i < (u32)4U; i++)
                                                        {
                                                          u32 *os = wv_a;
                                                          u32 x1 = wv_a[i] + z[i];
                                                          os[i] = x1;
                                                        }
                                                      }
                                                      {
                                                        u32 *wv_a8 = b + d1 * (u32)4U;
                                                        u32 *wv_b9 = b + a0 * (u32)4U;
                                                        {
                                                          u32 i;
                                                          for (i = (u32)0U; i < (u32)4U; i++)
                                                          {
                                                            u32 *os = wv_a8;
                                                            u32 x1 = wv_a8[i] ^ wv_b9[i];
                                                            os[i] = x1;
                                                          }
                                                        }
                                                        {
                                                          u32 *r117 = wv_a8;
                                                          {
                                                            u32 i;
                                                            for (i = (u32)0U; i < (u32)4U; i++)
                                                            {
                                                              u32 *os = r117;
                                                              u32 x1 = r117[i];
                                                              u32
                                                              x13 = x1 >> r0 | x1 << ((u32)32U - r0);
                                                              os[i] = x13;
                                                            }
                                                          }
                                                          {
                                                            u32 *wv_a9 = b + c * (u32)4U;
                                                            u32 *wv_b10 = b + d1 * (u32)4U;
                                                            {
                                                              u32 i;
                                                              for (i = (u32)0U; i < (u32)4U; i++)
                                                              {
                                                                u32 *os = wv_a9;
                                                                u32 x1 = wv_a9[i] + wv_b10[i];
                                                                os[i] = x1;
                                                              }
                                                            }
                                                            {
                                                              u32 i;
                                                              for (i = (u32)0U; i < (u32)4U; i++)
                                                              {
                                                                u32 *os = wv_a9;
                                                                u32 x1 = wv_a9[i] + zz[i];
                                                                os[i] = x1;
                                                              }
                                                            }
                                                            {
                                                              u32 *wv_a10 = b + b1 * (u32)4U;
                                                              u32 *wv_b11 = b + c * (u32)4U;
                                                              {
                                                                u32 i;
                                                                for (i = (u32)0U; i < (u32)4U; i++)
                                                                {
                                                                  u32 *os = wv_a10;
                                                                  u32 x1 = wv_a10[i] ^ wv_b11[i];
                                                                  os[i] = x1;
                                                                }
                                                              }
                                                              {
                                                                u32 *r118 = wv_a10;
                                                                {
                                                                  u32 i;
                                                                  for
                                                                  (i
                                                                    = (u32)0U;
                                                                    i
                                                                    < (u32)4U;
                                                                    i++)
                                                                  {
                                                                    u32 *os = r118;
                                                                    u32 x1 = r118[i];
                                                                    u32
                                                                    x13 =
                                                                      x1
                                                                      >> r1
                                                                      | x1 << ((u32)32U - r1);
                                                                    os[i] = x13;
                                                                  }
                                                                }
                                                                {
                                                                  u32 *wv_a11 = b + a0 * (u32)4U;
                                                                  u32 *wv_b12 = b + b1 * (u32)4U;
                                                                  {
                                                                    u32 i;
                                                                    for
                                                                    (i
                                                                      = (u32)0U;
                                                                      i
                                                                      < (u32)4U;
                                                                      i++)
                                                                    {
                                                                      u32 *os = wv_a11;
                                                                      u32
                                                                      x1 = wv_a11[i] + wv_b12[i];
                                                                      os[i] = x1;
                                                                    }
                                                                  }
                                                                  {
                                                                    u32 i;
                                                                    for
                                                                    (i
                                                                      = (u32)0U;
                                                                      i
                                                                      < (u32)4U;
                                                                      i++)
                                                                    {
                                                                      u32 *os = wv_a11;
                                                                      u32 x1 = wv_a11[i] + w[i];
                                                                      os[i] = x1;
                                                                    }
                                                                  }
                                                                  {
                                                                    u32 *wv_a12 = b + d1 * (u32)4U;
                                                                    u32 *wv_b13 = b + a0 * (u32)4U;
                                                                    {
                                                                      u32 i;
                                                                      for
                                                                      (i
                                                                        = (u32)0U;
                                                                        i
                                                                        < (u32)4U;
                                                                        i++)
                                                                      {
                                                                        u32 *os = wv_a12;
                                                                        u32
                                                                        x1 = wv_a12[i] ^ wv_b13[i];
                                                                        os[i] = x1;
                                                                      }
                                                                    }
                                                                    {
                                                                      u32 *r119 = wv_a12;
                                                                      {
                                                                        u32 i;
                                                                        for
                                                                        (i
                                                                          = (u32)0U;
                                                                          i
                                                                          < (u32)4U;
                                                                          i++)
                                                                        {
                                                                          u32 *os = r119;
                                                                          u32 x1 = r119[i];
                                                                          u32
                                                                          x13 =
                                                                            x1
                                                                            >> r24
                                                                            | x1 << ((u32)32U - r24);
                                                                          os[i] = x13;
                                                                        }
                                                                      }
                                                                      {
                                                                        u32
                                                                        *wv_a13 = b + c * (u32)4U;
                                                                        u32
                                                                        *wv_b14 = b + d1 * (u32)4U;
                                                                        {
                                                                          u32 i;
                                                                          for
                                                                          (i
                                                                            = (u32)0U;
                                                                            i
                                                                            < (u32)4U;
                                                                            i++)
                                                                          {
                                                                            u32 *os = wv_a13;
                                                                            u32
                                                                            x1 =
                                                                              wv_a13[i]
                                                                              + wv_b14[i];
                                                                            os[i] = x1;
                                                                          }
                                                                        }
                                                                        {
                                                                          u32 i;
                                                                          for
                                                                          (i
                                                                            = (u32)0U;
                                                                            i
                                                                            < (u32)4U;
                                                                            i++)
                                                                          {
                                                                            u32 *os = wv_a13;
                                                                            u32
                                                                            x1 = wv_a13[i] + zz[i];
                                                                            os[i] = x1;
                                                                          }
                                                                        }
                                                                        {
                                                                          u32
                                                                          *wv_a14 = b + b1 * (u32)4U;
                                                                          u32
                                                                          *wv_b = b + c * (u32)4U;
                                                                          {
                                                                            u32 i;
                                                                            for
                                                                            (i
                                                                              = (u32)0U;
                                                                              i
                                                                              < (u32)4U;
                                                                              i++)
                                                                            {
                                                                              u32 *os = wv_a14;
                                                                              u32
                                                                              x1 =
                                                                                wv_a14[i]
                                                                                ^ wv_b[i];
                                                                              os[i] = x1;
                                                                            }
                                                                          }
                                                                          {
                                                                            u32 *r1110 = wv_a14;
                                                                            {
                                                                              u32 i;
                                                                              for
                                                                              (i
                                                                                = (u32)0U;
                                                                                i
                                                                                < (u32)4U;
                                                                                i++)
                                                                              {
                                                                                u32 *os = r1110;
                                                                                u32 x1 = r1110[i];
                                                                                u32
                                                                                x13 =
                                                                                  x1
                                                                                  >> r34
                                                                                  |
                                                                                    x1
                                                                                    <<
                                                                                      ((u32)32U
                                                                                      - r34);
                                                                                os[i] = x13;
                                                                              }
                                                                            }
                                                                            {
                                                                              u32
                                                                              *r15 =
                                                                                b
                                                                                + (u32)1U * (u32)4U;
                                                                              u32
                                                                              *r2 =
                                                                                b
                                                                                + (u32)2U * (u32)4U;
                                                                              u32
                                                                              *r3 =
                                                                                b
                                                                                + (u32)3U * (u32)4U;
                                                                              u32 n0 = (u32)3U;
                                                                              u32
                                                                              n13 =
                                                                                ((u32)3U + (u32)1U)
                                                                                % (u32)4U;
                                                                              u32
                                                                              n23 =
                                                                                ((u32)3U + (u32)2U)
                                                                                % (u32)4U;
                                                                              u32
                                                                              n33 =
                                                                                ((u32)3U + (u32)3U)
                                                                                % (u32)4U;
                                                                              u32 *r1111 = r15;
                                                                              u32 x03 = r1111[n0];
                                                                              u32 x13 = r1111[n13];
                                                                              u32 x23 = r1111[n23];
                                                                              u32 x33 = r1111[n33];
                                                                              r1111[0U] = x03;
                                                                              r1111[1U] = x13;
                                                                              r1111[2U] = x23;
                                                                              r1111[3U] = x33;
                                                                              {
                                                                                u32 n03 = (u32)2U;
                                                                                u32
                                                                                n14 =
                                                                                  ((u32)2U
                                                                                  + (u32)1U)
                                                                                  % (u32)4U;
                                                                                u32
                                                                                n24 =
                                                                                  ((u32)2U
                                                                                  + (u32)2U)
                                                                                  % (u32)4U;
                                                                                u32
                                                                                n34 =
                                                                                  ((u32)2U
                                                                                  + (u32)3U)
                                                                                  % (u32)4U;
                                                                                u32 *r1112 = r2;
                                                                                u32
                                                                                x04 = r1112[n03];
                                                                                u32
                                                                                x14 = r1112[n14];
                                                                                u32
                                                                                x24 = r1112[n24];
                                                                                u32
                                                                                x34 = r1112[n34];
                                                                                r1112[0U] = x04;
                                                                                r1112[1U] = x14;
                                                                                r1112[2U] = x24;
                                                                                r1112[3U] = x34;
                                                                                {
                                                                                  u32 n04 = (u32)1U;
                                                                                  u32
                                                                                  n1 =
                                                                                    ((u32)1U
                                                                                    + (u32)1U)
                                                                                    % (u32)4U;
                                                                                  u32
                                                                                  n2 =
                                                                                    ((u32)1U
                                                                                    + (u32)2U)
                                                                                    % (u32)4U;
                                                                                  u32
                                                                                  n3 =
                                                                                    ((u32)1U
                                                                                    + (u32)3U)
                                                                                    % (u32)4U;
                                                                                  u32 *r11 = r3;
                                                                                  u32 x0 = r11[n04];
                                                                                  u32 x1 = r11[n1];
                                                                                  u32 x2 = r11[n2];
                                                                                  u32 x3 = r11[n3];
                                                                                  r11[0U] = x0;
                                                                                  r11[1U] = x1;
                                                                                  r11[2U] = x2;
                                                                                  r11[3U] = x3;
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        s00 = hash + (u32)0U * (u32)4U;
        s16 = hash + (u32)1U * (u32)4U;
        r00 = b + (u32)0U * (u32)4U;
        r10 = b + (u32)1U * (u32)4U;
        r20 = b + (u32)2U * (u32)4U;
        r30 = b + (u32)3U * (u32)4U;
        {
          u32 i;
          for (i = (u32)0U; i < (u32)4U; i++)
          {
            u32 *os = s00;
            u32 x = s00[i] ^ r00[i];
            os[i] = x;
          }
        }
        {
          u32 i;
          for (i = (u32)0U; i < (u32)4U; i++)
          {
            u32 *os = s00;
            u32 x = s00[i] ^ r20[i];
            os[i] = x;
          }
        }
        {
          u32 i;
          for (i = (u32)0U; i < (u32)4U; i++)
          {
            u32 *os = s16;
            u32 x = s16[i] ^ r10[i];
            os[i] = x;
          }
        }
        {
          u32 i;
          for (i = (u32)0U; i < (u32)4U; i++)
          {
            u32 *os = s16;
            u32 x = s16[i] ^ r30[i];
            os[i] = x;
          }
        }
        memset(b, 0U, (u32)4U * (u32)4U * sizeof (b[0U]));
      }
    }
  }
}

void Hacl_Blake2s_32_blake2s(u32 nn, u8 *output, u32 ll, u8 *d, u32 kk, u8 *k)
{
  KRML_CHECK_SIZE(sizeof (u32), (u32)4U * (u32)4U);
  {
    u32 h[(u32)4U * (u32)4U];
    memset(h, 0U, (u32)4U * (u32)4U * sizeof (h[0U]));
    {
      u64 prev0;
      if (kk == (u32)0U)
        prev0 = (u64)(u32)0U;
      else
        prev0 = (u64)(u32)64U;
      {
        u8 b0[64U] = { 0U };
        u32 *r0 = h + (u32)0U * (u32)4U;
        u32 *r1 = h + (u32)1U * (u32)4U;
        u32 *r2 = h + (u32)2U * (u32)4U;
        u32 *r3 = h + (u32)3U * (u32)4U;
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
        r2[0U] = iv0;
        r2[1U] = iv1;
        r2[2U] = iv2;
        r2[3U] = iv3;
        r3[0U] = iv4;
        r3[1U] = iv5;
        r3[2U] = iv6;
        r3[3U] = iv7;
        kk_shift_8 = kk << (u32)8U;
        iv0_ = iv0 ^ ((u32)0x01010000U ^ (kk_shift_8 ^ nn));
        r0[0U] = iv0_;
        r0[1U] = iv1;
        r0[2U] = iv2;
        r0[3U] = iv3;
        r1[0U] = iv4;
        r1[1U] = iv5;
        r1[2U] = iv6;
        r1[3U] = iv7;
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
              u8 *uu____0 = b;
              u32 *uu____1 = h + (u32)0U * (u32)4U;
              u8 *uu____2;
              u32 *uu____3;
              u8 *final;
              {
                u32 i;
                for (i = (u32)0U; i < (u32)4U; i++)
                  store32_le(uu____0 + i * (u32)4U, uu____1[i]);
              }
              uu____2 = b + (u32)4U * (u32)4U;
              uu____3 = h + (u32)1U * (u32)4U;
              {
                u32 i;
                for (i = (u32)0U; i < (u32)4U; i++)
                  store32_le(uu____2 + i * (u32)4U, uu____3[i]);
              }
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

