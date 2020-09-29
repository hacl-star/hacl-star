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

static inline void blake2s_update_block(u32 *wv, u32 *hash, bool flag, u64 totlen, u8 *d)
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
      memcpy(wv, hash, (u32)4U * (u32)4U * sizeof (u32));
      wv3 = wv + (u32)3U * (u32)4U;
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
            memset(m_st, 0U, (u32)4U * (u32)4U * sizeof (u32));
            {
              u32 *r0 = m_st + (u32)0U * (u32)4U;
              u32 *r1 = m_st + (u32)1U * (u32)4U;
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
              u32 uu____0 = m_w[s2];
              u32 uu____1 = m_w[s4];
              u32 uu____2 = m_w[s6];
              r0[0U] = m_w[s0];
              r0[1U] = uu____0;
              r0[2U] = uu____1;
              r0[3U] = uu____2;
              {
                u32 uu____3 = m_w[s3];
                u32 uu____4 = m_w[s5];
                u32 uu____5 = m_w[s7];
                r1[0U] = m_w[s1];
                r1[1U] = uu____3;
                r1[2U] = uu____4;
                r1[3U] = uu____5;
                {
                  u32 uu____6 = m_w[s10];
                  u32 uu____7 = m_w[s12];
                  u32 uu____8 = m_w[s14];
                  r21[0U] = m_w[s8];
                  r21[1U] = uu____6;
                  r21[2U] = uu____7;
                  r21[3U] = uu____8;
                  {
                    u32 uu____9 = m_w[s11];
                    u32 uu____10 = m_w[s13];
                    u32 uu____11 = m_w[s15];
                    r31[0U] = m_w[s9];
                    r31[1U] = uu____9;
                    r31[2U] = uu____10;
                    r31[3U] = uu____11;
                    {
                      u32 *x = m_st + (u32)0U * (u32)4U;
                      u32 *y = m_st + (u32)1U * (u32)4U;
                      u32 *z = m_st + (u32)2U * (u32)4U;
                      u32 *w = m_st + (u32)3U * (u32)4U;
                      u32 a = (u32)0U;
                      u32 b0 = (u32)1U;
                      u32 c0 = (u32)2U;
                      u32 d10 = (u32)3U;
                      u32 *wv_a0 = wv + a * (u32)4U;
                      u32 *wv_b0 = wv + b0 * (u32)4U;
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
                        u32 *wv_a1 = wv + d10 * (u32)4U;
                        u32 *wv_b1 = wv + a * (u32)4U;
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
                          u32 *r12 = wv_a1;
                          {
                            u32 i;
                            for (i = (u32)0U; i < (u32)4U; i++)
                            {
                              u32 *os = r12;
                              u32 x1 = r12[i];
                              u32 x10 = x1 >> (u32)16U | x1 << (u32)16U;
                              os[i] = x10;
                            }
                          }
                          {
                            u32 *wv_a2 = wv + c0 * (u32)4U;
                            u32 *wv_b2 = wv + d10 * (u32)4U;
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
                              u32 *wv_a3 = wv + b0 * (u32)4U;
                              u32 *wv_b3 = wv + c0 * (u32)4U;
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
                                u32 *r13 = wv_a3;
                                {
                                  u32 i;
                                  for (i = (u32)0U; i < (u32)4U; i++)
                                  {
                                    u32 *os = r13;
                                    u32 x1 = r13[i];
                                    u32 x10 = x1 >> (u32)12U | x1 << (u32)20U;
                                    os[i] = x10;
                                  }
                                }
                                {
                                  u32 *wv_a4 = wv + a * (u32)4U;
                                  u32 *wv_b4 = wv + b0 * (u32)4U;
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
                                    u32 *wv_a5 = wv + d10 * (u32)4U;
                                    u32 *wv_b5 = wv + a * (u32)4U;
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
                                      u32 *r14 = wv_a5;
                                      {
                                        u32 i;
                                        for (i = (u32)0U; i < (u32)4U; i++)
                                        {
                                          u32 *os = r14;
                                          u32 x1 = r14[i];
                                          u32 x10 = x1 >> (u32)8U | x1 << (u32)24U;
                                          os[i] = x10;
                                        }
                                      }
                                      {
                                        u32 *wv_a6 = wv + c0 * (u32)4U;
                                        u32 *wv_b6 = wv + d10 * (u32)4U;
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
                                          u32 *wv_a7 = wv + b0 * (u32)4U;
                                          u32 *wv_b7 = wv + c0 * (u32)4U;
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
                                            u32 *r15 = wv_a7;
                                            {
                                              u32 i;
                                              for (i = (u32)0U; i < (u32)4U; i++)
                                              {
                                                u32 *os = r15;
                                                u32 x1 = r15[i];
                                                u32 x10 = x1 >> (u32)7U | x1 << (u32)25U;
                                                os[i] = x10;
                                              }
                                            }
                                            {
                                              u32 *r16 = wv + (u32)1U * (u32)4U;
                                              u32 *r22 = wv + (u32)2U * (u32)4U;
                                              u32 *r32 = wv + (u32)3U * (u32)4U;
                                              u32 *r110 = r16;
                                              u32 x00 = r110[1U];
                                              u32 x10 = r110[((u32)1U + (u32)1U) % (u32)4U];
                                              u32 x20 = r110[((u32)1U + (u32)2U) % (u32)4U];
                                              u32 x30 = r110[((u32)1U + (u32)3U) % (u32)4U];
                                              r110[0U] = x00;
                                              r110[1U] = x10;
                                              r110[2U] = x20;
                                              r110[3U] = x30;
                                              {
                                                u32 *r111 = r22;
                                                u32 x01 = r111[2U];
                                                u32 x11 = r111[((u32)2U + (u32)1U) % (u32)4U];
                                                u32 x21 = r111[((u32)2U + (u32)2U) % (u32)4U];
                                                u32 x31 = r111[((u32)2U + (u32)3U) % (u32)4U];
                                                r111[0U] = x01;
                                                r111[1U] = x11;
                                                r111[2U] = x21;
                                                r111[3U] = x31;
                                                {
                                                  u32 *r112 = r32;
                                                  u32 x02 = r112[3U];
                                                  u32 x12 = r112[((u32)3U + (u32)1U) % (u32)4U];
                                                  u32 x22 = r112[((u32)3U + (u32)2U) % (u32)4U];
                                                  u32 x32 = r112[((u32)3U + (u32)3U) % (u32)4U];
                                                  r112[0U] = x02;
                                                  r112[1U] = x12;
                                                  r112[2U] = x22;
                                                  r112[3U] = x32;
                                                  {
                                                    u32 a0 = (u32)0U;
                                                    u32 b = (u32)1U;
                                                    u32 c = (u32)2U;
                                                    u32 d1 = (u32)3U;
                                                    u32 *wv_a = wv + a0 * (u32)4U;
                                                    u32 *wv_b8 = wv + b * (u32)4U;
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
                                                      u32 *wv_a8 = wv + d1 * (u32)4U;
                                                      u32 *wv_b9 = wv + a0 * (u32)4U;
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
                                                        u32 *r17 = wv_a8;
                                                        {
                                                          u32 i;
                                                          for (i = (u32)0U; i < (u32)4U; i++)
                                                          {
                                                            u32 *os = r17;
                                                            u32 x1 = r17[i];
                                                            u32
                                                            x13 = x1 >> (u32)16U | x1 << (u32)16U;
                                                            os[i] = x13;
                                                          }
                                                        }
                                                        {
                                                          u32 *wv_a9 = wv + c * (u32)4U;
                                                          u32 *wv_b10 = wv + d1 * (u32)4U;
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
                                                            u32 *wv_a10 = wv + b * (u32)4U;
                                                            u32 *wv_b11 = wv + c * (u32)4U;
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
                                                              u32 *r18 = wv_a10;
                                                              {
                                                                u32 i;
                                                                for (i = (u32)0U; i < (u32)4U; i++)
                                                                {
                                                                  u32 *os = r18;
                                                                  u32 x1 = r18[i];
                                                                  u32
                                                                  x13 =
                                                                    x1
                                                                    >> (u32)12U
                                                                    | x1 << (u32)20U;
                                                                  os[i] = x13;
                                                                }
                                                              }
                                                              {
                                                                u32 *wv_a11 = wv + a0 * (u32)4U;
                                                                u32 *wv_b12 = wv + b * (u32)4U;
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
                                                                    u32 x1 = wv_a11[i] + wv_b12[i];
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
                                                                  u32 *wv_a12 = wv + d1 * (u32)4U;
                                                                  u32 *wv_b13 = wv + a0 * (u32)4U;
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
                                                                    u32 *r19 = wv_a12;
                                                                    {
                                                                      u32 i;
                                                                      for
                                                                      (i
                                                                        = (u32)0U;
                                                                        i
                                                                        < (u32)4U;
                                                                        i++)
                                                                      {
                                                                        u32 *os = r19;
                                                                        u32 x1 = r19[i];
                                                                        u32
                                                                        x13 =
                                                                          x1
                                                                          >> (u32)8U
                                                                          | x1 << (u32)24U;
                                                                        os[i] = x13;
                                                                      }
                                                                    }
                                                                    {
                                                                      u32
                                                                      *wv_a13 = wv + c * (u32)4U;
                                                                      u32
                                                                      *wv_b14 = wv + d1 * (u32)4U;
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
                                                                          x1 = wv_a13[i] + wv_b14[i];
                                                                          os[i] = x1;
                                                                        }
                                                                      }
                                                                      {
                                                                        u32
                                                                        *wv_a14 = wv + b * (u32)4U;
                                                                        u32
                                                                        *wv_b = wv + c * (u32)4U;
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
                                                                            x1 = wv_a14[i] ^ wv_b[i];
                                                                            os[i] = x1;
                                                                          }
                                                                        }
                                                                        {
                                                                          u32 *r113 = wv_a14;
                                                                          {
                                                                            u32 i;
                                                                            for
                                                                            (i
                                                                              = (u32)0U;
                                                                              i
                                                                              < (u32)4U;
                                                                              i++)
                                                                            {
                                                                              u32 *os = r113;
                                                                              u32 x1 = r113[i];
                                                                              u32
                                                                              x13 =
                                                                                x1
                                                                                >> (u32)7U
                                                                                | x1 << (u32)25U;
                                                                              os[i] = x13;
                                                                            }
                                                                          }
                                                                          {
                                                                            u32
                                                                            *r114 =
                                                                              wv
                                                                              + (u32)1U * (u32)4U;
                                                                            u32
                                                                            *r2 =
                                                                              wv
                                                                              + (u32)2U * (u32)4U;
                                                                            u32
                                                                            *r3 =
                                                                              wv
                                                                              + (u32)3U * (u32)4U;
                                                                            u32 *r11 = r114;
                                                                            u32 x03 = r11[3U];
                                                                            u32
                                                                            x13 =
                                                                              r11[((u32)3U
                                                                              + (u32)1U)
                                                                              % (u32)4U];
                                                                            u32
                                                                            x23 =
                                                                              r11[((u32)3U
                                                                              + (u32)2U)
                                                                              % (u32)4U];
                                                                            u32
                                                                            x33 =
                                                                              r11[((u32)3U
                                                                              + (u32)3U)
                                                                              % (u32)4U];
                                                                            r11[0U] = x03;
                                                                            r11[1U] = x13;
                                                                            r11[2U] = x23;
                                                                            r11[3U] = x33;
                                                                            {
                                                                              u32 *r115 = r2;
                                                                              u32 x04 = r115[2U];
                                                                              u32
                                                                              x14 =
                                                                                r115[((u32)2U
                                                                                + (u32)1U)
                                                                                % (u32)4U];
                                                                              u32
                                                                              x24 =
                                                                                r115[((u32)2U
                                                                                + (u32)2U)
                                                                                % (u32)4U];
                                                                              u32
                                                                              x34 =
                                                                                r115[((u32)2U
                                                                                + (u32)3U)
                                                                                % (u32)4U];
                                                                              r115[0U] = x04;
                                                                              r115[1U] = x14;
                                                                              r115[2U] = x24;
                                                                              r115[3U] = x34;
                                                                              {
                                                                                u32 *r116 = r3;
                                                                                u32 x0 = r116[1U];
                                                                                u32
                                                                                x1 =
                                                                                  r116[((u32)1U
                                                                                  + (u32)1U)
                                                                                  % (u32)4U];
                                                                                u32
                                                                                x2 =
                                                                                  r116[((u32)1U
                                                                                  + (u32)2U)
                                                                                  % (u32)4U];
                                                                                u32
                                                                                x3 =
                                                                                  r116[((u32)1U
                                                                                  + (u32)3U)
                                                                                  % (u32)4U];
                                                                                r116[0U] = x0;
                                                                                r116[1U] = x1;
                                                                                r116[2U] = x2;
                                                                                r116[3U] = x3;
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
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
      r00 = wv + (u32)0U * (u32)4U;
      r10 = wv + (u32)1U * (u32)4U;
      r20 = wv + (u32)2U * (u32)4U;
      r30 = wv + (u32)3U * (u32)4U;
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
    }
  }
}

inline void Hacl_Blake2s_32_blake2s_init(u32 *wv, u32 *hash, u32 kk, u8 *k, u32 nn)
{
  u8 b[64U] = { 0U };
  u32 *r0 = hash + (u32)0U * (u32)4U;
  u32 *r1 = hash + (u32)1U * (u32)4U;
  u32 *r2 = hash + (u32)2U * (u32)4U;
  u32 *r3 = hash + (u32)3U * (u32)4U;
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
    memcpy(b, k, kk * sizeof (u8));
    {
      u64 totlen = (u64)(u32)0U + (u64)(u32)64U;
      u8 *b1 = b + (u32)0U * (u32)64U;
      blake2s_update_block(wv, hash, false, totlen, b1);
    }
  }
  Lib_Memzero0_memzero(b, (u32)64U * sizeof (b[0U]));
}

inline void
Hacl_Blake2s_32_blake2s_update_multi(u32 len, u32 *wv, u32 *hash, u64 prev, u8 *blocks, u32 nb)
{
  u32 i;
  for (i = (u32)0U; i < nb; i++)
  {
    u64 totlen = prev + (u64)((i + (u32)1U) * (u32)64U);
    u8 *b = blocks + i * (u32)64U;
    blake2s_update_block(wv, hash, false, totlen, b);
  }
}

inline void
Hacl_Blake2s_32_blake2s_update_last(u32 len, u32 *wv, u32 *hash, u64 prev, u32 rem, u8 *d)
{
  u8 b[64U] = { 0U };
  u8 *last = d + len - rem;
  u64 totlen;
  memcpy(b, last, rem * sizeof (u8));
  totlen = prev + (u64)len;
  blake2s_update_block(wv, hash, true, totlen, b);
  Lib_Memzero0_memzero(b, (u32)64U * sizeof (b[0U]));
}

static inline void blake2s_update_blocks(u32 len, u32 *wv, u32 *hash, u64 prev, u8 *blocks)
{
  u32 nb0 = len / (u32)64U;
  u32 rem0 = len % (u32)64U;
  K___u32_u32 scrut;
  if (rem0 == (u32)0U && nb0 > (u32)0U)
  {
    u32 nb_ = nb0 - (u32)1U;
    u32 rem_ = (u32)64U;
    scrut = ((K___u32_u32){ .fst = nb_, .snd = rem_ });
  }
  else
    scrut = ((K___u32_u32){ .fst = nb0, .snd = rem0 });
  {
    u32 nb = scrut.fst;
    u32 rem = scrut.snd;
    Hacl_Blake2s_32_blake2s_update_multi(len, wv, hash, prev, blocks, nb);
    Hacl_Blake2s_32_blake2s_update_last(len, wv, hash, prev, rem, blocks);
  }
}

inline void Hacl_Blake2s_32_blake2s_finish(u32 nn, u8 *output, u32 *hash)
{
  u32 double_row = (u32)2U * (u32)4U * (u32)4U;
  KRML_CHECK_SIZE(sizeof (u8), double_row);
  {
    u8 b[double_row];
    memset(b, 0U, double_row * sizeof (u8));
    {
      u8 *first = b;
      u8 *second = b + (u32)4U * (u32)4U;
      u32 *row0 = hash + (u32)0U * (u32)4U;
      u32 *row1 = hash + (u32)1U * (u32)4U;
      u8 *final;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)4U; i++)
          store32_le(first + i * (u32)4U, row0[i]);
      }
      {
        u32 i;
        for (i = (u32)0U; i < (u32)4U; i++)
          store32_le(second + i * (u32)4U, row1[i]);
      }
      final = b;
      memcpy(output, final, nn * sizeof (u8));
      Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
    }
  }
}

void Hacl_Blake2s_32_blake2s(u32 nn, u8 *output, u32 ll, u8 *d, u32 kk, u8 *k)
{
  u32 stlen = (u32)4U * (u32)4U;
  u32 stzero = (u32)0U;
  KRML_CHECK_SIZE(sizeof (u32), stlen);
  {
    u32 b[stlen];
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
      KRML_CHECK_SIZE(sizeof (u32), stlen);
      {
        u32 b1[stlen];
        {
          u32 _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        Hacl_Blake2s_32_blake2s_init(b1, b, kk, k, nn);
        blake2s_update_blocks(ll, b1, b, prev0, d);
        Hacl_Blake2s_32_blake2s_finish(nn, output, b);
        Lib_Memzero0_memzero(b1, stlen * sizeof (b1[0U]));
        Lib_Memzero0_memzero(b, stlen * sizeof (b[0U]));
      }
    }
  }
}

