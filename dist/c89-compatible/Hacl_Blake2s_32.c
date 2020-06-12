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

static inline void
blake2s_update_block(uint32_t *wv, uint32_t *hash, bool flag, uint64_t totlen, uint8_t *d)
{
  uint32_t mask[4U] = { 0U };
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
    uint32_t *wv3;
    uint32_t *s00;
    uint32_t *s16;
    uint32_t *r00;
    uint32_t *r10;
    uint32_t *r20;
    uint32_t *r30;
    uint32_t i0;
    mask[0U] = (uint32_t)totlen;
    mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(wv, hash, (uint32_t)4U * (uint32_t)4U * sizeof (hash[0U]));
    wv3 = wv + (uint32_t)3U * (uint32_t)4U;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv3;
        uint32_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
    }
    {
      uint32_t i1;
      for (i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
        {
          uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
          memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (m_st[0U]));
          {
            uint32_t *r01 = m_st + (uint32_t)0U * (uint32_t)4U;
            uint32_t *r12 = m_st + (uint32_t)1U * (uint32_t)4U;
            uint32_t *r21 = m_st + (uint32_t)2U * (uint32_t)4U;
            uint32_t *r31 = m_st + (uint32_t)3U * (uint32_t)4U;
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
            uint32_t nb = (uint32_t)4U;
            uint8_t *b00 = d + s0 * nb;
            uint8_t *b10 = d + s2 * nb;
            uint8_t *b20 = d + s4 * nb;
            uint8_t *b30 = d + s6 * nb;
            uint32_t u0 = load32_le(b00);
            uint32_t u00 = u0;
            uint32_t u1 = load32_le(b10);
            uint32_t u11 = u1;
            uint32_t u2 = load32_le(b20);
            uint32_t u20 = u2;
            uint32_t u3 = load32_le(b30);
            uint32_t u30 = u3;
            r01[0U] = u00;
            r01[1U] = u11;
            r01[2U] = u20;
            r01[3U] = u30;
            {
              uint32_t nb0 = (uint32_t)4U;
              uint8_t *b01 = d + s1 * nb0;
              uint8_t *b11 = d + s3 * nb0;
              uint8_t *b21 = d + s5 * nb0;
              uint8_t *b31 = d + s7 * nb0;
              uint32_t u4 = load32_le(b01);
              uint32_t u01 = u4;
              uint32_t u5 = load32_le(b11);
              uint32_t u110 = u5;
              uint32_t u6 = load32_le(b21);
              uint32_t u21 = u6;
              uint32_t u7 = load32_le(b31);
              uint32_t u31 = u7;
              r12[0U] = u01;
              r12[1U] = u110;
              r12[2U] = u21;
              r12[3U] = u31;
              {
                uint32_t nb1 = (uint32_t)4U;
                uint8_t *b02 = d + s8 * nb1;
                uint8_t *b12 = d + s10 * nb1;
                uint8_t *b22 = d + s12 * nb1;
                uint8_t *b32 = d + s14 * nb1;
                uint32_t u8 = load32_le(b02);
                uint32_t u02 = u8;
                uint32_t u9 = load32_le(b12);
                uint32_t u111 = u9;
                uint32_t u10 = load32_le(b22);
                uint32_t u22 = u10;
                uint32_t u12 = load32_le(b32);
                uint32_t u32 = u12;
                r21[0U] = u02;
                r21[1U] = u111;
                r21[2U] = u22;
                r21[3U] = u32;
                {
                  uint32_t nb2 = (uint32_t)4U;
                  uint8_t *b0 = d + s9 * nb2;
                  uint8_t *b1 = d + s11 * nb2;
                  uint8_t *b2 = d + s13 * nb2;
                  uint8_t *b3 = d + s15 * nb2;
                  uint32_t u13 = load32_le(b0);
                  uint32_t u03 = u13;
                  uint32_t u14 = load32_le(b1);
                  uint32_t u112 = u14;
                  uint32_t u15 = load32_le(b2);
                  uint32_t u23 = u15;
                  uint32_t u = load32_le(b3);
                  uint32_t u33 = u;
                  r31[0U] = u03;
                  r31[1U] = u112;
                  r31[2U] = u23;
                  r31[3U] = u33;
                  {
                    uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
                    uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
                    uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
                    uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
                    uint32_t a = (uint32_t)0U;
                    uint32_t b4 = (uint32_t)1U;
                    uint32_t c0 = (uint32_t)2U;
                    uint32_t d10 = (uint32_t)3U;
                    uint32_t r02 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                    uint32_t r13 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                    uint32_t r22 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                    uint32_t r32 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                    uint32_t zz0[4U] = { 0U };
                    uint32_t *wv_a0 = wv + a * (uint32_t)4U;
                    uint32_t *wv_b0 = wv + b4 * (uint32_t)4U;
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                      {
                        uint32_t *os = wv_a0;
                        uint32_t x1 = wv_a0[i] + wv_b0[i];
                        os[i] = x1;
                      }
                    }
                    {
                      uint32_t i;
                      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                      {
                        uint32_t *os = wv_a0;
                        uint32_t x1 = wv_a0[i] + x[i];
                        os[i] = x1;
                      }
                    }
                    {
                      uint32_t *wv_a1 = wv + d10 * (uint32_t)4U;
                      uint32_t *wv_b1 = wv + a * (uint32_t)4U;
                      {
                        uint32_t i;
                        for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                        {
                          uint32_t *os = wv_a1;
                          uint32_t x1 = wv_a1[i] ^ wv_b1[i];
                          os[i] = x1;
                        }
                      }
                      {
                        uint32_t *r110 = wv_a1;
                        {
                          uint32_t i;
                          for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                          {
                            uint32_t *os = r110;
                            uint32_t x1 = r110[i];
                            uint32_t x10 = x1 >> r02 | x1 << ((uint32_t)32U - r02);
                            os[i] = x10;
                          }
                        }
                        {
                          uint32_t *wv_a2 = wv + c0 * (uint32_t)4U;
                          uint32_t *wv_b2 = wv + d10 * (uint32_t)4U;
                          {
                            uint32_t i;
                            for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                            {
                              uint32_t *os = wv_a2;
                              uint32_t x1 = wv_a2[i] + wv_b2[i];
                              os[i] = x1;
                            }
                          }
                          {
                            uint32_t i;
                            for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                            {
                              uint32_t *os = wv_a2;
                              uint32_t x1 = wv_a2[i] + zz0[i];
                              os[i] = x1;
                            }
                          }
                          {
                            uint32_t *wv_a3 = wv + b4 * (uint32_t)4U;
                            uint32_t *wv_b3 = wv + c0 * (uint32_t)4U;
                            {
                              uint32_t i;
                              for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                              {
                                uint32_t *os = wv_a3;
                                uint32_t x1 = wv_a3[i] ^ wv_b3[i];
                                os[i] = x1;
                              }
                            }
                            {
                              uint32_t *r111 = wv_a3;
                              {
                                uint32_t i;
                                for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                {
                                  uint32_t *os = r111;
                                  uint32_t x1 = r111[i];
                                  uint32_t x10 = x1 >> r13 | x1 << ((uint32_t)32U - r13);
                                  os[i] = x10;
                                }
                              }
                              {
                                uint32_t *wv_a4 = wv + a * (uint32_t)4U;
                                uint32_t *wv_b4 = wv + b4 * (uint32_t)4U;
                                {
                                  uint32_t i;
                                  for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                  {
                                    uint32_t *os = wv_a4;
                                    uint32_t x1 = wv_a4[i] + wv_b4[i];
                                    os[i] = x1;
                                  }
                                }
                                {
                                  uint32_t i;
                                  for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                  {
                                    uint32_t *os = wv_a4;
                                    uint32_t x1 = wv_a4[i] + y[i];
                                    os[i] = x1;
                                  }
                                }
                                {
                                  uint32_t *wv_a5 = wv + d10 * (uint32_t)4U;
                                  uint32_t *wv_b5 = wv + a * (uint32_t)4U;
                                  {
                                    uint32_t i;
                                    for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                    {
                                      uint32_t *os = wv_a5;
                                      uint32_t x1 = wv_a5[i] ^ wv_b5[i];
                                      os[i] = x1;
                                    }
                                  }
                                  {
                                    uint32_t *r112 = wv_a5;
                                    {
                                      uint32_t i;
                                      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                      {
                                        uint32_t *os = r112;
                                        uint32_t x1 = r112[i];
                                        uint32_t x10 = x1 >> r22 | x1 << ((uint32_t)32U - r22);
                                        os[i] = x10;
                                      }
                                    }
                                    {
                                      uint32_t *wv_a6 = wv + c0 * (uint32_t)4U;
                                      uint32_t *wv_b6 = wv + d10 * (uint32_t)4U;
                                      {
                                        uint32_t i;
                                        for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                        {
                                          uint32_t *os = wv_a6;
                                          uint32_t x1 = wv_a6[i] + wv_b6[i];
                                          os[i] = x1;
                                        }
                                      }
                                      {
                                        uint32_t i;
                                        for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                        {
                                          uint32_t *os = wv_a6;
                                          uint32_t x1 = wv_a6[i] + zz0[i];
                                          os[i] = x1;
                                        }
                                      }
                                      {
                                        uint32_t *wv_a7 = wv + b4 * (uint32_t)4U;
                                        uint32_t *wv_b7 = wv + c0 * (uint32_t)4U;
                                        {
                                          uint32_t i;
                                          for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                          {
                                            uint32_t *os = wv_a7;
                                            uint32_t x1 = wv_a7[i] ^ wv_b7[i];
                                            os[i] = x1;
                                          }
                                        }
                                        {
                                          uint32_t *r113 = wv_a7;
                                          {
                                            uint32_t i;
                                            for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                            {
                                              uint32_t *os = r113;
                                              uint32_t x1 = r113[i];
                                              uint32_t
                                              x10 = x1 >> r32 | x1 << ((uint32_t)32U - r32);
                                              os[i] = x10;
                                            }
                                          }
                                          {
                                            uint32_t *r14 = wv + (uint32_t)1U * (uint32_t)4U;
                                            uint32_t *r23 = wv + (uint32_t)2U * (uint32_t)4U;
                                            uint32_t *r33 = wv + (uint32_t)3U * (uint32_t)4U;
                                            uint32_t *r114 = r14;
                                            uint32_t x00 = r114[1U];
                                            uint32_t
                                            x10 = r114[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
                                            uint32_t
                                            x20 = r114[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
                                            uint32_t
                                            x30 = r114[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
                                            r114[0U] = x00;
                                            r114[1U] = x10;
                                            r114[2U] = x20;
                                            r114[3U] = x30;
                                            {
                                              uint32_t *r115 = r23;
                                              uint32_t x01 = r115[2U];
                                              uint32_t
                                              x11 =
                                                r115[((uint32_t)2U + (uint32_t)1U)
                                                % (uint32_t)4U];
                                              uint32_t
                                              x21 =
                                                r115[((uint32_t)2U + (uint32_t)2U)
                                                % (uint32_t)4U];
                                              uint32_t
                                              x31 =
                                                r115[((uint32_t)2U + (uint32_t)3U)
                                                % (uint32_t)4U];
                                              r115[0U] = x01;
                                              r115[1U] = x11;
                                              r115[2U] = x21;
                                              r115[3U] = x31;
                                              {
                                                uint32_t *r116 = r33;
                                                uint32_t x02 = r116[3U];
                                                uint32_t
                                                x12 =
                                                  r116[((uint32_t)3U + (uint32_t)1U)
                                                  % (uint32_t)4U];
                                                uint32_t
                                                x22 =
                                                  r116[((uint32_t)3U + (uint32_t)2U)
                                                  % (uint32_t)4U];
                                                uint32_t
                                                x32 =
                                                  r116[((uint32_t)3U + (uint32_t)3U)
                                                  % (uint32_t)4U];
                                                r116[0U] = x02;
                                                r116[1U] = x12;
                                                r116[2U] = x22;
                                                r116[3U] = x32;
                                                {
                                                  uint32_t a0 = (uint32_t)0U;
                                                  uint32_t b = (uint32_t)1U;
                                                  uint32_t c = (uint32_t)2U;
                                                  uint32_t d1 = (uint32_t)3U;
                                                  uint32_t
                                                  r0 = Hacl_Impl_Blake2_Constants_rTable_S[0U];
                                                  uint32_t
                                                  r1 = Hacl_Impl_Blake2_Constants_rTable_S[1U];
                                                  uint32_t
                                                  r24 = Hacl_Impl_Blake2_Constants_rTable_S[2U];
                                                  uint32_t
                                                  r34 = Hacl_Impl_Blake2_Constants_rTable_S[3U];
                                                  uint32_t zz[4U] = { 0U };
                                                  uint32_t *wv_a = wv + a0 * (uint32_t)4U;
                                                  uint32_t *wv_b8 = wv + b * (uint32_t)4U;
                                                  {
                                                    uint32_t i;
                                                    for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                                    {
                                                      uint32_t *os = wv_a;
                                                      uint32_t x1 = wv_a[i] + wv_b8[i];
                                                      os[i] = x1;
                                                    }
                                                  }
                                                  {
                                                    uint32_t i;
                                                    for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                                    {
                                                      uint32_t *os = wv_a;
                                                      uint32_t x1 = wv_a[i] + z[i];
                                                      os[i] = x1;
                                                    }
                                                  }
                                                  {
                                                    uint32_t *wv_a8 = wv + d1 * (uint32_t)4U;
                                                    uint32_t *wv_b9 = wv + a0 * (uint32_t)4U;
                                                    {
                                                      uint32_t i;
                                                      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                                                      {
                                                        uint32_t *os = wv_a8;
                                                        uint32_t x1 = wv_a8[i] ^ wv_b9[i];
                                                        os[i] = x1;
                                                      }
                                                    }
                                                    {
                                                      uint32_t *r117 = wv_a8;
                                                      {
                                                        uint32_t i;
                                                        for
                                                        (i
                                                          = (uint32_t)0U;
                                                          i
                                                          < (uint32_t)4U;
                                                          i++)
                                                        {
                                                          uint32_t *os = r117;
                                                          uint32_t x1 = r117[i];
                                                          uint32_t
                                                          x13 =
                                                            x1
                                                            >> r0
                                                            | x1 << ((uint32_t)32U - r0);
                                                          os[i] = x13;
                                                        }
                                                      }
                                                      {
                                                        uint32_t *wv_a9 = wv + c * (uint32_t)4U;
                                                        uint32_t *wv_b10 = wv + d1 * (uint32_t)4U;
                                                        {
                                                          uint32_t i;
                                                          for
                                                          (i
                                                            = (uint32_t)0U;
                                                            i
                                                            < (uint32_t)4U;
                                                            i++)
                                                          {
                                                            uint32_t *os = wv_a9;
                                                            uint32_t x1 = wv_a9[i] + wv_b10[i];
                                                            os[i] = x1;
                                                          }
                                                        }
                                                        {
                                                          uint32_t i;
                                                          for
                                                          (i
                                                            = (uint32_t)0U;
                                                            i
                                                            < (uint32_t)4U;
                                                            i++)
                                                          {
                                                            uint32_t *os = wv_a9;
                                                            uint32_t x1 = wv_a9[i] + zz[i];
                                                            os[i] = x1;
                                                          }
                                                        }
                                                        {
                                                          uint32_t *wv_a10 = wv + b * (uint32_t)4U;
                                                          uint32_t *wv_b11 = wv + c * (uint32_t)4U;
                                                          {
                                                            uint32_t i;
                                                            for
                                                            (i
                                                              = (uint32_t)0U;
                                                              i
                                                              < (uint32_t)4U;
                                                              i++)
                                                            {
                                                              uint32_t *os = wv_a10;
                                                              uint32_t x1 = wv_a10[i] ^ wv_b11[i];
                                                              os[i] = x1;
                                                            }
                                                          }
                                                          {
                                                            uint32_t *r118 = wv_a10;
                                                            {
                                                              uint32_t i;
                                                              for
                                                              (i
                                                                = (uint32_t)0U;
                                                                i
                                                                < (uint32_t)4U;
                                                                i++)
                                                              {
                                                                uint32_t *os = r118;
                                                                uint32_t x1 = r118[i];
                                                                uint32_t
                                                                x13 =
                                                                  x1
                                                                  >> r1
                                                                  | x1 << ((uint32_t)32U - r1);
                                                                os[i] = x13;
                                                              }
                                                            }
                                                            {
                                                              uint32_t
                                                              *wv_a11 = wv + a0 * (uint32_t)4U;
                                                              uint32_t
                                                              *wv_b12 = wv + b * (uint32_t)4U;
                                                              {
                                                                uint32_t i;
                                                                for
                                                                (i
                                                                  = (uint32_t)0U;
                                                                  i
                                                                  < (uint32_t)4U;
                                                                  i++)
                                                                {
                                                                  uint32_t *os = wv_a11;
                                                                  uint32_t
                                                                  x1 = wv_a11[i] + wv_b12[i];
                                                                  os[i] = x1;
                                                                }
                                                              }
                                                              {
                                                                uint32_t i;
                                                                for
                                                                (i
                                                                  = (uint32_t)0U;
                                                                  i
                                                                  < (uint32_t)4U;
                                                                  i++)
                                                                {
                                                                  uint32_t *os = wv_a11;
                                                                  uint32_t x1 = wv_a11[i] + w[i];
                                                                  os[i] = x1;
                                                                }
                                                              }
                                                              {
                                                                uint32_t
                                                                *wv_a12 = wv + d1 * (uint32_t)4U;
                                                                uint32_t
                                                                *wv_b13 = wv + a0 * (uint32_t)4U;
                                                                {
                                                                  uint32_t i;
                                                                  for
                                                                  (i
                                                                    = (uint32_t)0U;
                                                                    i
                                                                    < (uint32_t)4U;
                                                                    i++)
                                                                  {
                                                                    uint32_t *os = wv_a12;
                                                                    uint32_t
                                                                    x1 = wv_a12[i] ^ wv_b13[i];
                                                                    os[i] = x1;
                                                                  }
                                                                }
                                                                {
                                                                  uint32_t *r119 = wv_a12;
                                                                  {
                                                                    uint32_t i;
                                                                    for
                                                                    (i
                                                                      = (uint32_t)0U;
                                                                      i
                                                                      < (uint32_t)4U;
                                                                      i++)
                                                                    {
                                                                      uint32_t *os = r119;
                                                                      uint32_t x1 = r119[i];
                                                                      uint32_t
                                                                      x13 =
                                                                        x1
                                                                        >> r24
                                                                        |
                                                                          x1
                                                                          << ((uint32_t)32U - r24);
                                                                      os[i] = x13;
                                                                    }
                                                                  }
                                                                  {
                                                                    uint32_t
                                                                    *wv_a13 = wv + c * (uint32_t)4U;
                                                                    uint32_t
                                                                    *wv_b14 = wv + d1 * (uint32_t)4U;
                                                                    {
                                                                      uint32_t i;
                                                                      for
                                                                      (i
                                                                        = (uint32_t)0U;
                                                                        i
                                                                        < (uint32_t)4U;
                                                                        i++)
                                                                      {
                                                                        uint32_t *os = wv_a13;
                                                                        uint32_t
                                                                        x1 = wv_a13[i] + wv_b14[i];
                                                                        os[i] = x1;
                                                                      }
                                                                    }
                                                                    {
                                                                      uint32_t i;
                                                                      for
                                                                      (i
                                                                        = (uint32_t)0U;
                                                                        i
                                                                        < (uint32_t)4U;
                                                                        i++)
                                                                      {
                                                                        uint32_t *os = wv_a13;
                                                                        uint32_t
                                                                        x1 = wv_a13[i] + zz[i];
                                                                        os[i] = x1;
                                                                      }
                                                                    }
                                                                    {
                                                                      uint32_t
                                                                      *wv_a14 =
                                                                        wv
                                                                        + b * (uint32_t)4U;
                                                                      uint32_t
                                                                      *wv_b = wv + c * (uint32_t)4U;
                                                                      {
                                                                        uint32_t i;
                                                                        for
                                                                        (i
                                                                          = (uint32_t)0U;
                                                                          i
                                                                          < (uint32_t)4U;
                                                                          i++)
                                                                        {
                                                                          uint32_t *os = wv_a14;
                                                                          uint32_t
                                                                          x1 = wv_a14[i] ^ wv_b[i];
                                                                          os[i] = x1;
                                                                        }
                                                                      }
                                                                      {
                                                                        uint32_t *r1110 = wv_a14;
                                                                        {
                                                                          uint32_t i;
                                                                          for
                                                                          (i
                                                                            = (uint32_t)0U;
                                                                            i
                                                                            < (uint32_t)4U;
                                                                            i++)
                                                                          {
                                                                            uint32_t *os = r1110;
                                                                            uint32_t x1 = r1110[i];
                                                                            uint32_t
                                                                            x13 =
                                                                              x1
                                                                              >> r34
                                                                              |
                                                                                x1
                                                                                <<
                                                                                  ((uint32_t)32U
                                                                                  - r34);
                                                                            os[i] = x13;
                                                                          }
                                                                        }
                                                                        {
                                                                          uint32_t
                                                                          *r15 =
                                                                            wv
                                                                            +
                                                                              (uint32_t)1U
                                                                              * (uint32_t)4U;
                                                                          uint32_t
                                                                          *r2 =
                                                                            wv
                                                                            +
                                                                              (uint32_t)2U
                                                                              * (uint32_t)4U;
                                                                          uint32_t
                                                                          *r3 =
                                                                            wv
                                                                            +
                                                                              (uint32_t)3U
                                                                              * (uint32_t)4U;
                                                                          uint32_t *r11 = r15;
                                                                          uint32_t x03 = r11[3U];
                                                                          uint32_t
                                                                          x13 =
                                                                            r11[((uint32_t)3U
                                                                            + (uint32_t)1U)
                                                                            % (uint32_t)4U];
                                                                          uint32_t
                                                                          x23 =
                                                                            r11[((uint32_t)3U
                                                                            + (uint32_t)2U)
                                                                            % (uint32_t)4U];
                                                                          uint32_t
                                                                          x33 =
                                                                            r11[((uint32_t)3U
                                                                            + (uint32_t)3U)
                                                                            % (uint32_t)4U];
                                                                          r11[0U] = x03;
                                                                          r11[1U] = x13;
                                                                          r11[2U] = x23;
                                                                          r11[3U] = x33;
                                                                          {
                                                                            uint32_t *r1111 = r2;
                                                                            uint32_t
                                                                            x04 = r1111[2U];
                                                                            uint32_t
                                                                            x14 =
                                                                              r1111[((uint32_t)2U
                                                                              + (uint32_t)1U)
                                                                              % (uint32_t)4U];
                                                                            uint32_t
                                                                            x24 =
                                                                              r1111[((uint32_t)2U
                                                                              + (uint32_t)2U)
                                                                              % (uint32_t)4U];
                                                                            uint32_t
                                                                            x34 =
                                                                              r1111[((uint32_t)2U
                                                                              + (uint32_t)3U)
                                                                              % (uint32_t)4U];
                                                                            r1111[0U] = x04;
                                                                            r1111[1U] = x14;
                                                                            r1111[2U] = x24;
                                                                            r1111[3U] = x34;
                                                                            {
                                                                              uint32_t *r1112 = r3;
                                                                              uint32_t
                                                                              x0 = r1112[1U];
                                                                              uint32_t
                                                                              x1 =
                                                                                r1112[((uint32_t)1U
                                                                                + (uint32_t)1U)
                                                                                % (uint32_t)4U];
                                                                              uint32_t
                                                                              x2 =
                                                                                r1112[((uint32_t)1U
                                                                                + (uint32_t)2U)
                                                                                % (uint32_t)4U];
                                                                              uint32_t
                                                                              x3 =
                                                                                r1112[((uint32_t)1U
                                                                                + (uint32_t)3U)
                                                                                % (uint32_t)4U];
                                                                              r1112[0U] = x0;
                                                                              r1112[1U] = x1;
                                                                              r1112[2U] = x2;
                                                                              r1112[3U] = x3;
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    s00 = hash + (uint32_t)0U * (uint32_t)4U;
    s16 = hash + (uint32_t)1U * (uint32_t)4U;
    r00 = wv + (uint32_t)0U * (uint32_t)4U;
    r10 = wv + (uint32_t)1U * (uint32_t)4U;
    r20 = wv + (uint32_t)2U * (uint32_t)4U;
    r30 = wv + (uint32_t)3U * (uint32_t)4U;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s00;
        uint32_t x = s00[i] ^ r00[i];
        os[i] = x;
      }
    }
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s00;
        uint32_t x = s00[i] ^ r20[i];
        os[i] = x;
      }
    }
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s16;
        uint32_t x = s16[i] ^ r10[i];
        os[i] = x;
      }
    }
    for (i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
    {
      uint32_t *os = s16;
      uint32_t x = s16[i0] ^ r30[i0];
      os[i0] = x;
    }
  }
}

void
Hacl_Blake2s_32_blake2s(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
)
{
  uint32_t stlen = (uint32_t)4U * (uint32_t)4U;
  uint32_t stzero = (uint32_t)0U;
  KRML_CHECK_SIZE(sizeof (uint32_t), stlen);
  {
    uint32_t b[stlen];
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
      KRML_CHECK_SIZE(sizeof (uint32_t), stlen);
      {
        uint32_t b1[stlen];
        {
          uint32_t _i;
          for (_i = 0U; _i < stlen; ++_i)
            b1[_i] = stzero;
        }
        {
          uint8_t b20[64U] = { 0U };
          uint32_t *r0 = b + (uint32_t)0U * (uint32_t)4U;
          uint32_t *r1 = b + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r2 = b + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r3 = b + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t rem10;
          K___uint32_t_uint32_t scrut;
          uint32_t nb;
          uint32_t rem1;
          r2[0U] = iv0;
          r2[1U] = iv1;
          r2[2U] = iv2;
          r2[3U] = iv3;
          r3[0U] = iv4;
          r3[1U] = iv5;
          r3[2U] = iv6;
          r3[3U] = iv7;
          kk_shift_8 = kk << (uint32_t)8U;
          iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ nn));
          r0[0U] = iv0_;
          r0[1U] = iv1;
          r0[2U] = iv2;
          r0[3U] = iv3;
          r1[0U] = iv4;
          r1[1U] = iv5;
          r1[2U] = iv6;
          r1[3U] = iv7;
          if (!(kk == (uint32_t)0U))
          {
            memcpy(b20, k, kk * sizeof (k[0U]));
            {
              uint64_t totlen = (uint64_t)(uint32_t)0U + (uint64_t)(uint32_t)64U;
              uint8_t *b3 = b20 + (uint32_t)0U * (uint32_t)64U;
              blake2s_update_block(b1, b, false, totlen, b3);
            }
          }
          memset(b20, 0U, (uint32_t)64U * sizeof (b20[0U]));
          nb0 = ll / (uint32_t)64U;
          rem10 = ll % (uint32_t)64U;
          if (rem10 == (uint32_t)0U && nb0 > (uint32_t)0U)
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
            lit.snd = rem10;
            scrut = lit;
          }
          nb = scrut.fst;
          rem1 = scrut.snd;
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
            uint8_t *last1 = d + ll - rem1;
            uint64_t totlen;
            uint32_t double_row;
            memcpy(b21, last1, rem1 * sizeof (last1[0U]));
            totlen = prev0 + (uint64_t)ll;
            blake2s_update_block(b1, b, true, totlen, b21);
            memset(b21, 0U, (uint32_t)64U * sizeof (b21[0U]));
            double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)4U;
            KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
            {
              uint8_t b2[double_row];
              memset(b2, 0U, double_row * sizeof (b2[0U]));
              {
                uint8_t *first = b2;
                uint8_t *second = b2 + (uint32_t)4U * (uint32_t)4U;
                uint32_t *row0 = b + (uint32_t)0U * (uint32_t)4U;
                uint32_t *row1 = b + (uint32_t)1U * (uint32_t)4U;
                uint8_t *final;
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                  {
                    store32_le(first + i * (uint32_t)4U, row0[i]);
                  }
                }
                {
                  uint32_t i;
                  for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
                  {
                    store32_le(second + i * (uint32_t)4U, row1[i]);
                  }
                }
                final = b2;
                memcpy(output, final, nn * sizeof (final[0U]));
                memset(b2, 0U, double_row * sizeof (b2[0U]));
                {
                  uint32_t _i;
                  for (_i = 0U; _i < stlen; ++_i)
                    b1[_i] = stzero;
                }
                {
                  uint32_t _i;
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

