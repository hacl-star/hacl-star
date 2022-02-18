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


#include "internal/Hacl_Hash_Blake2.h"

#include "internal/Hacl_Kremlib.h"

uint64_t Hacl_Hash_Core_Blake2_update_blake2s_32(uint32_t *s, uint64_t totlen, uint8_t *block)
{
  uint32_t wv[16U] = { 0U };
  uint64_t totlen1 = totlen + (uint64_t)(uint32_t)64U;
  uint32_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = m_w;
    uint8_t *bj = block + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  uint32_t mask[4U] = { 0U };
  uint32_t wv_14 = (uint32_t)0U;
  uint32_t wv_15 = (uint32_t)0U;
  mask[0U] = (uint32_t)totlen1;
  mask[1U] = (uint32_t)(totlen1 >> (uint32_t)32U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, s, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  uint32_t *wv3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = wv3;
    uint32_t x = wv3[i] ^ mask[i];
    os[i] = x;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)10U; i0++)
  {
    uint32_t start_idx = i0 % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
    uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
    memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
    uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t uu____0 = m_w[s2];
    uint32_t uu____1 = m_w[s4];
    uint32_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint32_t uu____3 = m_w[s3];
    uint32_t uu____4 = m_w[s5];
    uint32_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint32_t uu____6 = m_w[s10];
    uint32_t uu____7 = m_w[s12];
    uint32_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint32_t uu____9 = m_w[s11];
    uint32_t uu____10 = m_w[s13];
    uint32_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
    uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
    uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
    uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
    uint32_t a = (uint32_t)0U;
    uint32_t b0 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint32_t *wv_a0 = wv + a * (uint32_t)4U;
    uint32_t *wv_b0 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + x[i];
      os[i] = x1;
    }
    uint32_t *wv_a1 = wv + d0 * (uint32_t)4U;
    uint32_t *wv_b1 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a1;
      uint32_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;
    }
    uint32_t *r10 = wv_a1;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r10;
      uint32_t x1 = r10[i];
      uint32_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
      os[i] = x10;
    }
    uint32_t *wv_a2 = wv + c0 * (uint32_t)4U;
    uint32_t *wv_b2 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a2;
      uint32_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint32_t *wv_a3 = wv + b0 * (uint32_t)4U;
    uint32_t *wv_b3 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a3;
      uint32_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;
    }
    uint32_t *r12 = wv_a3;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r12;
      uint32_t x1 = r12[i];
      uint32_t x10 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
      os[i] = x10;
    }
    uint32_t *wv_a4 = wv + a * (uint32_t)4U;
    uint32_t *wv_b4 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + y[i];
      os[i] = x1;
    }
    uint32_t *wv_a5 = wv + d0 * (uint32_t)4U;
    uint32_t *wv_b5 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a5;
      uint32_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;
    }
    uint32_t *r13 = wv_a5;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r13;
      uint32_t x1 = r13[i];
      uint32_t x10 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
      os[i] = x10;
    }
    uint32_t *wv_a6 = wv + c0 * (uint32_t)4U;
    uint32_t *wv_b6 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a6;
      uint32_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint32_t *wv_a7 = wv + b0 * (uint32_t)4U;
    uint32_t *wv_b7 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a7;
      uint32_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;
    }
    uint32_t *r14 = wv_a7;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r14;
      uint32_t x1 = r14[i];
      uint32_t x10 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
      os[i] = x10;
    }
    uint32_t *r15 = wv + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r21 = wv + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r31 = wv + (uint32_t)3U * (uint32_t)4U;
    uint32_t *r110 = r15;
    uint32_t x00 = r110[1U];
    uint32_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint32_t *r111 = r21;
    uint32_t x01 = r111[2U];
    uint32_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint32_t *r112 = r31;
    uint32_t x02 = r112[3U];
    uint32_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint32_t *wv_a = wv + a0 * (uint32_t)4U;
    uint32_t *wv_b8 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + z[i];
      os[i] = x1;
    }
    uint32_t *wv_a8 = wv + d * (uint32_t)4U;
    uint32_t *wv_b9 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a8;
      uint32_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;
    }
    uint32_t *r16 = wv_a8;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r16;
      uint32_t x1 = r16[i];
      uint32_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
      os[i] = x13;
    }
    uint32_t *wv_a9 = wv + c * (uint32_t)4U;
    uint32_t *wv_b10 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a9;
      uint32_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint32_t *wv_a10 = wv + b * (uint32_t)4U;
    uint32_t *wv_b11 = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a10;
      uint32_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;
    }
    uint32_t *r17 = wv_a10;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r17;
      uint32_t x1 = r17[i];
      uint32_t x13 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
      os[i] = x13;
    }
    uint32_t *wv_a11 = wv + a0 * (uint32_t)4U;
    uint32_t *wv_b12 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + w[i];
      os[i] = x1;
    }
    uint32_t *wv_a12 = wv + d * (uint32_t)4U;
    uint32_t *wv_b13 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a12;
      uint32_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;
    }
    uint32_t *r18 = wv_a12;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r18;
      uint32_t x1 = r18[i];
      uint32_t x13 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
      os[i] = x13;
    }
    uint32_t *wv_a13 = wv + c * (uint32_t)4U;
    uint32_t *wv_b14 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a13;
      uint32_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint32_t *wv_a14 = wv + b * (uint32_t)4U;
    uint32_t *wv_b = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a14;
      uint32_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;
    }
    uint32_t *r19 = wv_a14;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r19;
      uint32_t x1 = r19[i];
      uint32_t x13 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
      os[i] = x13;
    }
    uint32_t *r113 = wv + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
    uint32_t *r11 = r113;
    uint32_t x03 = r11[3U];
    uint32_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint32_t *r114 = r2;
    uint32_t x04 = r114[2U];
    uint32_t x14 = r114[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x24 = r114[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x34 = r114[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint32_t *r115 = r3;
    uint32_t x0 = r115[1U];
    uint32_t x1 = r115[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x2 = r115[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x3 = r115[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;
  }
  uint32_t *s0 = s + (uint32_t)0U * (uint32_t)4U;
  uint32_t *s1 = s + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r0 = wv + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = wv + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r0[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r2[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r1[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r3[i];
    os[i] = x;
  }
  return totlen1;
}

void Hacl_Hash_Core_Blake2_finish_blake2s_32(uint32_t *s, uint64_t ev, uint8_t *dst)
{
  uint32_t double_row = (uint32_t)2U * ((uint32_t)4U * (uint32_t)4U);
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)4U;
  uint32_t *row0 = s + (uint32_t)0U * (uint32_t)4U;
  uint32_t *row1 = s + (uint32_t)1U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store32_le(first + i * (uint32_t)4U, row0[i]);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store32_le(second + i * (uint32_t)4U, row1[i]);
  }
  uint8_t *final = b;
  memcpy(dst, final, (uint32_t)32U * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
}

FStar_UInt128_uint128
Hacl_Hash_Core_Blake2_update_blake2b_32(
  uint64_t *s,
  FStar_UInt128_uint128 totlen,
  uint8_t *block
)
{
  uint64_t wv[16U] = { 0U };
  FStar_UInt128_uint128
  totlen1 =
    FStar_UInt128_add_mod(totlen,
      FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U));
  uint64_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t *os = m_w;
    uint8_t *bj = block + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t mask[4U] = { 0U };
  uint64_t wv_14 = (uint64_t)0U;
  uint64_t wv_15 = (uint64_t)0U;
  mask[0U] = FStar_UInt128_uint128_to_uint64(totlen1);
  mask[1U] = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen1, (uint32_t)64U));
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, s, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  uint64_t *wv3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = wv3;
    uint64_t x = wv3[i] ^ mask[i];
    os[i] = x;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)12U; i0++)
  {
    uint32_t start_idx = i0 % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
    uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
    memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
    uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
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
    uint64_t uu____0 = m_w[s2];
    uint64_t uu____1 = m_w[s4];
    uint64_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint64_t uu____3 = m_w[s3];
    uint64_t uu____4 = m_w[s5];
    uint64_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint64_t uu____6 = m_w[s10];
    uint64_t uu____7 = m_w[s12];
    uint64_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint64_t uu____9 = m_w[s11];
    uint64_t uu____10 = m_w[s13];
    uint64_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
    uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
    uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
    uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
    uint32_t a = (uint32_t)0U;
    uint32_t b0 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint64_t *wv_a0 = wv + a * (uint32_t)4U;
    uint64_t *wv_b0 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a0;
      uint64_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a0;
      uint64_t x1 = wv_a0[i] + x[i];
      os[i] = x1;
    }
    uint64_t *wv_a1 = wv + d0 * (uint32_t)4U;
    uint64_t *wv_b1 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a1;
      uint64_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;
    }
    uint64_t *r10 = wv_a1;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r10;
      uint64_t x1 = r10[i];
      uint64_t x10 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
      os[i] = x10;
    }
    uint64_t *wv_a2 = wv + c0 * (uint32_t)4U;
    uint64_t *wv_b2 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a2;
      uint64_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint64_t *wv_a3 = wv + b0 * (uint32_t)4U;
    uint64_t *wv_b3 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a3;
      uint64_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;
    }
    uint64_t *r12 = wv_a3;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r12;
      uint64_t x1 = r12[i];
      uint64_t x10 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
      os[i] = x10;
    }
    uint64_t *wv_a4 = wv + a * (uint32_t)4U;
    uint64_t *wv_b4 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a4;
      uint64_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a4;
      uint64_t x1 = wv_a4[i] + y[i];
      os[i] = x1;
    }
    uint64_t *wv_a5 = wv + d0 * (uint32_t)4U;
    uint64_t *wv_b5 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a5;
      uint64_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;
    }
    uint64_t *r13 = wv_a5;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r13;
      uint64_t x1 = r13[i];
      uint64_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
      os[i] = x10;
    }
    uint64_t *wv_a6 = wv + c0 * (uint32_t)4U;
    uint64_t *wv_b6 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a6;
      uint64_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint64_t *wv_a7 = wv + b0 * (uint32_t)4U;
    uint64_t *wv_b7 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a7;
      uint64_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;
    }
    uint64_t *r14 = wv_a7;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r14;
      uint64_t x1 = r14[i];
      uint64_t x10 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
      os[i] = x10;
    }
    uint64_t *r15 = wv + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r21 = wv + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r31 = wv + (uint32_t)3U * (uint32_t)4U;
    uint64_t *r110 = r15;
    uint64_t x00 = r110[1U];
    uint64_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint64_t *r111 = r21;
    uint64_t x01 = r111[2U];
    uint64_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint64_t *r112 = r31;
    uint64_t x02 = r112[3U];
    uint64_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint64_t *wv_a = wv + a0 * (uint32_t)4U;
    uint64_t *wv_b8 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a;
      uint64_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a;
      uint64_t x1 = wv_a[i] + z[i];
      os[i] = x1;
    }
    uint64_t *wv_a8 = wv + d * (uint32_t)4U;
    uint64_t *wv_b9 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a8;
      uint64_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;
    }
    uint64_t *r16 = wv_a8;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r16;
      uint64_t x1 = r16[i];
      uint64_t x13 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
      os[i] = x13;
    }
    uint64_t *wv_a9 = wv + c * (uint32_t)4U;
    uint64_t *wv_b10 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a9;
      uint64_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint64_t *wv_a10 = wv + b * (uint32_t)4U;
    uint64_t *wv_b11 = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a10;
      uint64_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;
    }
    uint64_t *r17 = wv_a10;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r17;
      uint64_t x1 = r17[i];
      uint64_t x13 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
      os[i] = x13;
    }
    uint64_t *wv_a11 = wv + a0 * (uint32_t)4U;
    uint64_t *wv_b12 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a11;
      uint64_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a11;
      uint64_t x1 = wv_a11[i] + w[i];
      os[i] = x1;
    }
    uint64_t *wv_a12 = wv + d * (uint32_t)4U;
    uint64_t *wv_b13 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a12;
      uint64_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;
    }
    uint64_t *r18 = wv_a12;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r18;
      uint64_t x1 = r18[i];
      uint64_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
      os[i] = x13;
    }
    uint64_t *wv_a13 = wv + c * (uint32_t)4U;
    uint64_t *wv_b14 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a13;
      uint64_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint64_t *wv_a14 = wv + b * (uint32_t)4U;
    uint64_t *wv_b = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a14;
      uint64_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;
    }
    uint64_t *r19 = wv_a14;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r19;
      uint64_t x1 = r19[i];
      uint64_t x13 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
      os[i] = x13;
    }
    uint64_t *r113 = wv + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
    uint64_t *r11 = r113;
    uint64_t x03 = r11[3U];
    uint64_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint64_t *r114 = r2;
    uint64_t x04 = r114[2U];
    uint64_t x14 = r114[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x24 = r114[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x34 = r114[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint64_t *r115 = r3;
    uint64_t x0 = r115[1U];
    uint64_t x1 = r115[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x2 = r115[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x3 = r115[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;
  }
  uint64_t *s0 = s + (uint32_t)0U * (uint32_t)4U;
  uint64_t *s1 = s + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r0 = wv + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = wv + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s0;
    uint64_t x = s0[i] ^ r0[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s0;
    uint64_t x = s0[i] ^ r2[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s1;
    uint64_t x = s1[i] ^ r1[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s1;
    uint64_t x = s1[i] ^ r3[i];
    os[i] = x;
  }
  return totlen1;
}

void
Hacl_Hash_Core_Blake2_finish_blake2b_32(uint64_t *s, FStar_UInt128_uint128 ev, uint8_t *dst)
{
  uint32_t double_row = (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U);
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
  uint64_t *row0 = s + (uint32_t)0U * (uint32_t)4U;
  uint64_t *row1 = s + (uint32_t)1U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store64_le(first + i * (uint32_t)8U, row0[i]);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store64_le(second + i * (uint32_t)8U, row1[i]);
  }
  uint8_t *final = b;
  memcpy(dst, final, (uint32_t)64U * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
}

uint64_t
Hacl_Hash_Blake2_update_multi_blake2s_32(
  uint32_t *s,
  uint64_t ev,
  uint8_t *blocks,
  uint32_t n_blocks
)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)64U;
    uint8_t *block = blocks + sz * i;
    uint64_t
    v_ =
      Hacl_Hash_Core_Blake2_update_blake2s_32(s,
        ev + (uint64_t)i * (uint64_t)(uint32_t)64U,
        block);
  }
  return ev + (uint64_t)n_blocks * (uint64_t)(uint32_t)64U;
}

FStar_UInt128_uint128
Hacl_Hash_Blake2_update_multi_blake2b_32(
  uint64_t *s,
  FStar_UInt128_uint128 ev,
  uint8_t *blocks,
  uint32_t n_blocks
)
{
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint32_t sz = (uint32_t)128U;
    uint8_t *block = blocks + sz * i;
    FStar_UInt128_uint128
    v_ =
      Hacl_Hash_Core_Blake2_update_blake2b_32(s,
        FStar_UInt128_add_mod(ev,
          FStar_UInt128_uint64_to_uint128((uint64_t)i * (uint64_t)(uint32_t)128U)),
        block);
  }
  return
    FStar_UInt128_add_mod(ev,
      FStar_UInt128_uint64_to_uint128((uint64_t)n_blocks * (uint64_t)(uint32_t)128U));
}

uint64_t
Hacl_Hash_Blake2_update_last_blake2s_32(
  uint32_t *s,
  uint64_t ev,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len0 = blocks_n * (uint32_t)64U;
  uint32_t rest_len0 = input_len - blocks_len0;
  K___uint32_t_uint32_t_uint32_t scrut;
  if (rest_len0 == (uint32_t)0U && blocks_n > (uint32_t)0U)
  {
    uint32_t blocks_n1 = blocks_n - (uint32_t)1U;
    uint32_t blocks_len1 = blocks_len0 - (uint32_t)64U;
    uint32_t rest_len1 = (uint32_t)64U;
    scrut =
      ((K___uint32_t_uint32_t_uint32_t){ .fst = blocks_n1, .snd = blocks_len1, .thd = rest_len1 });
  }
  else
  {
    scrut =
      ((K___uint32_t_uint32_t_uint32_t){ .fst = blocks_n, .snd = blocks_len0, .thd = rest_len0 });
  }
  uint32_t num_blocks0 = scrut.fst;
  uint32_t blocks_len = scrut.snd;
  uint32_t rest_len1 = scrut.thd;
  uint8_t *blocks0 = input;
  uint8_t *rest0 = input + blocks_len;
  K___uint32_t_uint32_t_uint32_t__uint8_t___uint8_t_
  scrut0 =
    { .fst = num_blocks0, .snd = blocks_len, .thd = rest_len1, .f3 = blocks0, .f4 = rest0 };
  uint32_t num_blocks = scrut0.fst;
  uint32_t rest_len = scrut0.thd;
  uint8_t *blocks = scrut0.f3;
  uint8_t *rest = scrut0.f4;
  uint64_t ev_ = Hacl_Hash_Blake2_update_multi_blake2s_32(s, ev, blocks, num_blocks);
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  uint8_t tmp[64U] = { 0U };
  uint8_t *tmp_rest = tmp;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  uint64_t totlen = ev_ + (uint64_t)rest_len;
  uint32_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = m_w;
    uint8_t *bj = tmp + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
  uint32_t mask[4U] = { 0U };
  uint32_t wv_14 = (uint32_t)0xFFFFFFFFU;
  uint32_t wv_15 = (uint32_t)0U;
  mask[0U] = (uint32_t)totlen;
  mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, s, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  uint32_t *wv3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = wv3;
    uint32_t x = wv3[i] ^ mask[i];
    os[i] = x;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)10U; i0++)
  {
    uint32_t start_idx = i0 % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
    uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
    memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
    uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t uu____0 = m_w[s2];
    uint32_t uu____1 = m_w[s4];
    uint32_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint32_t uu____3 = m_w[s3];
    uint32_t uu____4 = m_w[s5];
    uint32_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint32_t uu____6 = m_w[s10];
    uint32_t uu____7 = m_w[s12];
    uint32_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint32_t uu____9 = m_w[s11];
    uint32_t uu____10 = m_w[s13];
    uint32_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
    uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
    uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
    uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
    uint32_t a = (uint32_t)0U;
    uint32_t b0 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint32_t *wv_a0 = wv + a * (uint32_t)4U;
    uint32_t *wv_b0 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + x[i];
      os[i] = x1;
    }
    uint32_t *wv_a1 = wv + d0 * (uint32_t)4U;
    uint32_t *wv_b1 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a1;
      uint32_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;
    }
    uint32_t *r10 = wv_a1;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r10;
      uint32_t x1 = r10[i];
      uint32_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
      os[i] = x10;
    }
    uint32_t *wv_a2 = wv + c0 * (uint32_t)4U;
    uint32_t *wv_b2 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a2;
      uint32_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint32_t *wv_a3 = wv + b0 * (uint32_t)4U;
    uint32_t *wv_b3 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a3;
      uint32_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;
    }
    uint32_t *r12 = wv_a3;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r12;
      uint32_t x1 = r12[i];
      uint32_t x10 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
      os[i] = x10;
    }
    uint32_t *wv_a4 = wv + a * (uint32_t)4U;
    uint32_t *wv_b4 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + y[i];
      os[i] = x1;
    }
    uint32_t *wv_a5 = wv + d0 * (uint32_t)4U;
    uint32_t *wv_b5 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a5;
      uint32_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;
    }
    uint32_t *r13 = wv_a5;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r13;
      uint32_t x1 = r13[i];
      uint32_t x10 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
      os[i] = x10;
    }
    uint32_t *wv_a6 = wv + c0 * (uint32_t)4U;
    uint32_t *wv_b6 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a6;
      uint32_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint32_t *wv_a7 = wv + b0 * (uint32_t)4U;
    uint32_t *wv_b7 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a7;
      uint32_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;
    }
    uint32_t *r14 = wv_a7;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r14;
      uint32_t x1 = r14[i];
      uint32_t x10 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
      os[i] = x10;
    }
    uint32_t *r15 = wv + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r21 = wv + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r31 = wv + (uint32_t)3U * (uint32_t)4U;
    uint32_t *r110 = r15;
    uint32_t x00 = r110[1U];
    uint32_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint32_t *r111 = r21;
    uint32_t x01 = r111[2U];
    uint32_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint32_t *r112 = r31;
    uint32_t x02 = r112[3U];
    uint32_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint32_t *wv_a = wv + a0 * (uint32_t)4U;
    uint32_t *wv_b8 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + z[i];
      os[i] = x1;
    }
    uint32_t *wv_a8 = wv + d * (uint32_t)4U;
    uint32_t *wv_b9 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a8;
      uint32_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;
    }
    uint32_t *r16 = wv_a8;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r16;
      uint32_t x1 = r16[i];
      uint32_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
      os[i] = x13;
    }
    uint32_t *wv_a9 = wv + c * (uint32_t)4U;
    uint32_t *wv_b10 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a9;
      uint32_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint32_t *wv_a10 = wv + b * (uint32_t)4U;
    uint32_t *wv_b11 = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a10;
      uint32_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;
    }
    uint32_t *r17 = wv_a10;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r17;
      uint32_t x1 = r17[i];
      uint32_t x13 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
      os[i] = x13;
    }
    uint32_t *wv_a11 = wv + a0 * (uint32_t)4U;
    uint32_t *wv_b12 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + w[i];
      os[i] = x1;
    }
    uint32_t *wv_a12 = wv + d * (uint32_t)4U;
    uint32_t *wv_b13 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a12;
      uint32_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;
    }
    uint32_t *r18 = wv_a12;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r18;
      uint32_t x1 = r18[i];
      uint32_t x13 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
      os[i] = x13;
    }
    uint32_t *wv_a13 = wv + c * (uint32_t)4U;
    uint32_t *wv_b14 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a13;
      uint32_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint32_t *wv_a14 = wv + b * (uint32_t)4U;
    uint32_t *wv_b = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a14;
      uint32_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;
    }
    uint32_t *r19 = wv_a14;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r19;
      uint32_t x1 = r19[i];
      uint32_t x13 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
      os[i] = x13;
    }
    uint32_t *r113 = wv + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
    uint32_t *r11 = r113;
    uint32_t x03 = r11[3U];
    uint32_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint32_t *r114 = r2;
    uint32_t x04 = r114[2U];
    uint32_t x14 = r114[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x24 = r114[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x34 = r114[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint32_t *r115 = r3;
    uint32_t x0 = r115[1U];
    uint32_t x1 = r115[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x2 = r115[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x3 = r115[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;
  }
  uint32_t *s0 = s + (uint32_t)0U * (uint32_t)4U;
  uint32_t *s1 = s + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r0 = wv + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = wv + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r0[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r2[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r1[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r3[i];
    os[i] = x;
  }
  return (uint64_t)0U;
}

FStar_UInt128_uint128
Hacl_Hash_Blake2_update_last_blake2b_32(
  uint64_t *s,
  FStar_UInt128_uint128 ev,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)128U;
  uint32_t blocks_len0 = blocks_n * (uint32_t)128U;
  uint32_t rest_len0 = input_len - blocks_len0;
  K___uint32_t_uint32_t_uint32_t scrut;
  if (rest_len0 == (uint32_t)0U && blocks_n > (uint32_t)0U)
  {
    uint32_t blocks_n1 = blocks_n - (uint32_t)1U;
    uint32_t blocks_len1 = blocks_len0 - (uint32_t)128U;
    uint32_t rest_len1 = (uint32_t)128U;
    scrut =
      ((K___uint32_t_uint32_t_uint32_t){ .fst = blocks_n1, .snd = blocks_len1, .thd = rest_len1 });
  }
  else
  {
    scrut =
      ((K___uint32_t_uint32_t_uint32_t){ .fst = blocks_n, .snd = blocks_len0, .thd = rest_len0 });
  }
  uint32_t num_blocks0 = scrut.fst;
  uint32_t blocks_len = scrut.snd;
  uint32_t rest_len1 = scrut.thd;
  uint8_t *blocks0 = input;
  uint8_t *rest0 = input + blocks_len;
  K___uint32_t_uint32_t_uint32_t__uint8_t___uint8_t_
  scrut0 =
    { .fst = num_blocks0, .snd = blocks_len, .thd = rest_len1, .f3 = blocks0, .f4 = rest0 };
  uint32_t num_blocks = scrut0.fst;
  uint32_t rest_len = scrut0.thd;
  uint8_t *blocks = scrut0.f3;
  uint8_t *rest = scrut0.f4;
  FStar_UInt128_uint128
  ev_ = Hacl_Hash_Blake2_update_multi_blake2b_32(s, ev, blocks, num_blocks);
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
  uint64_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  uint8_t tmp[128U] = { 0U };
  uint8_t *tmp_rest = tmp;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  FStar_UInt128_uint128
  totlen = FStar_UInt128_add_mod(ev_, FStar_UInt128_uint64_to_uint128((uint64_t)rest_len));
  uint64_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t *os = m_w;
    uint8_t *bj = tmp + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t mask[4U] = { 0U };
  uint64_t wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t wv_15 = (uint64_t)0U;
  mask[0U] = FStar_UInt128_uint128_to_uint64(totlen);
  mask[1U] = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen, (uint32_t)64U));
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, s, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  uint64_t *wv3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = wv3;
    uint64_t x = wv3[i] ^ mask[i];
    os[i] = x;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)12U; i0++)
  {
    uint32_t start_idx = i0 % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
    uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
    memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
    uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
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
    uint64_t uu____0 = m_w[s2];
    uint64_t uu____1 = m_w[s4];
    uint64_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint64_t uu____3 = m_w[s3];
    uint64_t uu____4 = m_w[s5];
    uint64_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint64_t uu____6 = m_w[s10];
    uint64_t uu____7 = m_w[s12];
    uint64_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint64_t uu____9 = m_w[s11];
    uint64_t uu____10 = m_w[s13];
    uint64_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
    uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
    uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
    uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
    uint32_t a = (uint32_t)0U;
    uint32_t b0 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint64_t *wv_a0 = wv + a * (uint32_t)4U;
    uint64_t *wv_b0 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a0;
      uint64_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a0;
      uint64_t x1 = wv_a0[i] + x[i];
      os[i] = x1;
    }
    uint64_t *wv_a1 = wv + d0 * (uint32_t)4U;
    uint64_t *wv_b1 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a1;
      uint64_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;
    }
    uint64_t *r10 = wv_a1;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r10;
      uint64_t x1 = r10[i];
      uint64_t x10 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
      os[i] = x10;
    }
    uint64_t *wv_a2 = wv + c0 * (uint32_t)4U;
    uint64_t *wv_b2 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a2;
      uint64_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint64_t *wv_a3 = wv + b0 * (uint32_t)4U;
    uint64_t *wv_b3 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a3;
      uint64_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;
    }
    uint64_t *r12 = wv_a3;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r12;
      uint64_t x1 = r12[i];
      uint64_t x10 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
      os[i] = x10;
    }
    uint64_t *wv_a4 = wv + a * (uint32_t)4U;
    uint64_t *wv_b4 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a4;
      uint64_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a4;
      uint64_t x1 = wv_a4[i] + y[i];
      os[i] = x1;
    }
    uint64_t *wv_a5 = wv + d0 * (uint32_t)4U;
    uint64_t *wv_b5 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a5;
      uint64_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;
    }
    uint64_t *r13 = wv_a5;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r13;
      uint64_t x1 = r13[i];
      uint64_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
      os[i] = x10;
    }
    uint64_t *wv_a6 = wv + c0 * (uint32_t)4U;
    uint64_t *wv_b6 = wv + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a6;
      uint64_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint64_t *wv_a7 = wv + b0 * (uint32_t)4U;
    uint64_t *wv_b7 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a7;
      uint64_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;
    }
    uint64_t *r14 = wv_a7;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r14;
      uint64_t x1 = r14[i];
      uint64_t x10 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
      os[i] = x10;
    }
    uint64_t *r15 = wv + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r21 = wv + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r31 = wv + (uint32_t)3U * (uint32_t)4U;
    uint64_t *r110 = r15;
    uint64_t x00 = r110[1U];
    uint64_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint64_t *r111 = r21;
    uint64_t x01 = r111[2U];
    uint64_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint64_t *r112 = r31;
    uint64_t x02 = r112[3U];
    uint64_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint64_t *wv_a = wv + a0 * (uint32_t)4U;
    uint64_t *wv_b8 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a;
      uint64_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a;
      uint64_t x1 = wv_a[i] + z[i];
      os[i] = x1;
    }
    uint64_t *wv_a8 = wv + d * (uint32_t)4U;
    uint64_t *wv_b9 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a8;
      uint64_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;
    }
    uint64_t *r16 = wv_a8;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r16;
      uint64_t x1 = r16[i];
      uint64_t x13 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
      os[i] = x13;
    }
    uint64_t *wv_a9 = wv + c * (uint32_t)4U;
    uint64_t *wv_b10 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a9;
      uint64_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint64_t *wv_a10 = wv + b * (uint32_t)4U;
    uint64_t *wv_b11 = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a10;
      uint64_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;
    }
    uint64_t *r17 = wv_a10;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r17;
      uint64_t x1 = r17[i];
      uint64_t x13 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
      os[i] = x13;
    }
    uint64_t *wv_a11 = wv + a0 * (uint32_t)4U;
    uint64_t *wv_b12 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a11;
      uint64_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a11;
      uint64_t x1 = wv_a11[i] + w[i];
      os[i] = x1;
    }
    uint64_t *wv_a12 = wv + d * (uint32_t)4U;
    uint64_t *wv_b13 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a12;
      uint64_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;
    }
    uint64_t *r18 = wv_a12;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r18;
      uint64_t x1 = r18[i];
      uint64_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
      os[i] = x13;
    }
    uint64_t *wv_a13 = wv + c * (uint32_t)4U;
    uint64_t *wv_b14 = wv + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a13;
      uint64_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint64_t *wv_a14 = wv + b * (uint32_t)4U;
    uint64_t *wv_b = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a14;
      uint64_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;
    }
    uint64_t *r19 = wv_a14;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r19;
      uint64_t x1 = r19[i];
      uint64_t x13 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
      os[i] = x13;
    }
    uint64_t *r113 = wv + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
    uint64_t *r11 = r113;
    uint64_t x03 = r11[3U];
    uint64_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint64_t *r114 = r2;
    uint64_t x04 = r114[2U];
    uint64_t x14 = r114[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x24 = r114[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x34 = r114[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint64_t *r115 = r3;
    uint64_t x0 = r115[1U];
    uint64_t x1 = r115[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x2 = r115[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x3 = r115[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;
  }
  uint64_t *s0 = s + (uint32_t)0U * (uint32_t)4U;
  uint64_t *s1 = s + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r0 = wv + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = wv + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s0;
    uint64_t x = s0[i] ^ r0[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s0;
    uint64_t x = s0[i] ^ r2[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s1;
    uint64_t x = s1[i] ^ r1[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s1;
    uint64_t x = s1[i] ^ r3[i];
    os[i] = x;
  }
  return FStar_UInt128_uint64_to_uint128((uint64_t)0U);
}

void Hacl_Hash_Blake2_hash_blake2s_32(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  Hacl_Blake2s_32_blake2s((uint32_t)32U, dst, input_len, input, (uint32_t)0U, NULL);
}

void Hacl_Hash_Blake2_hash_blake2b_32(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  Hacl_Blake2b_32_blake2b((uint32_t)64U, dst, input_len, input, (uint32_t)0U, NULL);
}

static inline void
blake2b_update_block(
  uint64_t *wv,
  uint64_t *hash,
  bool flag,
  FStar_UInt128_uint128 totlen,
  uint8_t *d
)
{
  uint64_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint64_t *os = m_w;
    uint8_t *bj = d + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t mask[4U] = { 0U };
  uint64_t wv_14;
  if (flag)
  {
    wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  }
  else
  {
    wv_14 = (uint64_t)0U;
  }
  uint64_t wv_15 = (uint64_t)0U;
  mask[0U] = FStar_UInt128_uint128_to_uint64(totlen);
  mask[1U] = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(totlen, (uint32_t)64U));
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, hash, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  uint64_t *wv3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = wv3;
    uint64_t x = wv3[i] ^ mask[i];
    os[i] = x;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)12U; i0++)
  {
    uint32_t start_idx = i0 % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
    uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
    memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
    uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
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
    uint64_t uu____0 = m_w[s2];
    uint64_t uu____1 = m_w[s4];
    uint64_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint64_t uu____3 = m_w[s3];
    uint64_t uu____4 = m_w[s5];
    uint64_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint64_t uu____6 = m_w[s10];
    uint64_t uu____7 = m_w[s12];
    uint64_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint64_t uu____9 = m_w[s11];
    uint64_t uu____10 = m_w[s13];
    uint64_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
    uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
    uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
    uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
    uint32_t a = (uint32_t)0U;
    uint32_t b0 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d10 = (uint32_t)3U;
    uint64_t *wv_a0 = wv + a * (uint32_t)4U;
    uint64_t *wv_b0 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a0;
      uint64_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a0;
      uint64_t x1 = wv_a0[i] + x[i];
      os[i] = x1;
    }
    uint64_t *wv_a1 = wv + d10 * (uint32_t)4U;
    uint64_t *wv_b1 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a1;
      uint64_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;
    }
    uint64_t *r10 = wv_a1;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r10;
      uint64_t x1 = r10[i];
      uint64_t x10 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
      os[i] = x10;
    }
    uint64_t *wv_a2 = wv + c0 * (uint32_t)4U;
    uint64_t *wv_b2 = wv + d10 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a2;
      uint64_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint64_t *wv_a3 = wv + b0 * (uint32_t)4U;
    uint64_t *wv_b3 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a3;
      uint64_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;
    }
    uint64_t *r12 = wv_a3;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r12;
      uint64_t x1 = r12[i];
      uint64_t x10 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
      os[i] = x10;
    }
    uint64_t *wv_a4 = wv + a * (uint32_t)4U;
    uint64_t *wv_b4 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a4;
      uint64_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a4;
      uint64_t x1 = wv_a4[i] + y[i];
      os[i] = x1;
    }
    uint64_t *wv_a5 = wv + d10 * (uint32_t)4U;
    uint64_t *wv_b5 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a5;
      uint64_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;
    }
    uint64_t *r13 = wv_a5;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r13;
      uint64_t x1 = r13[i];
      uint64_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
      os[i] = x10;
    }
    uint64_t *wv_a6 = wv + c0 * (uint32_t)4U;
    uint64_t *wv_b6 = wv + d10 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a6;
      uint64_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint64_t *wv_a7 = wv + b0 * (uint32_t)4U;
    uint64_t *wv_b7 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a7;
      uint64_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;
    }
    uint64_t *r14 = wv_a7;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r14;
      uint64_t x1 = r14[i];
      uint64_t x10 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
      os[i] = x10;
    }
    uint64_t *r15 = wv + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r21 = wv + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r31 = wv + (uint32_t)3U * (uint32_t)4U;
    uint64_t *r110 = r15;
    uint64_t x00 = r110[1U];
    uint64_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint64_t *r111 = r21;
    uint64_t x01 = r111[2U];
    uint64_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint64_t *r112 = r31;
    uint64_t x02 = r112[3U];
    uint64_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d1 = (uint32_t)3U;
    uint64_t *wv_a = wv + a0 * (uint32_t)4U;
    uint64_t *wv_b8 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a;
      uint64_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a;
      uint64_t x1 = wv_a[i] + z[i];
      os[i] = x1;
    }
    uint64_t *wv_a8 = wv + d1 * (uint32_t)4U;
    uint64_t *wv_b9 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a8;
      uint64_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;
    }
    uint64_t *r16 = wv_a8;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r16;
      uint64_t x1 = r16[i];
      uint64_t x13 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
      os[i] = x13;
    }
    uint64_t *wv_a9 = wv + c * (uint32_t)4U;
    uint64_t *wv_b10 = wv + d1 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a9;
      uint64_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint64_t *wv_a10 = wv + b * (uint32_t)4U;
    uint64_t *wv_b11 = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a10;
      uint64_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;
    }
    uint64_t *r17 = wv_a10;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r17;
      uint64_t x1 = r17[i];
      uint64_t x13 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
      os[i] = x13;
    }
    uint64_t *wv_a11 = wv + a0 * (uint32_t)4U;
    uint64_t *wv_b12 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a11;
      uint64_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a11;
      uint64_t x1 = wv_a11[i] + w[i];
      os[i] = x1;
    }
    uint64_t *wv_a12 = wv + d1 * (uint32_t)4U;
    uint64_t *wv_b13 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a12;
      uint64_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;
    }
    uint64_t *r18 = wv_a12;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r18;
      uint64_t x1 = r18[i];
      uint64_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
      os[i] = x13;
    }
    uint64_t *wv_a13 = wv + c * (uint32_t)4U;
    uint64_t *wv_b14 = wv + d1 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a13;
      uint64_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint64_t *wv_a14 = wv + b * (uint32_t)4U;
    uint64_t *wv_b = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a14;
      uint64_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;
    }
    uint64_t *r19 = wv_a14;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = r19;
      uint64_t x1 = r19[i];
      uint64_t x13 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
      os[i] = x13;
    }
    uint64_t *r113 = wv + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
    uint64_t *r11 = r113;
    uint64_t x03 = r11[3U];
    uint64_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint64_t *r114 = r2;
    uint64_t x04 = r114[2U];
    uint64_t x14 = r114[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x24 = r114[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x34 = r114[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint64_t *r115 = r3;
    uint64_t x0 = r115[1U];
    uint64_t x1 = r115[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint64_t x2 = r115[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint64_t x3 = r115[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;
  }
  uint64_t *s0 = hash + (uint32_t)0U * (uint32_t)4U;
  uint64_t *s1 = hash + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r0 = wv + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = wv + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s0;
    uint64_t x = s0[i] ^ r0[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s0;
    uint64_t x = s0[i] ^ r2[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s1;
    uint64_t x = s1[i] ^ r1[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = s1;
    uint64_t x = s1[i] ^ r3[i];
    os[i] = x;
  }
}

inline void Hacl_Blake2b_32_blake2b_init(uint64_t *hash, uint32_t kk, uint32_t nn)
{
  uint64_t *r0 = hash + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = hash + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = hash + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = hash + (uint32_t)3U * (uint32_t)4U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r2[0U] = iv0;
  r2[1U] = iv1;
  r2[2U] = iv2;
  r2[3U] = iv3;
  r3[0U] = iv4;
  r3[1U] = iv5;
  r3[2U] = iv6;
  r3[3U] = iv7;
  uint64_t kk_shift_8 = (uint64_t)kk << (uint32_t)8U;
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)nn));
  r0[0U] = iv0_;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
}

inline void
Hacl_Blake2b_32_blake2b_update_key(
  uint64_t *wv,
  uint64_t *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t ll
)
{
  FStar_UInt128_uint128 lb = FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U);
  uint8_t b[128U] = { 0U };
  memcpy(b, k, kk * sizeof (uint8_t));
  if (ll == (uint32_t)0U)
  {
    blake2b_update_block(wv, hash, true, lb, b);
  }
  else
  {
    blake2b_update_block(wv, hash, false, lb, b);
  }
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
}

inline void
Hacl_Blake2b_32_blake2b_update_multi(
  uint32_t len,
  uint64_t *wv,
  uint64_t *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks,
  uint32_t nb
)
{
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    FStar_UInt128_uint128
    totlen =
      FStar_UInt128_add_mod(prev,
        FStar_UInt128_uint64_to_uint128((uint64_t)((i + (uint32_t)1U) * (uint32_t)128U)));
    uint8_t *b = blocks + i * (uint32_t)128U;
    blake2b_update_block(wv, hash, false, totlen, b);
  }
}

inline void
Hacl_Blake2b_32_blake2b_update_last(
  uint32_t len,
  uint64_t *wv,
  uint64_t *hash,
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
  blake2b_update_block(wv, hash, true, totlen, b);
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
}

static inline void
blake2b_update_blocks(
  uint32_t len,
  uint64_t *wv,
  uint64_t *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks
)
{
  uint32_t nb0 = len / (uint32_t)128U;
  uint32_t rem0 = len % (uint32_t)128U;
  K___uint32_t_uint32_t scrut;
  if (rem0 == (uint32_t)0U && nb0 > (uint32_t)0U)
  {
    uint32_t nb_ = nb0 - (uint32_t)1U;
    uint32_t rem_ = (uint32_t)128U;
    scrut = ((K___uint32_t_uint32_t){ .fst = nb_, .snd = rem_ });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = nb0, .snd = rem0 });
  }
  uint32_t nb = scrut.fst;
  uint32_t rem = scrut.snd;
  Hacl_Blake2b_32_blake2b_update_multi(len, wv, hash, prev, blocks, nb);
  Hacl_Blake2b_32_blake2b_update_last(len, wv, hash, prev, rem, blocks);
}

static inline void
blake2b_update(uint64_t *wv, uint64_t *hash, uint32_t kk, uint8_t *k, uint32_t ll, uint8_t *d)
{
  FStar_UInt128_uint128 lb = FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)128U);
  if (kk > (uint32_t)0U)
  {
    Hacl_Blake2b_32_blake2b_update_key(wv, hash, kk, k, ll);
    if (!(ll == (uint32_t)0U))
    {
      blake2b_update_blocks(ll, wv, hash, lb, d);
      return;
    }
    return;
  }
  blake2b_update_blocks(ll,
    wv,
    hash,
    FStar_UInt128_uint64_to_uint128((uint64_t)(uint32_t)0U),
    d);
}

inline void Hacl_Blake2b_32_blake2b_finish(uint32_t nn, uint8_t *output, uint64_t *hash)
{
  uint32_t double_row = (uint32_t)2U * ((uint32_t)4U * (uint32_t)8U);
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
  uint64_t *row0 = hash + (uint32_t)0U * (uint32_t)4U;
  uint64_t *row1 = hash + (uint32_t)1U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store64_le(first + i * (uint32_t)8U, row0[i]);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store64_le(second + i * (uint32_t)8U, row1[i]);
  }
  uint8_t *final = b;
  memcpy(output, final, nn * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
}

void
Hacl_Blake2b_32_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
)
{
  uint32_t stlen = (uint32_t)4U * (uint32_t)4U;
  uint64_t stzero = (uint64_t)0U;
  KRML_CHECK_SIZE(sizeof (uint64_t), stlen);
  uint64_t b[stlen];
  for (uint32_t _i = 0U; _i < stlen; ++_i)
    b[_i] = stzero;
  KRML_CHECK_SIZE(sizeof (uint64_t), stlen);
  uint64_t b1[stlen];
  for (uint32_t _i = 0U; _i < stlen; ++_i)
    b1[_i] = stzero;
  Hacl_Blake2b_32_blake2b_init(b, kk, nn);
  blake2b_update(b1, b, kk, k, ll, d);
  Hacl_Blake2b_32_blake2b_finish(nn, output, b);
  Lib_Memzero0_memzero(b1, stlen * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, stlen * sizeof (b[0U]));
}

static inline void
blake2s_update_block(uint32_t *wv, uint32_t *hash, bool flag, uint64_t totlen, uint8_t *d)
{
  uint32_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = m_w;
    uint8_t *bj = d + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r = u;
    uint32_t x = r;
    os[i] = x;
  }
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
  uint32_t wv_15 = (uint32_t)0U;
  mask[0U] = (uint32_t)totlen;
  mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(wv, hash, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  uint32_t *wv3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = wv3;
    uint32_t x = wv3[i] ^ mask[i];
    os[i] = x;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)10U; i0++)
  {
    uint32_t start_idx = i0 % (uint32_t)10U * (uint32_t)16U;
    KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
    uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
    memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
    uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t uu____0 = m_w[s2];
    uint32_t uu____1 = m_w[s4];
    uint32_t uu____2 = m_w[s6];
    r0[0U] = m_w[s0];
    r0[1U] = uu____0;
    r0[2U] = uu____1;
    r0[3U] = uu____2;
    uint32_t uu____3 = m_w[s3];
    uint32_t uu____4 = m_w[s5];
    uint32_t uu____5 = m_w[s7];
    r1[0U] = m_w[s1];
    r1[1U] = uu____3;
    r1[2U] = uu____4;
    r1[3U] = uu____5;
    uint32_t uu____6 = m_w[s10];
    uint32_t uu____7 = m_w[s12];
    uint32_t uu____8 = m_w[s14];
    r20[0U] = m_w[s8];
    r20[1U] = uu____6;
    r20[2U] = uu____7;
    r20[3U] = uu____8;
    uint32_t uu____9 = m_w[s11];
    uint32_t uu____10 = m_w[s13];
    uint32_t uu____11 = m_w[s15];
    r30[0U] = m_w[s9];
    r30[1U] = uu____9;
    r30[2U] = uu____10;
    r30[3U] = uu____11;
    uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
    uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
    uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
    uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
    uint32_t a = (uint32_t)0U;
    uint32_t b0 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d10 = (uint32_t)3U;
    uint32_t *wv_a0 = wv + a * (uint32_t)4U;
    uint32_t *wv_b0 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + wv_b0[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a0;
      uint32_t x1 = wv_a0[i] + x[i];
      os[i] = x1;
    }
    uint32_t *wv_a1 = wv + d10 * (uint32_t)4U;
    uint32_t *wv_b1 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a1;
      uint32_t x1 = wv_a1[i] ^ wv_b1[i];
      os[i] = x1;
    }
    uint32_t *r10 = wv_a1;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r10;
      uint32_t x1 = r10[i];
      uint32_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
      os[i] = x10;
    }
    uint32_t *wv_a2 = wv + c0 * (uint32_t)4U;
    uint32_t *wv_b2 = wv + d10 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a2;
      uint32_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint32_t *wv_a3 = wv + b0 * (uint32_t)4U;
    uint32_t *wv_b3 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a3;
      uint32_t x1 = wv_a3[i] ^ wv_b3[i];
      os[i] = x1;
    }
    uint32_t *r12 = wv_a3;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r12;
      uint32_t x1 = r12[i];
      uint32_t x10 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
      os[i] = x10;
    }
    uint32_t *wv_a4 = wv + a * (uint32_t)4U;
    uint32_t *wv_b4 = wv + b0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + wv_b4[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a4;
      uint32_t x1 = wv_a4[i] + y[i];
      os[i] = x1;
    }
    uint32_t *wv_a5 = wv + d10 * (uint32_t)4U;
    uint32_t *wv_b5 = wv + a * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a5;
      uint32_t x1 = wv_a5[i] ^ wv_b5[i];
      os[i] = x1;
    }
    uint32_t *r13 = wv_a5;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r13;
      uint32_t x1 = r13[i];
      uint32_t x10 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
      os[i] = x10;
    }
    uint32_t *wv_a6 = wv + c0 * (uint32_t)4U;
    uint32_t *wv_b6 = wv + d10 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a6;
      uint32_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint32_t *wv_a7 = wv + b0 * (uint32_t)4U;
    uint32_t *wv_b7 = wv + c0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a7;
      uint32_t x1 = wv_a7[i] ^ wv_b7[i];
      os[i] = x1;
    }
    uint32_t *r14 = wv_a7;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r14;
      uint32_t x1 = r14[i];
      uint32_t x10 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
      os[i] = x10;
    }
    uint32_t *r15 = wv + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r21 = wv + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r31 = wv + (uint32_t)3U * (uint32_t)4U;
    uint32_t *r110 = r15;
    uint32_t x00 = r110[1U];
    uint32_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r110[0U] = x00;
    r110[1U] = x10;
    r110[2U] = x20;
    r110[3U] = x30;
    uint32_t *r111 = r21;
    uint32_t x01 = r111[2U];
    uint32_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r111[0U] = x01;
    r111[1U] = x11;
    r111[2U] = x21;
    r111[3U] = x31;
    uint32_t *r112 = r31;
    uint32_t x02 = r112[3U];
    uint32_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r112[0U] = x02;
    r112[1U] = x12;
    r112[2U] = x22;
    r112[3U] = x32;
    uint32_t a0 = (uint32_t)0U;
    uint32_t b = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d1 = (uint32_t)3U;
    uint32_t *wv_a = wv + a0 * (uint32_t)4U;
    uint32_t *wv_b8 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + wv_b8[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a;
      uint32_t x1 = wv_a[i] + z[i];
      os[i] = x1;
    }
    uint32_t *wv_a8 = wv + d1 * (uint32_t)4U;
    uint32_t *wv_b9 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a8;
      uint32_t x1 = wv_a8[i] ^ wv_b9[i];
      os[i] = x1;
    }
    uint32_t *r16 = wv_a8;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r16;
      uint32_t x1 = r16[i];
      uint32_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
      os[i] = x13;
    }
    uint32_t *wv_a9 = wv + c * (uint32_t)4U;
    uint32_t *wv_b10 = wv + d1 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a9;
      uint32_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint32_t *wv_a10 = wv + b * (uint32_t)4U;
    uint32_t *wv_b11 = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a10;
      uint32_t x1 = wv_a10[i] ^ wv_b11[i];
      os[i] = x1;
    }
    uint32_t *r17 = wv_a10;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r17;
      uint32_t x1 = r17[i];
      uint32_t x13 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
      os[i] = x13;
    }
    uint32_t *wv_a11 = wv + a0 * (uint32_t)4U;
    uint32_t *wv_b12 = wv + b * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + wv_b12[i];
      os[i] = x1;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a11;
      uint32_t x1 = wv_a11[i] + w[i];
      os[i] = x1;
    }
    uint32_t *wv_a12 = wv + d1 * (uint32_t)4U;
    uint32_t *wv_b13 = wv + a0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a12;
      uint32_t x1 = wv_a12[i] ^ wv_b13[i];
      os[i] = x1;
    }
    uint32_t *r18 = wv_a12;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r18;
      uint32_t x1 = r18[i];
      uint32_t x13 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
      os[i] = x13;
    }
    uint32_t *wv_a13 = wv + c * (uint32_t)4U;
    uint32_t *wv_b14 = wv + d1 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a13;
      uint32_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint32_t *wv_a14 = wv + b * (uint32_t)4U;
    uint32_t *wv_b = wv + c * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a14;
      uint32_t x1 = wv_a14[i] ^ wv_b[i];
      os[i] = x1;
    }
    uint32_t *r19 = wv_a14;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = r19;
      uint32_t x1 = r19[i];
      uint32_t x13 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
      os[i] = x13;
    }
    uint32_t *r113 = wv + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
    uint32_t *r11 = r113;
    uint32_t x03 = r11[3U];
    uint32_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
    r11[0U] = x03;
    r11[1U] = x13;
    r11[2U] = x23;
    r11[3U] = x33;
    uint32_t *r114 = r2;
    uint32_t x04 = r114[2U];
    uint32_t x14 = r114[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x24 = r114[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x34 = r114[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
    r114[0U] = x04;
    r114[1U] = x14;
    r114[2U] = x24;
    r114[3U] = x34;
    uint32_t *r115 = r3;
    uint32_t x0 = r115[1U];
    uint32_t x1 = r115[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
    uint32_t x2 = r115[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
    uint32_t x3 = r115[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
    r115[0U] = x0;
    r115[1U] = x1;
    r115[2U] = x2;
    r115[3U] = x3;
  }
  uint32_t *s0 = hash + (uint32_t)0U * (uint32_t)4U;
  uint32_t *s1 = hash + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r0 = wv + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = wv + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = wv + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = wv + (uint32_t)3U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r0[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s0;
    uint32_t x = s0[i] ^ r2[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r1[i];
    os[i] = x;
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint32_t *os = s1;
    uint32_t x = s1[i] ^ r3[i];
    os[i] = x;
  }
}

inline void Hacl_Blake2s_32_blake2s_init(uint32_t *hash, uint32_t kk, uint32_t nn)
{
  uint32_t *r0 = hash + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = hash + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = hash + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = hash + (uint32_t)3U * (uint32_t)4U;
  uint32_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
  uint32_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
  uint32_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
  uint32_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
  uint32_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
  uint32_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
  uint32_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
  uint32_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
  r2[0U] = iv0;
  r2[1U] = iv1;
  r2[2U] = iv2;
  r2[3U] = iv3;
  r3[0U] = iv4;
  r3[1U] = iv5;
  r3[2U] = iv6;
  r3[3U] = iv7;
  uint32_t kk_shift_8 = kk << (uint32_t)8U;
  uint32_t iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ nn));
  r0[0U] = iv0_;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
}

inline void
Hacl_Blake2s_32_blake2s_update_key(
  uint32_t *wv,
  uint32_t *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t ll
)
{
  uint64_t lb = (uint64_t)(uint32_t)64U;
  uint8_t b[64U] = { 0U };
  memcpy(b, k, kk * sizeof (uint8_t));
  if (ll == (uint32_t)0U)
  {
    blake2s_update_block(wv, hash, true, lb, b);
  }
  else
  {
    blake2s_update_block(wv, hash, false, lb, b);
  }
  Lib_Memzero0_memzero(b, (uint32_t)64U * sizeof (b[0U]));
}

inline void
Hacl_Blake2s_32_blake2s_update_multi(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint8_t *blocks,
  uint32_t nb
)
{
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint64_t totlen = prev + (uint64_t)((i + (uint32_t)1U) * (uint32_t)64U);
    uint8_t *b = blocks + i * (uint32_t)64U;
    blake2s_update_block(wv, hash, false, totlen, b);
  }
}

inline void
Hacl_Blake2s_32_blake2s_update_last(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint32_t rem,
  uint8_t *d
)
{
  uint8_t b[64U] = { 0U };
  uint8_t *last = d + len - rem;
  memcpy(b, last, rem * sizeof (uint8_t));
  uint64_t totlen = prev + (uint64_t)len;
  blake2s_update_block(wv, hash, true, totlen, b);
  Lib_Memzero0_memzero(b, (uint32_t)64U * sizeof (b[0U]));
}

static inline void
blake2s_update_blocks(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint8_t *blocks
)
{
  uint32_t nb0 = len / (uint32_t)64U;
  uint32_t rem0 = len % (uint32_t)64U;
  K___uint32_t_uint32_t scrut;
  if (rem0 == (uint32_t)0U && nb0 > (uint32_t)0U)
  {
    uint32_t nb_ = nb0 - (uint32_t)1U;
    uint32_t rem_ = (uint32_t)64U;
    scrut = ((K___uint32_t_uint32_t){ .fst = nb_, .snd = rem_ });
  }
  else
  {
    scrut = ((K___uint32_t_uint32_t){ .fst = nb0, .snd = rem0 });
  }
  uint32_t nb = scrut.fst;
  uint32_t rem = scrut.snd;
  Hacl_Blake2s_32_blake2s_update_multi(len, wv, hash, prev, blocks, nb);
  Hacl_Blake2s_32_blake2s_update_last(len, wv, hash, prev, rem, blocks);
}

static inline void
blake2s_update(uint32_t *wv, uint32_t *hash, uint32_t kk, uint8_t *k, uint32_t ll, uint8_t *d)
{
  uint64_t lb = (uint64_t)(uint32_t)64U;
  if (kk > (uint32_t)0U)
  {
    Hacl_Blake2s_32_blake2s_update_key(wv, hash, kk, k, ll);
    if (!(ll == (uint32_t)0U))
    {
      blake2s_update_blocks(ll, wv, hash, lb, d);
      return;
    }
    return;
  }
  blake2s_update_blocks(ll, wv, hash, (uint64_t)(uint32_t)0U, d);
}

inline void Hacl_Blake2s_32_blake2s_finish(uint32_t nn, uint8_t *output, uint32_t *hash)
{
  uint32_t double_row = (uint32_t)2U * ((uint32_t)4U * (uint32_t)4U);
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)4U;
  uint32_t *row0 = hash + (uint32_t)0U * (uint32_t)4U;
  uint32_t *row1 = hash + (uint32_t)1U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store32_le(first + i * (uint32_t)4U, row0[i]);
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    store32_le(second + i * (uint32_t)4U, row1[i]);
  }
  uint8_t *final = b;
  memcpy(output, final, nn * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, double_row * sizeof (b[0U]));
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
  uint32_t b[stlen];
  for (uint32_t _i = 0U; _i < stlen; ++_i)
    b[_i] = stzero;
  KRML_CHECK_SIZE(sizeof (uint32_t), stlen);
  uint32_t b1[stlen];
  for (uint32_t _i = 0U; _i < stlen; ++_i)
    b1[_i] = stzero;
  Hacl_Blake2s_32_blake2s_init(b, kk, nn);
  blake2s_update(b1, b, kk, k, ll, d);
  Hacl_Blake2s_32_blake2s_finish(nn, output, b);
  Lib_Memzero0_memzero(b1, stlen * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, stlen * sizeof (b[0U]));
}

