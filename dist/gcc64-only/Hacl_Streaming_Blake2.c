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


#include "Hacl_Streaming_Blake2.h"

typedef struct Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t_____s
{
  K____uint32_t___uint32_t_ block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____;

/*
  State allocation function when there is no key
*/
Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
*Hacl_Streaming_Blake2_blake2s_32_no_key_create_in()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  uint32_t *wv = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
  uint32_t *b0 = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
  K____uint32_t___uint32_t_ block_state = { .fst = wv, .snd = b0 };
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
  s1 = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____));
  p[0U] = s1;
  uint8_t b[64U] = { 0U };
  uint32_t *r0 = block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = block_state.snd + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = block_state.snd + (uint32_t)3U * (uint32_t)4U;
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
  uint32_t kk_shift_8 = (uint32_t)0U;
  uint32_t iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
  r0[0U] = iv0_;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
  Lib_Memzero0_memzero(b, (uint32_t)64U * sizeof (b[0U]));
  return p;
}

/*
  Update function when there is no key
*/
void
Hacl_Streaming_Blake2_blake2s_32_no_key_update(
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s1 = *p;
  uint64_t total_len = s1.total_len;
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
    Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s2 = *p;
    K____uint32_t___uint32_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s2 = *p;
    K____uint32_t___uint32_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
    uint32_t sz1;
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
      for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
        uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
        uint8_t *b = buf + i0 * (uint32_t)64U;
        uint32_t m_w[16U] = { 0U };
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
        {
          uint32_t *os = m_w;
          uint8_t *bj = b + i * (uint32_t)4U;
          uint32_t u = load32_le(bj);
          uint32_t r = u;
          uint32_t x = r;
          os[i] = x;
        }
        uint32_t mask[4U] = { 0U };
        uint32_t wv_14 = (uint32_t)0U;
        uint32_t wv_15 = (uint32_t)0U;
        mask[0U] = (uint32_t)totlen;
        mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
        mask[2U] = wv_14;
        mask[3U] = wv_15;
        memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
        uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv3;
          uint32_t x = wv3[i] ^ mask[i];
          os[i] = x;
        }
        for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
        {
          uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
          uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
          memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
          uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
          uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
          uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
          uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
          uint32_t uu____0 = m_w[s21];
          uint32_t uu____1 = m_w[s4];
          uint32_t uu____2 = m_w[s6];
          r0[0U] = m_w[s0];
          r0[1U] = uu____0;
          r0[2U] = uu____1;
          r0[3U] = uu____2;
          uint32_t uu____3 = m_w[s3];
          uint32_t uu____4 = m_w[s5];
          uint32_t uu____5 = m_w[s7];
          r1[0U] = m_w[s11];
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
          uint32_t uu____9 = m_w[s111];
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
          uint32_t b10 = (uint32_t)1U;
          uint32_t c0 = (uint32_t)2U;
          uint32_t d0 = (uint32_t)3U;
          uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
          uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
          uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
          uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
          uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a2;
            uint32_t x1 = wv_a2[i] + wv_b2[i];
            os[i] = x1;
          }
          uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
          uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
          uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
          uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
          uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
          uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a6;
            uint32_t x1 = wv_a6[i] + wv_b6[i];
            os[i] = x1;
          }
          uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
          uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t b1 = (uint32_t)1U;
          uint32_t c = (uint32_t)2U;
          uint32_t d = (uint32_t)3U;
          uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
          uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
          uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
          uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a9;
            uint32_t x1 = wv_a9[i] + wv_b10[i];
            os[i] = x1;
          }
          uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
          uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
          uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
          uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
          uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
          uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a13;
            uint32_t x1 = wv_a13[i] + wv_b14[i];
            os[i] = x1;
          }
          uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
          uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
          uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
        uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
        uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t *os = s11;
          uint32_t x = s11[i] ^ r1[i];
          os[i] = x;
        }
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = s11;
          uint32_t x = s11[i] ^ r3[i];
          os[i] = x;
        }
      }
    }
    uint32_t ite0;
    if ((uint64_t)len % (uint64_t)(uint32_t)64U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite0 = (uint32_t)64U;
    }
    else
    {
      ite0 = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)64U);
    }
    uint32_t n_blocks = (len - ite0) / (uint32_t)64U;
    uint32_t data1_len = n_blocks * (uint32_t)64U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    uint32_t nb = data1_len / (uint32_t)64U;
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
      uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
      uint8_t *b = data1 + i0 * (uint32_t)64U;
      uint32_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      uint32_t mask[4U] = { 0U };
      uint32_t wv_14 = (uint32_t)0U;
      uint32_t wv_15 = (uint32_t)0U;
      mask[0U] = (uint32_t)totlen;
      mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
      uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv3;
        uint32_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
        uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
        uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint32_t uu____12 = m_w[s21];
        uint32_t uu____13 = m_w[s4];
        uint32_t uu____14 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____12;
        r0[2U] = uu____13;
        r0[3U] = uu____14;
        uint32_t uu____15 = m_w[s3];
        uint32_t uu____16 = m_w[s5];
        uint32_t uu____17 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____15;
        r1[2U] = uu____16;
        r1[3U] = uu____17;
        uint32_t uu____18 = m_w[s10];
        uint32_t uu____19 = m_w[s12];
        uint32_t uu____20 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____18;
        r20[2U] = uu____19;
        r20[3U] = uu____20;
        uint32_t uu____21 = m_w[s111];
        uint32_t uu____22 = m_w[s13];
        uint32_t uu____23 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____21;
        r30[2U] = uu____22;
        r30[3U] = uu____23;
        uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a2;
          uint32_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a6;
          uint32_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a9;
          uint32_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a13;
          uint32_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)64U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s2 = *p;
  K____uint32_t___uint32_t_ block_state10 = s2.block_state;
  uint8_t *buf0 = s2.buf;
  uint64_t total_len10 = s2.total_len;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)64U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)64U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s20 = *p;
  K____uint32_t___uint32_t_ block_state1 = s20.block_state;
  uint8_t *buf = s20.buf;
  uint64_t total_len1 = s20.total_len;
  uint32_t sz1;
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
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
      uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
      uint8_t *b = buf + i0 * (uint32_t)64U;
      uint32_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      uint32_t mask[4U] = { 0U };
      uint32_t wv_14 = (uint32_t)0U;
      uint32_t wv_15 = (uint32_t)0U;
      mask[0U] = (uint32_t)totlen;
      mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
      uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv3;
        uint32_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
        uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
        uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint32_t uu____24 = m_w[s21];
        uint32_t uu____25 = m_w[s4];
        uint32_t uu____26 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____24;
        r0[2U] = uu____25;
        r0[3U] = uu____26;
        uint32_t uu____27 = m_w[s3];
        uint32_t uu____28 = m_w[s5];
        uint32_t uu____29 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____27;
        r1[2U] = uu____28;
        r1[3U] = uu____29;
        uint32_t uu____30 = m_w[s10];
        uint32_t uu____31 = m_w[s12];
        uint32_t uu____32 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____30;
        r20[2U] = uu____31;
        r20[3U] = uu____32;
        uint32_t uu____33 = m_w[s111];
        uint32_t uu____34 = m_w[s13];
        uint32_t uu____35 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____33;
        r30[2U] = uu____34;
        r30[3U] = uu____35;
        uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a2;
          uint32_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a6;
          uint32_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a9;
          uint32_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a13;
          uint32_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
    }
  }
  uint32_t ite0;
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
  uint32_t n_blocks = (len - diff - ite0) / (uint32_t)64U;
  uint32_t data1_len = n_blocks * (uint32_t)64U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  uint32_t nb = data1_len / (uint32_t)64U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
    uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
    uint8_t *b = data11 + i0 * (uint32_t)64U;
    uint32_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t *os = m_w;
      uint8_t *bj = b + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
    uint32_t mask[4U] = { 0U };
    uint32_t wv_14 = (uint32_t)0U;
    uint32_t wv_15 = (uint32_t)0U;
    mask[0U] = (uint32_t)totlen;
    mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
    uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv3;
      uint32_t x = wv3[i] ^ mask[i];
      os[i] = x;
    }
    for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
    {
      uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
      uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
      memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
      uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
      uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
      uint32_t uu____36 = m_w[s21];
      uint32_t uu____37 = m_w[s4];
      uint32_t uu____38 = m_w[s6];
      r0[0U] = m_w[s0];
      r0[1U] = uu____36;
      r0[2U] = uu____37;
      r0[3U] = uu____38;
      uint32_t uu____39 = m_w[s3];
      uint32_t uu____40 = m_w[s5];
      uint32_t uu____41 = m_w[s7];
      r1[0U] = m_w[s11];
      r1[1U] = uu____39;
      r1[2U] = uu____40;
      r1[3U] = uu____41;
      uint32_t uu____42 = m_w[s10];
      uint32_t uu____43 = m_w[s12];
      uint32_t uu____44 = m_w[s14];
      r20[0U] = m_w[s8];
      r20[1U] = uu____42;
      r20[2U] = uu____43;
      r20[3U] = uu____44;
      uint32_t uu____45 = m_w[s111];
      uint32_t uu____46 = m_w[s13];
      uint32_t uu____47 = m_w[s15];
      r30[0U] = m_w[s9];
      r30[1U] = uu____45;
      r30[2U] = uu____46;
      r30[3U] = uu____47;
      uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
      uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
      uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
      uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t a = (uint32_t)0U;
      uint32_t b10 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
      uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
      uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
      uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
      uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a2;
        uint32_t x1 = wv_a2[i] + wv_b2[i];
        os[i] = x1;
      }
      uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
      uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
      uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
      uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
      uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
      uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a6;
        uint32_t x1 = wv_a6[i] + wv_b6[i];
        os[i] = x1;
      }
      uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
      uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t b1 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
      uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
      uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
      uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a9;
        uint32_t x1 = wv_a9[i] + wv_b10[i];
        os[i] = x1;
      }
      uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
      uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
      uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
      uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
      uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
      uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a13;
        uint32_t x1 = wv_a13[i] + wv_b14[i];
        os[i] = x1;
      }
      uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
      uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
      uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
    uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *os = s11;
      uint32_t x = s11[i] ^ r1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = s11;
      uint32_t x = s11[i] ^ r3[i];
      os[i] = x;
    }
  }
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
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
Hacl_Streaming_Blake2_blake2s_32_no_key_finish(
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ scrut = *p;
  K____uint32_t___uint32_t_ block_state = scrut.block_state;
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
  uint8_t *buf_1 = buf_;
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t b0[(uint32_t)4U * (uint32_t)4U];
  memset(b0, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  K____uint32_t___uint32_t_ tmp_block_state = { .fst = wv, .snd = b0 };
  uint32_t *src_b = block_state.snd;
  uint32_t *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)16U * sizeof (uint32_t));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint8_t b2[64U] = { 0U };
  uint8_t *last = buf_1 + r - r;
  memcpy(b2, last, r * sizeof (uint8_t));
  uint64_t ite;
  if ((uint32_t)0U == (uint32_t)0U)
  {
    ite = prev_len;
  }
  else
  {
    ite = prev_len + (uint64_t)(uint32_t)64U;
  }
  uint64_t totlen = ite + (uint64_t)r;
  uint32_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = m_w;
    uint8_t *bj = b2 + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r1 = u;
    uint32_t x = r1;
    os[i] = x;
  }
  uint32_t mask[4U] = { 0U };
  uint32_t wv_14 = (uint32_t)0xFFFFFFFFU;
  uint32_t wv_15 = (uint32_t)0U;
  mask[0U] = (uint32_t)totlen;
  mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(tmp_block_state.fst,
    tmp_block_state.snd,
    (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  uint32_t *wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b10 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint32_t *wv_a0 = tmp_block_state.fst + a * (uint32_t)4U;
    uint32_t *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint32_t *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint32_t *wv_b1 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint32_t *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint32_t *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a2;
      uint32_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint32_t *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint32_t *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint32_t *wv_a4 = tmp_block_state.fst + a * (uint32_t)4U;
    uint32_t *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint32_t *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint32_t *wv_b5 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint32_t *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint32_t *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a6;
      uint32_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint32_t *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint32_t *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint32_t *r15 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r21 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r31 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b1 = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint32_t *wv_a = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint32_t *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint32_t *wv_a8 = tmp_block_state.fst + d * (uint32_t)4U;
    uint32_t *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint32_t *wv_a9 = tmp_block_state.fst + c * (uint32_t)4U;
    uint32_t *wv_b10 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a9;
      uint32_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint32_t *wv_a10 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint32_t *wv_b11 = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint32_t *wv_a11 = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint32_t *wv_b12 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint32_t *wv_a12 = tmp_block_state.fst + d * (uint32_t)4U;
    uint32_t *wv_b13 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint32_t *wv_a13 = tmp_block_state.fst + c * (uint32_t)4U;
    uint32_t *wv_b14 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a13;
      uint32_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint32_t *wv_a14 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint32_t *wv_b = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint32_t *r113 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  uint32_t *s0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint32_t *s1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r0 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  Lib_Memzero0_memzero(b2, (uint32_t)64U * sizeof (b2[0U]));
  uint32_t double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)4U;
  uint32_t *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint32_t *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
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

/*
  Free state function when there is no key
*/
void
Hacl_Streaming_Blake2_blake2s_32_no_key_free(
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ *s1
)
{
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ scrut = *s1;
  uint8_t *buf = scrut.buf;
  K____uint32_t___uint32_t_ block_state = scrut.block_state;
  uint32_t *wv = block_state.fst;
  uint32_t *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s1);
}

typedef struct Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t_____s
{
  K____uint64_t___uint64_t_ block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____;

/*
  State allocation function when there is no key
*/
Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
*Hacl_Streaming_Blake2_blake2b_32_no_key_create_in()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  uint64_t *wv = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
  uint64_t *b0 = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
  K____uint64_t___uint64_t_ block_state = { .fst = wv, .snd = b0 };
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
  s1 = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____));
  p[0U] = s1;
  uint8_t b[128U] = { 0U };
  uint64_t *r0 = block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = block_state.snd + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = block_state.snd + (uint32_t)3U * (uint32_t)4U;
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
  uint64_t kk_shift_8 = (uint64_t)(uint32_t)0U << (uint32_t)8U;
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r0[0U] = iv0_;
  r0[1U] = iv1;
  r0[2U] = iv2;
  r0[3U] = iv3;
  r1[0U] = iv4;
  r1[1U] = iv5;
  r1[2U] = iv6;
  r1[3U] = iv7;
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
  return p;
}

/*
  Update function when there is no key
*/
void
Hacl_Streaming_Blake2_blake2b_32_no_key_update(
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s1 = *p;
  uint64_t total_len = s1.total_len;
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
    Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s2 = *p;
    K____uint64_t___uint64_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
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
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s2 = *p;
    K____uint64_t___uint64_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
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
        uint64_t mask[4U] = { 0U };
        uint64_t wv_14 = (uint64_t)0U;
        uint64_t wv_15 = (uint64_t)0U;
        mask[0U] = (uint64_t)totlen;
        mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
        mask[2U] = wv_14;
        mask[3U] = wv_15;
        memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
        uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv3;
          uint64_t x = wv3[i] ^ mask[i];
          os[i] = x;
        }
        for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
        {
          uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
          uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
          memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
          uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
          uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
          uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
          uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
          uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
          uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
          uint64_t uu____0 = m_w[s21];
          uint64_t uu____1 = m_w[s4];
          uint64_t uu____2 = m_w[s6];
          r0[0U] = m_w[s0];
          r0[1U] = uu____0;
          r0[2U] = uu____1;
          r0[3U] = uu____2;
          uint64_t uu____3 = m_w[s3];
          uint64_t uu____4 = m_w[s5];
          uint64_t uu____5 = m_w[s7];
          r1[0U] = m_w[s11];
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
          uint64_t uu____9 = m_w[s111];
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
          uint32_t b10 = (uint32_t)1U;
          uint32_t c0 = (uint32_t)2U;
          uint32_t d0 = (uint32_t)3U;
          uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
          uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
          uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
          uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
          uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a2;
            uint64_t x1 = wv_a2[i] + wv_b2[i];
            os[i] = x1;
          }
          uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
          uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
          uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
          uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
          uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
          uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a6;
            uint64_t x1 = wv_a6[i] + wv_b6[i];
            os[i] = x1;
          }
          uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
          uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t b1 = (uint32_t)1U;
          uint32_t c = (uint32_t)2U;
          uint32_t d = (uint32_t)3U;
          uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
          uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
          uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
          uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a9;
            uint64_t x1 = wv_a9[i] + wv_b10[i];
            os[i] = x1;
          }
          uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
          uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
          uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
          uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
          uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
          uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a13;
            uint64_t x1 = wv_a13[i] + wv_b14[i];
            os[i] = x1;
          }
          uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
          uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
          uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
        uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
        uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint64_t *os = s11;
          uint64_t x = s11[i] ^ r1[i];
          os[i] = x;
        }
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = s11;
          uint64_t x = s11[i] ^ r3[i];
          os[i] = x;
        }
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
      uint64_t mask[4U] = { 0U };
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask[0U] = (uint64_t)totlen;
      mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
      uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv3;
        uint64_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
        uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
        uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint64_t uu____12 = m_w[s21];
        uint64_t uu____13 = m_w[s4];
        uint64_t uu____14 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____12;
        r0[2U] = uu____13;
        r0[3U] = uu____14;
        uint64_t uu____15 = m_w[s3];
        uint64_t uu____16 = m_w[s5];
        uint64_t uu____17 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____15;
        r1[2U] = uu____16;
        r1[3U] = uu____17;
        uint64_t uu____18 = m_w[s10];
        uint64_t uu____19 = m_w[s12];
        uint64_t uu____20 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____18;
        r20[2U] = uu____19;
        r20[3U] = uu____20;
        uint64_t uu____21 = m_w[s111];
        uint64_t uu____22 = m_w[s13];
        uint64_t uu____23 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____21;
        r30[2U] = uu____22;
        r30[3U] = uu____23;
        uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a2;
          uint64_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a6;
          uint64_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a9;
          uint64_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a13;
          uint64_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
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
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s2 = *p;
  K____uint64_t___uint64_t_ block_state10 = s2.block_state;
  uint8_t *buf0 = s2.buf;
  uint64_t total_len10 = s2.total_len;
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
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s20 = *p;
  K____uint64_t___uint64_t_ block_state1 = s20.block_state;
  uint8_t *buf = s20.buf;
  uint64_t total_len1 = s20.total_len;
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
      uint64_t mask[4U] = { 0U };
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask[0U] = (uint64_t)totlen;
      mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
      uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv3;
        uint64_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
        uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
        uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint64_t uu____24 = m_w[s21];
        uint64_t uu____25 = m_w[s4];
        uint64_t uu____26 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____24;
        r0[2U] = uu____25;
        r0[3U] = uu____26;
        uint64_t uu____27 = m_w[s3];
        uint64_t uu____28 = m_w[s5];
        uint64_t uu____29 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____27;
        r1[2U] = uu____28;
        r1[3U] = uu____29;
        uint64_t uu____30 = m_w[s10];
        uint64_t uu____31 = m_w[s12];
        uint64_t uu____32 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____30;
        r20[2U] = uu____31;
        r20[3U] = uu____32;
        uint64_t uu____33 = m_w[s111];
        uint64_t uu____34 = m_w[s13];
        uint64_t uu____35 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____33;
        r30[2U] = uu____34;
        r30[3U] = uu____35;
        uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a2;
          uint64_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a6;
          uint64_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a9;
          uint64_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a13;
          uint64_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
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
    uint64_t mask[4U] = { 0U };
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask[0U] = (uint64_t)totlen;
    mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
    uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv3;
      uint64_t x = wv3[i] ^ mask[i];
      os[i] = x;
    }
    for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
    {
      uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
      uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
      memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
      uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
      uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
      uint64_t uu____36 = m_w[s21];
      uint64_t uu____37 = m_w[s4];
      uint64_t uu____38 = m_w[s6];
      r0[0U] = m_w[s0];
      r0[1U] = uu____36;
      r0[2U] = uu____37;
      r0[3U] = uu____38;
      uint64_t uu____39 = m_w[s3];
      uint64_t uu____40 = m_w[s5];
      uint64_t uu____41 = m_w[s7];
      r1[0U] = m_w[s11];
      r1[1U] = uu____39;
      r1[2U] = uu____40;
      r1[3U] = uu____41;
      uint64_t uu____42 = m_w[s10];
      uint64_t uu____43 = m_w[s12];
      uint64_t uu____44 = m_w[s14];
      r20[0U] = m_w[s8];
      r20[1U] = uu____42;
      r20[2U] = uu____43;
      r20[3U] = uu____44;
      uint64_t uu____45 = m_w[s111];
      uint64_t uu____46 = m_w[s13];
      uint64_t uu____47 = m_w[s15];
      r30[0U] = m_w[s9];
      r30[1U] = uu____45;
      r30[2U] = uu____46;
      r30[3U] = uu____47;
      uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
      uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
      uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
      uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t a = (uint32_t)0U;
      uint32_t b10 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
      uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
      uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
      uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
      uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a2;
        uint64_t x1 = wv_a2[i] + wv_b2[i];
        os[i] = x1;
      }
      uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
      uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
      uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
      uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
      uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
      uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a6;
        uint64_t x1 = wv_a6[i] + wv_b6[i];
        os[i] = x1;
      }
      uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
      uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t b1 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
      uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
      uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
      uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a9;
        uint64_t x1 = wv_a9[i] + wv_b10[i];
        os[i] = x1;
      }
      uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
      uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
      uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
      uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
      uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
      uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a13;
        uint64_t x1 = wv_a13[i] + wv_b14[i];
        os[i] = x1;
      }
      uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
      uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
      uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
    uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *os = s11;
      uint64_t x = s11[i] ^ r1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = s11;
      uint64_t x = s11[i] ^ r3[i];
      os[i] = x;
    }
  }
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
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
Hacl_Streaming_Blake2_blake2b_32_no_key_finish(
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ scrut = *p;
  K____uint64_t___uint64_t_ block_state = scrut.block_state;
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
  uint64_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
  uint64_t b0[(uint32_t)4U * (uint32_t)4U];
  memset(b0, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  K____uint64_t___uint64_t_ tmp_block_state = { .fst = wv, .snd = b0 };
  uint64_t *src_b = block_state.snd;
  uint64_t *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)16U * sizeof (uint64_t));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint8_t b2[128U] = { 0U };
  uint8_t *last = buf_1 + r - r;
  memcpy(b2, last, r * sizeof (uint8_t));
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
  uint64_t mask[4U] = { 0U };
  uint64_t wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t wv_15 = (uint64_t)0U;
  mask[0U] = (uint64_t)totlen;
  mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(tmp_block_state.fst,
    tmp_block_state.snd,
    (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  uint64_t *wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b10 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint64_t *wv_a0 = tmp_block_state.fst + a * (uint32_t)4U;
    uint64_t *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint64_t *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint64_t *wv_b1 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint64_t *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint64_t *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a2;
      uint64_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint64_t *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint64_t *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint64_t *wv_a4 = tmp_block_state.fst + a * (uint32_t)4U;
    uint64_t *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint64_t *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint64_t *wv_b5 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint64_t *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint64_t *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a6;
      uint64_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint64_t *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint64_t *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint64_t *r15 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r21 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r31 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b1 = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint64_t *wv_a = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint64_t *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint64_t *wv_a8 = tmp_block_state.fst + d * (uint32_t)4U;
    uint64_t *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint64_t *wv_a9 = tmp_block_state.fst + c * (uint32_t)4U;
    uint64_t *wv_b10 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a9;
      uint64_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint64_t *wv_a10 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint64_t *wv_b11 = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint64_t *wv_a11 = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint64_t *wv_b12 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint64_t *wv_a12 = tmp_block_state.fst + d * (uint32_t)4U;
    uint64_t *wv_b13 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint64_t *wv_a13 = tmp_block_state.fst + c * (uint32_t)4U;
    uint64_t *wv_b14 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a13;
      uint64_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint64_t *wv_a14 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint64_t *wv_b = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint64_t *r113 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  uint64_t *s0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint64_t *s1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r0 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  Lib_Memzero0_memzero(b2, (uint32_t)128U * sizeof (b2[0U]));
  uint32_t double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)8U;
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
  uint64_t *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint64_t *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
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

/*
  Free state function when there is no key
*/
void
Hacl_Streaming_Blake2_blake2b_32_no_key_free(
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ *s1
)
{
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ scrut = *s1;
  uint8_t *buf = scrut.buf;
  K____uint64_t___uint64_t_ block_state = scrut.block_state;
  uint64_t *wv = block_state.fst;
  uint64_t *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s1);
}

/*
  State allocation function when using a (potentially null) key
*/
Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
*Hacl_Streaming_Blake2_blake2s_32_with_key_create_in(uint32_t key_size, uint8_t *k1)
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  uint32_t *wv = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
  uint32_t *b0 = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
  K____uint32_t___uint32_t_ block_state = { .fst = wv, .snd = b0 };
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
  s1 = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____));
  p[0U] = s1;
  uint8_t b[64U] = { 0U };
  uint32_t *r00 = block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r10 = block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r20 = block_state.snd + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r30 = block_state.snd + (uint32_t)3U * (uint32_t)4U;
  uint32_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_S[0U];
  uint32_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_S[1U];
  uint32_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_S[2U];
  uint32_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_S[3U];
  uint32_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_S[4U];
  uint32_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_S[5U];
  uint32_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_S[6U];
  uint32_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_S[7U];
  r20[0U] = iv0;
  r20[1U] = iv1;
  r20[2U] = iv2;
  r20[3U] = iv3;
  r30[0U] = iv4;
  r30[1U] = iv5;
  r30[2U] = iv6;
  r30[3U] = iv7;
  uint32_t kk_shift_8 = key_size << (uint32_t)8U;
  uint32_t iv0_ = iv0 ^ ((uint32_t)0x01010000U ^ (kk_shift_8 ^ (uint32_t)32U));
  r00[0U] = iv0_;
  r00[1U] = iv1;
  r00[2U] = iv2;
  r00[3U] = iv3;
  r10[0U] = iv4;
  r10[1U] = iv5;
  r10[2U] = iv6;
  r10[3U] = iv7;
  if (!(key_size == (uint32_t)0U))
  {
    memcpy(b, k1, key_size * sizeof (uint8_t));
    uint64_t totlen = (uint64_t)(uint32_t)0U + (uint64_t)(uint32_t)64U;
    uint8_t *b1 = b + (uint32_t)0U * (uint32_t)64U;
    uint32_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t *os = m_w;
      uint8_t *bj = b1 + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r1 = u;
      uint32_t x = r1;
      os[i] = x;
    }
    uint32_t mask[4U] = { 0U };
    uint32_t wv_14 = (uint32_t)0U;
    uint32_t wv_15 = (uint32_t)0U;
    mask[0U] = (uint32_t)totlen;
    mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(block_state.fst, block_state.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
    uint32_t *wv3 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *r21 = m_st + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r31 = m_st + (uint32_t)3U * (uint32_t)4U;
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
      r1[0U] = m_w[s11];
      r1[1U] = uu____3;
      r1[2U] = uu____4;
      r1[3U] = uu____5;
      uint32_t uu____6 = m_w[s10];
      uint32_t uu____7 = m_w[s12];
      uint32_t uu____8 = m_w[s14];
      r21[0U] = m_w[s8];
      r21[1U] = uu____6;
      r21[2U] = uu____7;
      r21[3U] = uu____8;
      uint32_t uu____9 = m_w[s111];
      uint32_t uu____10 = m_w[s13];
      uint32_t uu____11 = m_w[s15];
      r31[0U] = m_w[s9];
      r31[1U] = uu____9;
      r31[2U] = uu____10;
      r31[3U] = uu____11;
      uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
      uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
      uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
      uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t a = (uint32_t)0U;
      uint32_t b20 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t *wv_a0 = block_state.fst + a * (uint32_t)4U;
      uint32_t *wv_b0 = block_state.fst + b20 * (uint32_t)4U;
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
      uint32_t *wv_a1 = block_state.fst + d0 * (uint32_t)4U;
      uint32_t *wv_b1 = block_state.fst + a * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a1;
        uint32_t x1 = wv_a1[i] ^ wv_b1[i];
        os[i] = x1;
      }
      uint32_t *r12 = wv_a1;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r12;
        uint32_t x1 = r12[i];
        uint32_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
        os[i] = x10;
      }
      uint32_t *wv_a2 = block_state.fst + c0 * (uint32_t)4U;
      uint32_t *wv_b2 = block_state.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a2;
        uint32_t x1 = wv_a2[i] + wv_b2[i];
        os[i] = x1;
      }
      uint32_t *wv_a3 = block_state.fst + b20 * (uint32_t)4U;
      uint32_t *wv_b3 = block_state.fst + c0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a3;
        uint32_t x1 = wv_a3[i] ^ wv_b3[i];
        os[i] = x1;
      }
      uint32_t *r13 = wv_a3;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r13;
        uint32_t x1 = r13[i];
        uint32_t x10 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
        os[i] = x10;
      }
      uint32_t *wv_a4 = block_state.fst + a * (uint32_t)4U;
      uint32_t *wv_b4 = block_state.fst + b20 * (uint32_t)4U;
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
      uint32_t *wv_a5 = block_state.fst + d0 * (uint32_t)4U;
      uint32_t *wv_b5 = block_state.fst + a * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a5;
        uint32_t x1 = wv_a5[i] ^ wv_b5[i];
        os[i] = x1;
      }
      uint32_t *r14 = wv_a5;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r14;
        uint32_t x1 = r14[i];
        uint32_t x10 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
        os[i] = x10;
      }
      uint32_t *wv_a6 = block_state.fst + c0 * (uint32_t)4U;
      uint32_t *wv_b6 = block_state.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a6;
        uint32_t x1 = wv_a6[i] + wv_b6[i];
        os[i] = x1;
      }
      uint32_t *wv_a7 = block_state.fst + b20 * (uint32_t)4U;
      uint32_t *wv_b7 = block_state.fst + c0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a7;
        uint32_t x1 = wv_a7[i] ^ wv_b7[i];
        os[i] = x1;
      }
      uint32_t *r15 = wv_a7;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r15;
        uint32_t x1 = r15[i];
        uint32_t x10 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
        os[i] = x10;
      }
      uint32_t *r16 = block_state.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r22 = block_state.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r32 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
      uint32_t *r110 = r16;
      uint32_t x00 = r110[1U];
      uint32_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
      uint32_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
      uint32_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
      r110[0U] = x00;
      r110[1U] = x10;
      r110[2U] = x20;
      r110[3U] = x30;
      uint32_t *r111 = r22;
      uint32_t x01 = r111[2U];
      uint32_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
      uint32_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
      uint32_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
      r111[0U] = x01;
      r111[1U] = x11;
      r111[2U] = x21;
      r111[3U] = x31;
      uint32_t *r112 = r32;
      uint32_t x02 = r112[3U];
      uint32_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
      uint32_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
      uint32_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
      r112[0U] = x02;
      r112[1U] = x12;
      r112[2U] = x22;
      r112[3U] = x32;
      uint32_t a0 = (uint32_t)0U;
      uint32_t b2 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t *wv_a = block_state.fst + a0 * (uint32_t)4U;
      uint32_t *wv_b8 = block_state.fst + b2 * (uint32_t)4U;
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
      uint32_t *wv_a8 = block_state.fst + d * (uint32_t)4U;
      uint32_t *wv_b9 = block_state.fst + a0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a8;
        uint32_t x1 = wv_a8[i] ^ wv_b9[i];
        os[i] = x1;
      }
      uint32_t *r17 = wv_a8;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r17;
        uint32_t x1 = r17[i];
        uint32_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)16U;
        os[i] = x13;
      }
      uint32_t *wv_a9 = block_state.fst + c * (uint32_t)4U;
      uint32_t *wv_b10 = block_state.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a9;
        uint32_t x1 = wv_a9[i] + wv_b10[i];
        os[i] = x1;
      }
      uint32_t *wv_a10 = block_state.fst + b2 * (uint32_t)4U;
      uint32_t *wv_b11 = block_state.fst + c * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a10;
        uint32_t x1 = wv_a10[i] ^ wv_b11[i];
        os[i] = x1;
      }
      uint32_t *r18 = wv_a10;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r18;
        uint32_t x1 = r18[i];
        uint32_t x13 = x1 >> (uint32_t)12U | x1 << (uint32_t)20U;
        os[i] = x13;
      }
      uint32_t *wv_a11 = block_state.fst + a0 * (uint32_t)4U;
      uint32_t *wv_b12 = block_state.fst + b2 * (uint32_t)4U;
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
      uint32_t *wv_a12 = block_state.fst + d * (uint32_t)4U;
      uint32_t *wv_b13 = block_state.fst + a0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a12;
        uint32_t x1 = wv_a12[i] ^ wv_b13[i];
        os[i] = x1;
      }
      uint32_t *r19 = wv_a12;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r19;
        uint32_t x1 = r19[i];
        uint32_t x13 = x1 >> (uint32_t)8U | x1 << (uint32_t)24U;
        os[i] = x13;
      }
      uint32_t *wv_a13 = block_state.fst + c * (uint32_t)4U;
      uint32_t *wv_b14 = block_state.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a13;
        uint32_t x1 = wv_a13[i] + wv_b14[i];
        os[i] = x1;
      }
      uint32_t *wv_a14 = block_state.fst + b2 * (uint32_t)4U;
      uint32_t *wv_b = block_state.fst + c * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a14;
        uint32_t x1 = wv_a14[i] ^ wv_b[i];
        os[i] = x1;
      }
      uint32_t *r113 = wv_a14;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = r113;
        uint32_t x1 = r113[i];
        uint32_t x13 = x1 >> (uint32_t)7U | x1 << (uint32_t)25U;
        os[i] = x13;
      }
      uint32_t *r114 = block_state.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
      uint32_t *r11 = r114;
      uint32_t x03 = r11[3U];
      uint32_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
      uint32_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
      uint32_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
      r11[0U] = x03;
      r11[1U] = x13;
      r11[2U] = x23;
      r11[3U] = x33;
      uint32_t *r115 = r2;
      uint32_t x04 = r115[2U];
      uint32_t x14 = r115[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
      uint32_t x24 = r115[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
      uint32_t x34 = r115[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
      r115[0U] = x04;
      r115[1U] = x14;
      r115[2U] = x24;
      r115[3U] = x34;
      uint32_t *r116 = r3;
      uint32_t x0 = r116[1U];
      uint32_t x1 = r116[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
      uint32_t x2 = r116[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
      uint32_t x3 = r116[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
      r116[0U] = x0;
      r116[1U] = x1;
      r116[2U] = x2;
      r116[3U] = x3;
    }
    uint32_t *s0 = block_state.snd + (uint32_t)0U * (uint32_t)4U;
    uint32_t *s11 = block_state.snd + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r0 = block_state.fst + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *os = s11;
      uint32_t x = s11[i] ^ r1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = s11;
      uint32_t x = s11[i] ^ r3[i];
      os[i] = x;
    }
  }
  Lib_Memzero0_memzero(b, (uint32_t)64U * sizeof (b[0U]));
  return p;
}

/*
  Update function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2_blake2s_32_with_key_update(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s1 = *p;
  uint64_t total_len = s1.total_len;
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
    Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s2 = *p;
    K____uint32_t___uint32_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s2 = *p;
    K____uint32_t___uint32_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
    uint32_t sz1;
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
      for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
        uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
        uint8_t *b = buf + i0 * (uint32_t)64U;
        uint32_t m_w[16U] = { 0U };
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
        {
          uint32_t *os = m_w;
          uint8_t *bj = b + i * (uint32_t)4U;
          uint32_t u = load32_le(bj);
          uint32_t r = u;
          uint32_t x = r;
          os[i] = x;
        }
        uint32_t mask[4U] = { 0U };
        uint32_t wv_14 = (uint32_t)0U;
        uint32_t wv_15 = (uint32_t)0U;
        mask[0U] = (uint32_t)totlen;
        mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
        mask[2U] = wv_14;
        mask[3U] = wv_15;
        memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
        uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv3;
          uint32_t x = wv3[i] ^ mask[i];
          os[i] = x;
        }
        for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
        {
          uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
          uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
          memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
          uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
          uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
          uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
          uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
          uint32_t uu____0 = m_w[s21];
          uint32_t uu____1 = m_w[s4];
          uint32_t uu____2 = m_w[s6];
          r0[0U] = m_w[s0];
          r0[1U] = uu____0;
          r0[2U] = uu____1;
          r0[3U] = uu____2;
          uint32_t uu____3 = m_w[s3];
          uint32_t uu____4 = m_w[s5];
          uint32_t uu____5 = m_w[s7];
          r1[0U] = m_w[s11];
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
          uint32_t uu____9 = m_w[s111];
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
          uint32_t b10 = (uint32_t)1U;
          uint32_t c0 = (uint32_t)2U;
          uint32_t d0 = (uint32_t)3U;
          uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
          uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
          uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
          uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
          uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a2;
            uint32_t x1 = wv_a2[i] + wv_b2[i];
            os[i] = x1;
          }
          uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
          uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
          uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
          uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
          uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
          uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a6;
            uint32_t x1 = wv_a6[i] + wv_b6[i];
            os[i] = x1;
          }
          uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
          uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t b1 = (uint32_t)1U;
          uint32_t c = (uint32_t)2U;
          uint32_t d = (uint32_t)3U;
          uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
          uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
          uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
          uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a9;
            uint32_t x1 = wv_a9[i] + wv_b10[i];
            os[i] = x1;
          }
          uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
          uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
          uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
          uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
          uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
          uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint32_t *os = wv_a13;
            uint32_t x1 = wv_a13[i] + wv_b14[i];
            os[i] = x1;
          }
          uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
          uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
          uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
        uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
        uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t *os = s11;
          uint32_t x = s11[i] ^ r1[i];
          os[i] = x;
        }
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = s11;
          uint32_t x = s11[i] ^ r3[i];
          os[i] = x;
        }
      }
    }
    uint32_t ite0;
    if ((uint64_t)len % (uint64_t)(uint32_t)64U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite0 = (uint32_t)64U;
    }
    else
    {
      ite0 = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)64U);
    }
    uint32_t n_blocks = (len - ite0) / (uint32_t)64U;
    uint32_t data1_len = n_blocks * (uint32_t)64U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    uint32_t nb = data1_len / (uint32_t)64U;
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
      uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
      uint8_t *b = data1 + i0 * (uint32_t)64U;
      uint32_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      uint32_t mask[4U] = { 0U };
      uint32_t wv_14 = (uint32_t)0U;
      uint32_t wv_15 = (uint32_t)0U;
      mask[0U] = (uint32_t)totlen;
      mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
      uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv3;
        uint32_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
        uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
        uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint32_t uu____12 = m_w[s21];
        uint32_t uu____13 = m_w[s4];
        uint32_t uu____14 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____12;
        r0[2U] = uu____13;
        r0[3U] = uu____14;
        uint32_t uu____15 = m_w[s3];
        uint32_t uu____16 = m_w[s5];
        uint32_t uu____17 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____15;
        r1[2U] = uu____16;
        r1[3U] = uu____17;
        uint32_t uu____18 = m_w[s10];
        uint32_t uu____19 = m_w[s12];
        uint32_t uu____20 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____18;
        r20[2U] = uu____19;
        r20[3U] = uu____20;
        uint32_t uu____21 = m_w[s111];
        uint32_t uu____22 = m_w[s13];
        uint32_t uu____23 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____21;
        r30[2U] = uu____22;
        r30[3U] = uu____23;
        uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a2;
          uint32_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a6;
          uint32_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a9;
          uint32_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a13;
          uint32_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)64U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s2 = *p;
  K____uint32_t___uint32_t_ block_state10 = s2.block_state;
  uint8_t *buf0 = s2.buf;
  uint64_t total_len10 = s2.total_len;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)64U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)64U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ s20 = *p;
  K____uint32_t___uint32_t_ block_state1 = s20.block_state;
  uint8_t *buf = s20.buf;
  uint64_t total_len1 = s20.total_len;
  uint32_t sz1;
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
    for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
      uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
      uint8_t *b = buf + i0 * (uint32_t)64U;
      uint32_t m_w[16U] = { 0U };
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t *os = m_w;
        uint8_t *bj = b + i * (uint32_t)4U;
        uint32_t u = load32_le(bj);
        uint32_t r = u;
        uint32_t x = r;
        os[i] = x;
      }
      uint32_t mask[4U] = { 0U };
      uint32_t wv_14 = (uint32_t)0U;
      uint32_t wv_15 = (uint32_t)0U;
      mask[0U] = (uint32_t)totlen;
      mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
      uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv3;
        uint32_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
        uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
        uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint32_t uu____24 = m_w[s21];
        uint32_t uu____25 = m_w[s4];
        uint32_t uu____26 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____24;
        r0[2U] = uu____25;
        r0[3U] = uu____26;
        uint32_t uu____27 = m_w[s3];
        uint32_t uu____28 = m_w[s5];
        uint32_t uu____29 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____27;
        r1[2U] = uu____28;
        r1[3U] = uu____29;
        uint32_t uu____30 = m_w[s10];
        uint32_t uu____31 = m_w[s12];
        uint32_t uu____32 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____30;
        r20[2U] = uu____31;
        r20[3U] = uu____32;
        uint32_t uu____33 = m_w[s111];
        uint32_t uu____34 = m_w[s13];
        uint32_t uu____35 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____33;
        r30[2U] = uu____34;
        r30[3U] = uu____35;
        uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a2;
          uint32_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a6;
          uint32_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a9;
          uint32_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint32_t *os = wv_a13;
          uint32_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = s11;
        uint32_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
    }
  }
  uint32_t ite0;
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
  uint32_t n_blocks = (len - diff - ite0) / (uint32_t)64U;
  uint32_t data1_len = n_blocks * (uint32_t)64U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  uint32_t nb = data1_len / (uint32_t)64U;
  for (uint32_t i0 = (uint32_t)0U; i0 < nb; i0++)
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
    uint64_t totlen = ite + (uint64_t)((i0 + (uint32_t)1U) * (uint32_t)64U);
    uint8_t *b = data11 + i0 * (uint32_t)64U;
    uint32_t m_w[16U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t *os = m_w;
      uint8_t *bj = b + i * (uint32_t)4U;
      uint32_t u = load32_le(bj);
      uint32_t r = u;
      uint32_t x = r;
      os[i] = x;
    }
    uint32_t mask[4U] = { 0U };
    uint32_t wv_14 = (uint32_t)0U;
    uint32_t wv_15 = (uint32_t)0U;
    mask[0U] = (uint32_t)totlen;
    mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
    uint32_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv3;
      uint32_t x = wv3[i] ^ mask[i];
      os[i] = x;
    }
    for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)10U; i1++)
    {
      uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
      uint32_t m_st[(uint32_t)4U * (uint32_t)4U];
      memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
      uint32_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
      uint32_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
      uint32_t uu____36 = m_w[s21];
      uint32_t uu____37 = m_w[s4];
      uint32_t uu____38 = m_w[s6];
      r0[0U] = m_w[s0];
      r0[1U] = uu____36;
      r0[2U] = uu____37;
      r0[3U] = uu____38;
      uint32_t uu____39 = m_w[s3];
      uint32_t uu____40 = m_w[s5];
      uint32_t uu____41 = m_w[s7];
      r1[0U] = m_w[s11];
      r1[1U] = uu____39;
      r1[2U] = uu____40;
      r1[3U] = uu____41;
      uint32_t uu____42 = m_w[s10];
      uint32_t uu____43 = m_w[s12];
      uint32_t uu____44 = m_w[s14];
      r20[0U] = m_w[s8];
      r20[1U] = uu____42;
      r20[2U] = uu____43;
      r20[3U] = uu____44;
      uint32_t uu____45 = m_w[s111];
      uint32_t uu____46 = m_w[s13];
      uint32_t uu____47 = m_w[s15];
      r30[0U] = m_w[s9];
      r30[1U] = uu____45;
      r30[2U] = uu____46;
      r30[3U] = uu____47;
      uint32_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
      uint32_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
      uint32_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
      uint32_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t a = (uint32_t)0U;
      uint32_t b10 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint32_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
      uint32_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint32_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
      uint32_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
      uint32_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
      uint32_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a2;
        uint32_t x1 = wv_a2[i] + wv_b2[i];
        os[i] = x1;
      }
      uint32_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
      uint32_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint32_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
      uint32_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint32_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
      uint32_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
      uint32_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
      uint32_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a6;
        uint32_t x1 = wv_a6[i] + wv_b6[i];
        os[i] = x1;
      }
      uint32_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
      uint32_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint32_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t b1 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint32_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
      uint32_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint32_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
      uint32_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint32_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
      uint32_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a9;
        uint32_t x1 = wv_a9[i] + wv_b10[i];
        os[i] = x1;
      }
      uint32_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
      uint32_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
      uint32_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
      uint32_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint32_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
      uint32_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint32_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
      uint32_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint32_t *os = wv_a13;
        uint32_t x1 = wv_a13[i] + wv_b14[i];
        os[i] = x1;
      }
      uint32_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
      uint32_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
      uint32_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
    uint32_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
    uint32_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t *os = s11;
      uint32_t x = s11[i] ^ r1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = s11;
      uint32_t x = s11[i] ^ r3[i];
      os[i] = x;
    }
  }
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____){
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
Hacl_Streaming_Blake2_blake2s_32_with_key_finish(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ scrut = *p;
  K____uint32_t___uint32_t_ block_state = scrut.block_state;
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
  uint8_t *buf_1 = buf_;
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), (uint32_t)4U * (uint32_t)4U);
  uint32_t b0[(uint32_t)4U * (uint32_t)4U];
  memset(b0, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  K____uint32_t___uint32_t_ tmp_block_state = { .fst = wv, .snd = b0 };
  uint32_t *src_b = block_state.snd;
  uint32_t *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)16U * sizeof (uint32_t));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint8_t b2[64U] = { 0U };
  uint8_t *last = buf_1 + r - r;
  memcpy(b2, last, r * sizeof (uint8_t));
  uint64_t ite;
  if (key_size == (uint32_t)0U)
  {
    ite = prev_len;
  }
  else
  {
    ite = prev_len + (uint64_t)(uint32_t)64U;
  }
  uint64_t totlen = ite + (uint64_t)r;
  uint32_t m_w[16U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
  {
    uint32_t *os = m_w;
    uint8_t *bj = b2 + i * (uint32_t)4U;
    uint32_t u = load32_le(bj);
    uint32_t r1 = u;
    uint32_t x = r1;
    os[i] = x;
  }
  uint32_t mask[4U] = { 0U };
  uint32_t wv_14 = (uint32_t)0xFFFFFFFFU;
  uint32_t wv_15 = (uint32_t)0U;
  mask[0U] = (uint32_t)totlen;
  mask[1U] = (uint32_t)(totlen >> (uint32_t)32U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(tmp_block_state.fst,
    tmp_block_state.snd,
    (uint32_t)4U * (uint32_t)4U * sizeof (uint32_t));
  uint32_t *wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b10 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint32_t *wv_a0 = tmp_block_state.fst + a * (uint32_t)4U;
    uint32_t *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint32_t *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint32_t *wv_b1 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint32_t *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint32_t *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a2;
      uint32_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint32_t *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint32_t *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint32_t *wv_a4 = tmp_block_state.fst + a * (uint32_t)4U;
    uint32_t *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint32_t *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint32_t *wv_b5 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint32_t *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint32_t *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a6;
      uint32_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint32_t *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint32_t *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint32_t *r15 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r21 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r31 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b1 = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint32_t *wv_a = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint32_t *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint32_t *wv_a8 = tmp_block_state.fst + d * (uint32_t)4U;
    uint32_t *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint32_t *wv_a9 = tmp_block_state.fst + c * (uint32_t)4U;
    uint32_t *wv_b10 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a9;
      uint32_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint32_t *wv_a10 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint32_t *wv_b11 = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint32_t *wv_a11 = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint32_t *wv_b12 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint32_t *wv_a12 = tmp_block_state.fst + d * (uint32_t)4U;
    uint32_t *wv_b13 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint32_t *wv_a13 = tmp_block_state.fst + c * (uint32_t)4U;
    uint32_t *wv_b14 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint32_t *os = wv_a13;
      uint32_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint32_t *wv_a14 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint32_t *wv_b = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint32_t *r113 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint32_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint32_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  uint32_t *s0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint32_t *s1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r0 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)4U;
  uint32_t *r1 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
  uint32_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
  uint32_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  Lib_Memzero0_memzero(b2, (uint32_t)64U * sizeof (b2[0U]));
  uint32_t double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)4U;
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)4U;
  uint32_t *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint32_t *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
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

/*
  Free state function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2_blake2s_32_with_key_free(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ *s1
)
{
  Hacl_Streaming_Functor_state_s__K____uint32_t___uint32_t____ scrut = *s1;
  uint8_t *buf = scrut.buf;
  K____uint32_t___uint32_t_ block_state = scrut.block_state;
  uint32_t *wv = block_state.fst;
  uint32_t *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s1);
}

/*
  State allocation function when using a (potentially null) key
*/
Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
*Hacl_Streaming_Blake2_blake2b_32_with_key_create_in(uint32_t key_size, uint8_t *k1)
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  uint64_t *wv = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
  uint64_t *b0 = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
  K____uint64_t___uint64_t_ block_state = { .fst = wv, .snd = b0 };
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
  s1 = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____),
    (uint32_t)1U);
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____));
  p[0U] = s1;
  uint8_t b[128U] = { 0U };
  uint64_t *r00 = block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r10 = block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r20 = block_state.snd + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r30 = block_state.snd + (uint32_t)3U * (uint32_t)4U;
  uint64_t iv0 = Hacl_Impl_Blake2_Constants_ivTable_B[0U];
  uint64_t iv1 = Hacl_Impl_Blake2_Constants_ivTable_B[1U];
  uint64_t iv2 = Hacl_Impl_Blake2_Constants_ivTable_B[2U];
  uint64_t iv3 = Hacl_Impl_Blake2_Constants_ivTable_B[3U];
  uint64_t iv4 = Hacl_Impl_Blake2_Constants_ivTable_B[4U];
  uint64_t iv5 = Hacl_Impl_Blake2_Constants_ivTable_B[5U];
  uint64_t iv6 = Hacl_Impl_Blake2_Constants_ivTable_B[6U];
  uint64_t iv7 = Hacl_Impl_Blake2_Constants_ivTable_B[7U];
  r20[0U] = iv0;
  r20[1U] = iv1;
  r20[2U] = iv2;
  r20[3U] = iv3;
  r30[0U] = iv4;
  r30[1U] = iv5;
  r30[2U] = iv6;
  r30[3U] = iv7;
  uint64_t kk_shift_8 = (uint64_t)key_size << (uint32_t)8U;
  uint64_t iv0_ = iv0 ^ ((uint64_t)0x01010000U ^ (kk_shift_8 ^ (uint64_t)(uint32_t)64U));
  r00[0U] = iv0_;
  r00[1U] = iv1;
  r00[2U] = iv2;
  r00[3U] = iv3;
  r10[0U] = iv4;
  r10[1U] = iv5;
  r10[2U] = iv6;
  r10[3U] = iv7;
  if (!(key_size == (uint32_t)0U))
  {
    memcpy(b, k1, key_size * sizeof (uint8_t));
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
    uint64_t mask[4U] = { 0U };
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask[0U] = (uint64_t)totlen;
    mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(block_state.fst, block_state.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
    uint64_t *wv3 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *r21 = m_st + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r31 = m_st + (uint32_t)3U * (uint32_t)4U;
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
      r1[0U] = m_w[s11];
      r1[1U] = uu____3;
      r1[2U] = uu____4;
      r1[3U] = uu____5;
      uint64_t uu____6 = m_w[s10];
      uint64_t uu____7 = m_w[s12];
      uint64_t uu____8 = m_w[s14];
      r21[0U] = m_w[s8];
      r21[1U] = uu____6;
      r21[2U] = uu____7;
      r21[3U] = uu____8;
      uint64_t uu____9 = m_w[s111];
      uint64_t uu____10 = m_w[s13];
      uint64_t uu____11 = m_w[s15];
      r31[0U] = m_w[s9];
      r31[1U] = uu____9;
      r31[2U] = uu____10;
      r31[3U] = uu____11;
      uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
      uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
      uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
      uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t a = (uint32_t)0U;
      uint32_t b20 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint64_t *wv_a0 = block_state.fst + a * (uint32_t)4U;
      uint64_t *wv_b0 = block_state.fst + b20 * (uint32_t)4U;
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
      uint64_t *wv_a1 = block_state.fst + d0 * (uint32_t)4U;
      uint64_t *wv_b1 = block_state.fst + a * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a1;
        uint64_t x1 = wv_a1[i] ^ wv_b1[i];
        os[i] = x1;
      }
      uint64_t *r12 = wv_a1;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r12;
        uint64_t x1 = r12[i];
        uint64_t x10 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
        os[i] = x10;
      }
      uint64_t *wv_a2 = block_state.fst + c0 * (uint32_t)4U;
      uint64_t *wv_b2 = block_state.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a2;
        uint64_t x1 = wv_a2[i] + wv_b2[i];
        os[i] = x1;
      }
      uint64_t *wv_a3 = block_state.fst + b20 * (uint32_t)4U;
      uint64_t *wv_b3 = block_state.fst + c0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a3;
        uint64_t x1 = wv_a3[i] ^ wv_b3[i];
        os[i] = x1;
      }
      uint64_t *r13 = wv_a3;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r13;
        uint64_t x1 = r13[i];
        uint64_t x10 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
        os[i] = x10;
      }
      uint64_t *wv_a4 = block_state.fst + a * (uint32_t)4U;
      uint64_t *wv_b4 = block_state.fst + b20 * (uint32_t)4U;
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
      uint64_t *wv_a5 = block_state.fst + d0 * (uint32_t)4U;
      uint64_t *wv_b5 = block_state.fst + a * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a5;
        uint64_t x1 = wv_a5[i] ^ wv_b5[i];
        os[i] = x1;
      }
      uint64_t *r14 = wv_a5;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r14;
        uint64_t x1 = r14[i];
        uint64_t x10 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
        os[i] = x10;
      }
      uint64_t *wv_a6 = block_state.fst + c0 * (uint32_t)4U;
      uint64_t *wv_b6 = block_state.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a6;
        uint64_t x1 = wv_a6[i] + wv_b6[i];
        os[i] = x1;
      }
      uint64_t *wv_a7 = block_state.fst + b20 * (uint32_t)4U;
      uint64_t *wv_b7 = block_state.fst + c0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a7;
        uint64_t x1 = wv_a7[i] ^ wv_b7[i];
        os[i] = x1;
      }
      uint64_t *r15 = wv_a7;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r15;
        uint64_t x1 = r15[i];
        uint64_t x10 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
        os[i] = x10;
      }
      uint64_t *r16 = block_state.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r22 = block_state.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r32 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
      uint64_t *r110 = r16;
      uint64_t x00 = r110[1U];
      uint64_t x10 = r110[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
      uint64_t x20 = r110[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
      uint64_t x30 = r110[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
      r110[0U] = x00;
      r110[1U] = x10;
      r110[2U] = x20;
      r110[3U] = x30;
      uint64_t *r111 = r22;
      uint64_t x01 = r111[2U];
      uint64_t x11 = r111[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
      uint64_t x21 = r111[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
      uint64_t x31 = r111[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
      r111[0U] = x01;
      r111[1U] = x11;
      r111[2U] = x21;
      r111[3U] = x31;
      uint64_t *r112 = r32;
      uint64_t x02 = r112[3U];
      uint64_t x12 = r112[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
      uint64_t x22 = r112[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
      uint64_t x32 = r112[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
      r112[0U] = x02;
      r112[1U] = x12;
      r112[2U] = x22;
      r112[3U] = x32;
      uint32_t a0 = (uint32_t)0U;
      uint32_t b2 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint64_t *wv_a = block_state.fst + a0 * (uint32_t)4U;
      uint64_t *wv_b8 = block_state.fst + b2 * (uint32_t)4U;
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
      uint64_t *wv_a8 = block_state.fst + d * (uint32_t)4U;
      uint64_t *wv_b9 = block_state.fst + a0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a8;
        uint64_t x1 = wv_a8[i] ^ wv_b9[i];
        os[i] = x1;
      }
      uint64_t *r17 = wv_a8;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r17;
        uint64_t x1 = r17[i];
        uint64_t x13 = x1 >> (uint32_t)32U | x1 << (uint32_t)32U;
        os[i] = x13;
      }
      uint64_t *wv_a9 = block_state.fst + c * (uint32_t)4U;
      uint64_t *wv_b10 = block_state.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a9;
        uint64_t x1 = wv_a9[i] + wv_b10[i];
        os[i] = x1;
      }
      uint64_t *wv_a10 = block_state.fst + b2 * (uint32_t)4U;
      uint64_t *wv_b11 = block_state.fst + c * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a10;
        uint64_t x1 = wv_a10[i] ^ wv_b11[i];
        os[i] = x1;
      }
      uint64_t *r18 = wv_a10;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r18;
        uint64_t x1 = r18[i];
        uint64_t x13 = x1 >> (uint32_t)24U | x1 << (uint32_t)40U;
        os[i] = x13;
      }
      uint64_t *wv_a11 = block_state.fst + a0 * (uint32_t)4U;
      uint64_t *wv_b12 = block_state.fst + b2 * (uint32_t)4U;
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
      uint64_t *wv_a12 = block_state.fst + d * (uint32_t)4U;
      uint64_t *wv_b13 = block_state.fst + a0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a12;
        uint64_t x1 = wv_a12[i] ^ wv_b13[i];
        os[i] = x1;
      }
      uint64_t *r19 = wv_a12;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r19;
        uint64_t x1 = r19[i];
        uint64_t x13 = x1 >> (uint32_t)16U | x1 << (uint32_t)48U;
        os[i] = x13;
      }
      uint64_t *wv_a13 = block_state.fst + c * (uint32_t)4U;
      uint64_t *wv_b14 = block_state.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a13;
        uint64_t x1 = wv_a13[i] + wv_b14[i];
        os[i] = x1;
      }
      uint64_t *wv_a14 = block_state.fst + b2 * (uint32_t)4U;
      uint64_t *wv_b = block_state.fst + c * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a14;
        uint64_t x1 = wv_a14[i] ^ wv_b[i];
        os[i] = x1;
      }
      uint64_t *r113 = wv_a14;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = r113;
        uint64_t x1 = r113[i];
        uint64_t x13 = x1 >> (uint32_t)63U | x1 << (uint32_t)1U;
        os[i] = x13;
      }
      uint64_t *r114 = block_state.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
      uint64_t *r11 = r114;
      uint64_t x03 = r11[3U];
      uint64_t x13 = r11[((uint32_t)3U + (uint32_t)1U) % (uint32_t)4U];
      uint64_t x23 = r11[((uint32_t)3U + (uint32_t)2U) % (uint32_t)4U];
      uint64_t x33 = r11[((uint32_t)3U + (uint32_t)3U) % (uint32_t)4U];
      r11[0U] = x03;
      r11[1U] = x13;
      r11[2U] = x23;
      r11[3U] = x33;
      uint64_t *r115 = r2;
      uint64_t x04 = r115[2U];
      uint64_t x14 = r115[((uint32_t)2U + (uint32_t)1U) % (uint32_t)4U];
      uint64_t x24 = r115[((uint32_t)2U + (uint32_t)2U) % (uint32_t)4U];
      uint64_t x34 = r115[((uint32_t)2U + (uint32_t)3U) % (uint32_t)4U];
      r115[0U] = x04;
      r115[1U] = x14;
      r115[2U] = x24;
      r115[3U] = x34;
      uint64_t *r116 = r3;
      uint64_t x0 = r116[1U];
      uint64_t x1 = r116[((uint32_t)1U + (uint32_t)1U) % (uint32_t)4U];
      uint64_t x2 = r116[((uint32_t)1U + (uint32_t)2U) % (uint32_t)4U];
      uint64_t x3 = r116[((uint32_t)1U + (uint32_t)3U) % (uint32_t)4U];
      r116[0U] = x0;
      r116[1U] = x1;
      r116[2U] = x2;
      r116[3U] = x3;
    }
    uint64_t *s0 = block_state.snd + (uint32_t)0U * (uint32_t)4U;
    uint64_t *s11 = block_state.snd + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r0 = block_state.fst + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *os = s11;
      uint64_t x = s11[i] ^ r1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = s11;
      uint64_t x = s11[i] ^ r3[i];
      os[i] = x;
    }
  }
  Lib_Memzero0_memzero(b, (uint32_t)128U * sizeof (b[0U]));
  return p;
}

/*
  Update function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2_blake2b_32_with_key_update(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s1 = *p;
  uint64_t total_len = s1.total_len;
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
    Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s2 = *p;
    K____uint64_t___uint64_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
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
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s2 = *p;
    K____uint64_t___uint64_t_ block_state1 = s2.block_state;
    uint8_t *buf = s2.buf;
    uint64_t total_len1 = s2.total_len;
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
        uint64_t mask[4U] = { 0U };
        uint64_t wv_14 = (uint64_t)0U;
        uint64_t wv_15 = (uint64_t)0U;
        mask[0U] = (uint64_t)totlen;
        mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
        mask[2U] = wv_14;
        mask[3U] = wv_15;
        memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
        uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv3;
          uint64_t x = wv3[i] ^ mask[i];
          os[i] = x;
        }
        for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
        {
          uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
          KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
          uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
          memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
          uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
          uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
          uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
          uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
          uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
          uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
          uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
          uint64_t uu____0 = m_w[s21];
          uint64_t uu____1 = m_w[s4];
          uint64_t uu____2 = m_w[s6];
          r0[0U] = m_w[s0];
          r0[1U] = uu____0;
          r0[2U] = uu____1;
          r0[3U] = uu____2;
          uint64_t uu____3 = m_w[s3];
          uint64_t uu____4 = m_w[s5];
          uint64_t uu____5 = m_w[s7];
          r1[0U] = m_w[s11];
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
          uint64_t uu____9 = m_w[s111];
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
          uint32_t b10 = (uint32_t)1U;
          uint32_t c0 = (uint32_t)2U;
          uint32_t d0 = (uint32_t)3U;
          uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
          uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
          uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
          uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
          uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a2;
            uint64_t x1 = wv_a2[i] + wv_b2[i];
            os[i] = x1;
          }
          uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
          uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
          uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
          uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
          uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
          uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
          uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a6;
            uint64_t x1 = wv_a6[i] + wv_b6[i];
            os[i] = x1;
          }
          uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
          uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
          uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint32_t b1 = (uint32_t)1U;
          uint32_t c = (uint32_t)2U;
          uint32_t d = (uint32_t)3U;
          uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
          uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
          uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
          uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a9;
            uint64_t x1 = wv_a9[i] + wv_b10[i];
            os[i] = x1;
          }
          uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
          uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
          uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
          uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
          uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
          uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
          uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
          uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
          for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
          {
            uint64_t *os = wv_a13;
            uint64_t x1 = wv_a13[i] + wv_b14[i];
            os[i] = x1;
          }
          uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
          uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
          uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
          uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
          uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
        uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
        uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
          uint64_t *os = s11;
          uint64_t x = s11[i] ^ r1[i];
          os[i] = x;
        }
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = s11;
          uint64_t x = s11[i] ^ r3[i];
          os[i] = x;
        }
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
      uint64_t mask[4U] = { 0U };
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask[0U] = (uint64_t)totlen;
      mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
      uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv3;
        uint64_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
        uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
        uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint64_t uu____12 = m_w[s21];
        uint64_t uu____13 = m_w[s4];
        uint64_t uu____14 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____12;
        r0[2U] = uu____13;
        r0[3U] = uu____14;
        uint64_t uu____15 = m_w[s3];
        uint64_t uu____16 = m_w[s5];
        uint64_t uu____17 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____15;
        r1[2U] = uu____16;
        r1[3U] = uu____17;
        uint64_t uu____18 = m_w[s10];
        uint64_t uu____19 = m_w[s12];
        uint64_t uu____20 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____18;
        r20[2U] = uu____19;
        r20[3U] = uu____20;
        uint64_t uu____21 = m_w[s111];
        uint64_t uu____22 = m_w[s13];
        uint64_t uu____23 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____21;
        r30[2U] = uu____22;
        r30[3U] = uu____23;
        uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a2;
          uint64_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a6;
          uint64_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a9;
          uint64_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a13;
          uint64_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
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
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s2 = *p;
  K____uint64_t___uint64_t_ block_state10 = s2.block_state;
  uint8_t *buf0 = s2.buf;
  uint64_t total_len10 = s2.total_len;
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
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ s20 = *p;
  K____uint64_t___uint64_t_ block_state1 = s20.block_state;
  uint8_t *buf = s20.buf;
  uint64_t total_len1 = s20.total_len;
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
      uint64_t mask[4U] = { 0U };
      uint64_t wv_14 = (uint64_t)0U;
      uint64_t wv_15 = (uint64_t)0U;
      mask[0U] = (uint64_t)totlen;
      mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
      mask[2U] = wv_14;
      mask[3U] = wv_15;
      memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
      uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv3;
        uint64_t x = wv3[i] ^ mask[i];
        os[i] = x;
      }
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
      {
        uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
        KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
        uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
        memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
        uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
        uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
        uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
        uint64_t uu____24 = m_w[s21];
        uint64_t uu____25 = m_w[s4];
        uint64_t uu____26 = m_w[s6];
        r0[0U] = m_w[s0];
        r0[1U] = uu____24;
        r0[2U] = uu____25;
        r0[3U] = uu____26;
        uint64_t uu____27 = m_w[s3];
        uint64_t uu____28 = m_w[s5];
        uint64_t uu____29 = m_w[s7];
        r1[0U] = m_w[s11];
        r1[1U] = uu____27;
        r1[2U] = uu____28;
        r1[3U] = uu____29;
        uint64_t uu____30 = m_w[s10];
        uint64_t uu____31 = m_w[s12];
        uint64_t uu____32 = m_w[s14];
        r20[0U] = m_w[s8];
        r20[1U] = uu____30;
        r20[2U] = uu____31;
        r20[3U] = uu____32;
        uint64_t uu____33 = m_w[s111];
        uint64_t uu____34 = m_w[s13];
        uint64_t uu____35 = m_w[s15];
        r30[0U] = m_w[s9];
        r30[1U] = uu____33;
        r30[2U] = uu____34;
        r30[3U] = uu____35;
        uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
        uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
        uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
        uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
        uint32_t a = (uint32_t)0U;
        uint32_t b10 = (uint32_t)1U;
        uint32_t c0 = (uint32_t)2U;
        uint32_t d0 = (uint32_t)3U;
        uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a2;
          uint64_t x1 = wv_a2[i] + wv_b2[i];
          os[i] = x1;
        }
        uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
        uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
        uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
        uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
        uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
        uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a6;
          uint64_t x1 = wv_a6[i] + wv_b6[i];
          os[i] = x1;
        }
        uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
        uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
        uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint32_t b1 = (uint32_t)1U;
        uint32_t c = (uint32_t)2U;
        uint32_t d = (uint32_t)3U;
        uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a9;
          uint64_t x1 = wv_a9[i] + wv_b10[i];
          os[i] = x1;
        }
        uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
        uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
        uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
        uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
        uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
        uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          uint64_t *os = wv_a13;
          uint64_t x1 = wv_a13[i] + wv_b14[i];
          os[i] = x1;
        }
        uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
        uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
        uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
        uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
        uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
      uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
      uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r1[i];
        os[i] = x;
      }
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = s11;
        uint64_t x = s11[i] ^ r3[i];
        os[i] = x;
      }
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
    uint64_t mask[4U] = { 0U };
    uint64_t wv_14 = (uint64_t)0U;
    uint64_t wv_15 = (uint64_t)0U;
    mask[0U] = (uint64_t)totlen;
    mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
    mask[2U] = wv_14;
    mask[3U] = wv_15;
    memcpy(block_state1.fst, block_state1.snd, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
    uint64_t *wv3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv3;
      uint64_t x = wv3[i] ^ mask[i];
      os[i] = x;
    }
    for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)12U; i1++)
    {
      uint32_t start_idx = i1 % (uint32_t)10U * (uint32_t)16U;
      KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
      uint64_t m_st[(uint32_t)4U * (uint32_t)4U];
      memset(m_st, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
      uint64_t *r0 = m_st + (uint32_t)0U * (uint32_t)4U;
      uint64_t *r1 = m_st + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r20 = m_st + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r30 = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t s0 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx];
      uint32_t s11 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)1U];
      uint32_t s21 = Hacl_Impl_Blake2_Constants_sigmaTable[start_idx + (uint32_t)2U];
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
      uint64_t uu____36 = m_w[s21];
      uint64_t uu____37 = m_w[s4];
      uint64_t uu____38 = m_w[s6];
      r0[0U] = m_w[s0];
      r0[1U] = uu____36;
      r0[2U] = uu____37;
      r0[3U] = uu____38;
      uint64_t uu____39 = m_w[s3];
      uint64_t uu____40 = m_w[s5];
      uint64_t uu____41 = m_w[s7];
      r1[0U] = m_w[s11];
      r1[1U] = uu____39;
      r1[2U] = uu____40;
      r1[3U] = uu____41;
      uint64_t uu____42 = m_w[s10];
      uint64_t uu____43 = m_w[s12];
      uint64_t uu____44 = m_w[s14];
      r20[0U] = m_w[s8];
      r20[1U] = uu____42;
      r20[2U] = uu____43;
      r20[3U] = uu____44;
      uint64_t uu____45 = m_w[s111];
      uint64_t uu____46 = m_w[s13];
      uint64_t uu____47 = m_w[s15];
      r30[0U] = m_w[s9];
      r30[1U] = uu____45;
      r30[2U] = uu____46;
      r30[3U] = uu____47;
      uint64_t *x = m_st + (uint32_t)0U * (uint32_t)4U;
      uint64_t *y = m_st + (uint32_t)1U * (uint32_t)4U;
      uint64_t *z = m_st + (uint32_t)2U * (uint32_t)4U;
      uint64_t *w = m_st + (uint32_t)3U * (uint32_t)4U;
      uint32_t a = (uint32_t)0U;
      uint32_t b10 = (uint32_t)1U;
      uint32_t c0 = (uint32_t)2U;
      uint32_t d0 = (uint32_t)3U;
      uint64_t *wv_a0 = block_state1.fst + a * (uint32_t)4U;
      uint64_t *wv_b0 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint64_t *wv_a1 = block_state1.fst + d0 * (uint32_t)4U;
      uint64_t *wv_b1 = block_state1.fst + a * (uint32_t)4U;
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
      uint64_t *wv_a2 = block_state1.fst + c0 * (uint32_t)4U;
      uint64_t *wv_b2 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a2;
        uint64_t x1 = wv_a2[i] + wv_b2[i];
        os[i] = x1;
      }
      uint64_t *wv_a3 = block_state1.fst + b10 * (uint32_t)4U;
      uint64_t *wv_b3 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint64_t *wv_a4 = block_state1.fst + a * (uint32_t)4U;
      uint64_t *wv_b4 = block_state1.fst + b10 * (uint32_t)4U;
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
      uint64_t *wv_a5 = block_state1.fst + d0 * (uint32_t)4U;
      uint64_t *wv_b5 = block_state1.fst + a * (uint32_t)4U;
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
      uint64_t *wv_a6 = block_state1.fst + c0 * (uint32_t)4U;
      uint64_t *wv_b6 = block_state1.fst + d0 * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a6;
        uint64_t x1 = wv_a6[i] + wv_b6[i];
        os[i] = x1;
      }
      uint64_t *wv_a7 = block_state1.fst + b10 * (uint32_t)4U;
      uint64_t *wv_b7 = block_state1.fst + c0 * (uint32_t)4U;
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
      uint64_t *r15 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r21 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r31 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint32_t b1 = (uint32_t)1U;
      uint32_t c = (uint32_t)2U;
      uint32_t d = (uint32_t)3U;
      uint64_t *wv_a = block_state1.fst + a0 * (uint32_t)4U;
      uint64_t *wv_b8 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint64_t *wv_a8 = block_state1.fst + d * (uint32_t)4U;
      uint64_t *wv_b9 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint64_t *wv_a9 = block_state1.fst + c * (uint32_t)4U;
      uint64_t *wv_b10 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a9;
        uint64_t x1 = wv_a9[i] + wv_b10[i];
        os[i] = x1;
      }
      uint64_t *wv_a10 = block_state1.fst + b1 * (uint32_t)4U;
      uint64_t *wv_b11 = block_state1.fst + c * (uint32_t)4U;
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
      uint64_t *wv_a11 = block_state1.fst + a0 * (uint32_t)4U;
      uint64_t *wv_b12 = block_state1.fst + b1 * (uint32_t)4U;
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
      uint64_t *wv_a12 = block_state1.fst + d * (uint32_t)4U;
      uint64_t *wv_b13 = block_state1.fst + a0 * (uint32_t)4U;
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
      uint64_t *wv_a13 = block_state1.fst + c * (uint32_t)4U;
      uint64_t *wv_b14 = block_state1.fst + d * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        uint64_t *os = wv_a13;
        uint64_t x1 = wv_a13[i] + wv_b14[i];
        os[i] = x1;
      }
      uint64_t *wv_a14 = block_state1.fst + b1 * (uint32_t)4U;
      uint64_t *wv_b = block_state1.fst + c * (uint32_t)4U;
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
      uint64_t *r113 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
      uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
      uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint64_t *s0 = block_state1.snd + (uint32_t)0U * (uint32_t)4U;
    uint64_t *s11 = block_state1.snd + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r0 = block_state1.fst + (uint32_t)0U * (uint32_t)4U;
    uint64_t *r1 = block_state1.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = block_state1.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = block_state1.fst + (uint32_t)3U * (uint32_t)4U;
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
      uint64_t *os = s11;
      uint64_t x = s11[i] ^ r1[i];
      os[i] = x;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = s11;
      uint64_t x = s11[i] ^ r3[i];
      os[i] = x;
    }
  }
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____){
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
Hacl_Streaming_Blake2_blake2b_32_with_key_finish(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ scrut = *p;
  K____uint64_t___uint64_t_ block_state = scrut.block_state;
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
  uint64_t wv[(uint32_t)4U * (uint32_t)4U];
  memset(wv, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * (uint32_t)4U);
  uint64_t b0[(uint32_t)4U * (uint32_t)4U];
  memset(b0, 0U, (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  K____uint64_t___uint64_t_ tmp_block_state = { .fst = wv, .snd = b0 };
  uint64_t *src_b = block_state.snd;
  uint64_t *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)16U * sizeof (uint64_t));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint8_t b2[128U] = { 0U };
  uint8_t *last = buf_1 + r - r;
  memcpy(b2, last, r * sizeof (uint8_t));
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
  uint64_t mask[4U] = { 0U };
  uint64_t wv_14 = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t wv_15 = (uint64_t)0U;
  mask[0U] = (uint64_t)totlen;
  mask[1U] = (uint64_t)(totlen >> (uint32_t)64U);
  mask[2U] = wv_14;
  mask[3U] = wv_15;
  memcpy(tmp_block_state.fst,
    tmp_block_state.snd,
    (uint32_t)4U * (uint32_t)4U * sizeof (uint64_t));
  uint64_t *wv3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b10 = (uint32_t)1U;
    uint32_t c0 = (uint32_t)2U;
    uint32_t d0 = (uint32_t)3U;
    uint64_t *wv_a0 = tmp_block_state.fst + a * (uint32_t)4U;
    uint64_t *wv_b0 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint64_t *wv_a1 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint64_t *wv_b1 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint64_t *wv_a2 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint64_t *wv_b2 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a2;
      uint64_t x1 = wv_a2[i] + wv_b2[i];
      os[i] = x1;
    }
    uint64_t *wv_a3 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint64_t *wv_b3 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint64_t *wv_a4 = tmp_block_state.fst + a * (uint32_t)4U;
    uint64_t *wv_b4 = tmp_block_state.fst + b10 * (uint32_t)4U;
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
    uint64_t *wv_a5 = tmp_block_state.fst + d0 * (uint32_t)4U;
    uint64_t *wv_b5 = tmp_block_state.fst + a * (uint32_t)4U;
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
    uint64_t *wv_a6 = tmp_block_state.fst + c0 * (uint32_t)4U;
    uint64_t *wv_b6 = tmp_block_state.fst + d0 * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a6;
      uint64_t x1 = wv_a6[i] + wv_b6[i];
      os[i] = x1;
    }
    uint64_t *wv_a7 = tmp_block_state.fst + b10 * (uint32_t)4U;
    uint64_t *wv_b7 = tmp_block_state.fst + c0 * (uint32_t)4U;
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
    uint64_t *r15 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r21 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r31 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
    uint32_t b1 = (uint32_t)1U;
    uint32_t c = (uint32_t)2U;
    uint32_t d = (uint32_t)3U;
    uint64_t *wv_a = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint64_t *wv_b8 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint64_t *wv_a8 = tmp_block_state.fst + d * (uint32_t)4U;
    uint64_t *wv_b9 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint64_t *wv_a9 = tmp_block_state.fst + c * (uint32_t)4U;
    uint64_t *wv_b10 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a9;
      uint64_t x1 = wv_a9[i] + wv_b10[i];
      os[i] = x1;
    }
    uint64_t *wv_a10 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint64_t *wv_b11 = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint64_t *wv_a11 = tmp_block_state.fst + a0 * (uint32_t)4U;
    uint64_t *wv_b12 = tmp_block_state.fst + b1 * (uint32_t)4U;
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
    uint64_t *wv_a12 = tmp_block_state.fst + d * (uint32_t)4U;
    uint64_t *wv_b13 = tmp_block_state.fst + a0 * (uint32_t)4U;
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
    uint64_t *wv_a13 = tmp_block_state.fst + c * (uint32_t)4U;
    uint64_t *wv_b14 = tmp_block_state.fst + d * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      uint64_t *os = wv_a13;
      uint64_t x1 = wv_a13[i] + wv_b14[i];
      os[i] = x1;
    }
    uint64_t *wv_a14 = tmp_block_state.fst + b1 * (uint32_t)4U;
    uint64_t *wv_b = tmp_block_state.fst + c * (uint32_t)4U;
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
    uint64_t *r113 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
    uint64_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
    uint64_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  uint64_t *s0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint64_t *s1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r0 = tmp_block_state.fst + (uint32_t)0U * (uint32_t)4U;
  uint64_t *r1 = tmp_block_state.fst + (uint32_t)1U * (uint32_t)4U;
  uint64_t *r2 = tmp_block_state.fst + (uint32_t)2U * (uint32_t)4U;
  uint64_t *r3 = tmp_block_state.fst + (uint32_t)3U * (uint32_t)4U;
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
  Lib_Memzero0_memzero(b2, (uint32_t)128U * sizeof (b2[0U]));
  uint32_t double_row = (uint32_t)2U * (uint32_t)4U * (uint32_t)8U;
  KRML_CHECK_SIZE(sizeof (uint8_t), double_row);
  uint8_t b[double_row];
  memset(b, 0U, double_row * sizeof (uint8_t));
  uint8_t *first = b;
  uint8_t *second = b + (uint32_t)4U * (uint32_t)8U;
  uint64_t *row0 = tmp_block_state.snd + (uint32_t)0U * (uint32_t)4U;
  uint64_t *row1 = tmp_block_state.snd + (uint32_t)1U * (uint32_t)4U;
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

/*
  Free state function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2_blake2b_32_with_key_free(
  uint32_t key_size,
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ *s1
)
{
  Hacl_Streaming_Functor_state_s__K____uint64_t___uint64_t____ scrut = *s1;
  uint8_t *buf = scrut.buf;
  K____uint64_t___uint64_t_ block_state = scrut.block_state;
  uint64_t *wv = block_state.fst;
  uint64_t *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s1);
}

