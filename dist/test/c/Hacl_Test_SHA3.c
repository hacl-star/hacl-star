/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#include "Hacl_Test_SHA3.h"

extern uint32_t Hacl_Impl_SHA3_Vec_keccak_rotc[24];

extern uint32_t Hacl_Impl_SHA3_Vec_keccak_piln[24];

extern uint64_t Hacl_Impl_SHA3_Vec_keccak_rndc[24];

extern void C_String_print(Prims_string uu___);

static void absorb_inner_32(uint8_t *b, uint64_t *s)
{
  uint64_t ws[32U] = { 0U };
  uint8_t *b1 = b;
  uint64_t u = load64_le(b1);
  ws[0U] = u;
  uint64_t u0 = load64_le(b1 + 8U);
  ws[1U] = u0;
  uint64_t u1 = load64_le(b1 + 16U);
  ws[2U] = u1;
  uint64_t u2 = load64_le(b1 + 24U);
  ws[3U] = u2;
  uint64_t u3 = load64_le(b1 + 32U);
  ws[4U] = u3;
  uint64_t u4 = load64_le(b1 + 40U);
  ws[5U] = u4;
  uint64_t u5 = load64_le(b1 + 48U);
  ws[6U] = u5;
  uint64_t u6 = load64_le(b1 + 56U);
  ws[7U] = u6;
  uint64_t u7 = load64_le(b1 + 64U);
  ws[8U] = u7;
  uint64_t u8 = load64_le(b1 + 72U);
  ws[9U] = u8;
  uint64_t u9 = load64_le(b1 + 80U);
  ws[10U] = u9;
  uint64_t u10 = load64_le(b1 + 88U);
  ws[11U] = u10;
  uint64_t u11 = load64_le(b1 + 96U);
  ws[12U] = u11;
  uint64_t u12 = load64_le(b1 + 104U);
  ws[13U] = u12;
  uint64_t u13 = load64_le(b1 + 112U);
  ws[14U] = u13;
  uint64_t u14 = load64_le(b1 + 120U);
  ws[15U] = u14;
  uint64_t u15 = load64_le(b1 + 128U);
  ws[16U] = u15;
  uint64_t u16 = load64_le(b1 + 136U);
  ws[17U] = u16;
  uint64_t u17 = load64_le(b1 + 144U);
  ws[18U] = u17;
  uint64_t u18 = load64_le(b1 + 152U);
  ws[19U] = u18;
  uint64_t u19 = load64_le(b1 + 160U);
  ws[20U] = u19;
  uint64_t u20 = load64_le(b1 + 168U);
  ws[21U] = u20;
  uint64_t u21 = load64_le(b1 + 176U);
  ws[22U] = u21;
  uint64_t u22 = load64_le(b1 + 184U);
  ws[23U] = u22;
  uint64_t u23 = load64_le(b1 + 192U);
  ws[24U] = u23;
  uint64_t u24 = load64_le(b1 + 200U);
  ws[25U] = u24;
  uint64_t u25 = load64_le(b1 + 208U);
  ws[26U] = u25;
  uint64_t u26 = load64_le(b1 + 216U);
  ws[27U] = u26;
  uint64_t u27 = load64_le(b1 + 224U);
  ws[28U] = u27;
  uint64_t u28 = load64_le(b1 + 232U);
  ws[29U] = u28;
  uint64_t u29 = load64_le(b1 + 240U);
  ws[30U] = u29;
  uint64_t u30 = load64_le(b1 + 248U);
  ws[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    for (uint32_t i = 0U; i < 5U; i++)
    {
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
    }
    for (uint32_t i1 = 0U; i1 < 5U; i1++)
    {
      uint64_t uu____0 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
      for (uint32_t i = 0U; i < 5U; i++)
      {
        s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;
      }
    }
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____1 = current;
      s[_Y] = uu____1 << r | uu____1 >> (64U - r);
      current = temp;
    }
    for (uint32_t i = 0U; i < 5U; i++)
    {
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;
    }
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
}

static void
shake128(uint8_t *output, uint32_t outputByteLen, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 168U;
  for (uint32_t i = 0U; i < inputByteLen / rateInBytes1; i++)
  {
    uint8_t b[256U] = { 0U };
    uint8_t *b_ = b;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    absorb_inner_32(b_, s);
  }
  uint8_t b1[256U] = { 0U };
  uint8_t *b_ = b1;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x1FU;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u = load64_le(b);
  ws0[0U] = u;
  uint64_t u0 = load64_le(b + 8U);
  ws0[1U] = u0;
  uint64_t u1 = load64_le(b + 16U);
  ws0[2U] = u1;
  uint64_t u2 = load64_le(b + 24U);
  ws0[3U] = u2;
  uint64_t u3 = load64_le(b + 32U);
  ws0[4U] = u3;
  uint64_t u4 = load64_le(b + 40U);
  ws0[5U] = u4;
  uint64_t u5 = load64_le(b + 48U);
  ws0[6U] = u5;
  uint64_t u6 = load64_le(b + 56U);
  ws0[7U] = u6;
  uint64_t u7 = load64_le(b + 64U);
  ws0[8U] = u7;
  uint64_t u8 = load64_le(b + 72U);
  ws0[9U] = u8;
  uint64_t u9 = load64_le(b + 80U);
  ws0[10U] = u9;
  uint64_t u10 = load64_le(b + 88U);
  ws0[11U] = u10;
  uint64_t u11 = load64_le(b + 96U);
  ws0[12U] = u11;
  uint64_t u12 = load64_le(b + 104U);
  ws0[13U] = u12;
  uint64_t u13 = load64_le(b + 112U);
  ws0[14U] = u13;
  uint64_t u14 = load64_le(b + 120U);
  ws0[15U] = u14;
  uint64_t u15 = load64_le(b + 128U);
  ws0[16U] = u15;
  uint64_t u16 = load64_le(b + 136U);
  ws0[17U] = u16;
  uint64_t u17 = load64_le(b + 144U);
  ws0[18U] = u17;
  uint64_t u18 = load64_le(b + 152U);
  ws0[19U] = u18;
  uint64_t u19 = load64_le(b + 160U);
  ws0[20U] = u19;
  uint64_t u20 = load64_le(b + 168U);
  ws0[21U] = u20;
  uint64_t u21 = load64_le(b + 176U);
  ws0[22U] = u21;
  uint64_t u22 = load64_le(b + 184U);
  ws0[23U] = u22;
  uint64_t u23 = load64_le(b + 192U);
  ws0[24U] = u23;
  uint64_t u24 = load64_le(b + 200U);
  ws0[25U] = u24;
  uint64_t u25 = load64_le(b + 208U);
  ws0[26U] = u25;
  uint64_t u26 = load64_le(b + 216U);
  ws0[27U] = u26;
  uint64_t u27 = load64_le(b + 224U);
  ws0[28U] = u27;
  uint64_t u28 = load64_le(b + 232U);
  ws0[29U] = u28;
  uint64_t u29 = load64_le(b + 240U);
  ws0[30U] = u29;
  uint64_t u30 = load64_le(b + 248U);
  ws0[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b3 = b2;
  uint8_t *b0 = b3;
  b0[rateInBytes1 - 1U] = 0x80U;
  absorb_inner_32(b3, s);
  for (uint32_t i0 = 0U; i0 < outputByteLen / rateInBytes1; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, s, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b02 = rb;
    memcpy(b02 + i0 * rateInBytes1, hbuf, rateInBytes1 * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      for (uint32_t i = 0U; i < 5U; i++)
      {
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
      }
      for (uint32_t i2 = 0U; i2 < 5U; i2++)
      {
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        for (uint32_t i = 0U; i < 5U; i++)
        {
          s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;
        }
      }
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____1 = current;
        s[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      for (uint32_t i = 0U; i < 5U; i++)
      {
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;
      }
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint32_t remOut = outputByteLen % rateInBytes1;
  uint8_t hbuf[256U] = { 0U };
  uint64_t ws[32U] = { 0U };
  memcpy(ws, s, 25U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    store64_le(hbuf + i * 8U, ws[i]);
  }
  memcpy(rb + outputByteLen - remOut, hbuf, remOut * sizeof (uint8_t));
}

static void
shake256(uint8_t *output, uint32_t outputByteLen, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 136U;
  for (uint32_t i = 0U; i < inputByteLen / rateInBytes1; i++)
  {
    uint8_t b[256U] = { 0U };
    uint8_t *b_ = b;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    absorb_inner_32(b_, s);
  }
  uint8_t b1[256U] = { 0U };
  uint8_t *b_ = b1;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x1FU;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u = load64_le(b);
  ws0[0U] = u;
  uint64_t u0 = load64_le(b + 8U);
  ws0[1U] = u0;
  uint64_t u1 = load64_le(b + 16U);
  ws0[2U] = u1;
  uint64_t u2 = load64_le(b + 24U);
  ws0[3U] = u2;
  uint64_t u3 = load64_le(b + 32U);
  ws0[4U] = u3;
  uint64_t u4 = load64_le(b + 40U);
  ws0[5U] = u4;
  uint64_t u5 = load64_le(b + 48U);
  ws0[6U] = u5;
  uint64_t u6 = load64_le(b + 56U);
  ws0[7U] = u6;
  uint64_t u7 = load64_le(b + 64U);
  ws0[8U] = u7;
  uint64_t u8 = load64_le(b + 72U);
  ws0[9U] = u8;
  uint64_t u9 = load64_le(b + 80U);
  ws0[10U] = u9;
  uint64_t u10 = load64_le(b + 88U);
  ws0[11U] = u10;
  uint64_t u11 = load64_le(b + 96U);
  ws0[12U] = u11;
  uint64_t u12 = load64_le(b + 104U);
  ws0[13U] = u12;
  uint64_t u13 = load64_le(b + 112U);
  ws0[14U] = u13;
  uint64_t u14 = load64_le(b + 120U);
  ws0[15U] = u14;
  uint64_t u15 = load64_le(b + 128U);
  ws0[16U] = u15;
  uint64_t u16 = load64_le(b + 136U);
  ws0[17U] = u16;
  uint64_t u17 = load64_le(b + 144U);
  ws0[18U] = u17;
  uint64_t u18 = load64_le(b + 152U);
  ws0[19U] = u18;
  uint64_t u19 = load64_le(b + 160U);
  ws0[20U] = u19;
  uint64_t u20 = load64_le(b + 168U);
  ws0[21U] = u20;
  uint64_t u21 = load64_le(b + 176U);
  ws0[22U] = u21;
  uint64_t u22 = load64_le(b + 184U);
  ws0[23U] = u22;
  uint64_t u23 = load64_le(b + 192U);
  ws0[24U] = u23;
  uint64_t u24 = load64_le(b + 200U);
  ws0[25U] = u24;
  uint64_t u25 = load64_le(b + 208U);
  ws0[26U] = u25;
  uint64_t u26 = load64_le(b + 216U);
  ws0[27U] = u26;
  uint64_t u27 = load64_le(b + 224U);
  ws0[28U] = u27;
  uint64_t u28 = load64_le(b + 232U);
  ws0[29U] = u28;
  uint64_t u29 = load64_le(b + 240U);
  ws0[30U] = u29;
  uint64_t u30 = load64_le(b + 248U);
  ws0[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b3 = b2;
  uint8_t *b0 = b3;
  b0[rateInBytes1 - 1U] = 0x80U;
  absorb_inner_32(b3, s);
  for (uint32_t i0 = 0U; i0 < outputByteLen / rateInBytes1; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, s, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b02 = rb;
    memcpy(b02 + i0 * rateInBytes1, hbuf, rateInBytes1 * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      for (uint32_t i = 0U; i < 5U; i++)
      {
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
      }
      for (uint32_t i2 = 0U; i2 < 5U; i2++)
      {
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        for (uint32_t i = 0U; i < 5U; i++)
        {
          s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;
        }
      }
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____1 = current;
        s[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      for (uint32_t i = 0U; i < 5U; i++)
      {
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;
      }
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint32_t remOut = outputByteLen % rateInBytes1;
  uint8_t hbuf[256U] = { 0U };
  uint64_t ws[32U] = { 0U };
  memcpy(ws, s, 25U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    store64_le(hbuf + i * 8U, ws[i]);
  }
  memcpy(rb + outputByteLen - remOut, hbuf, remOut * sizeof (uint8_t));
}

static void sha3_224(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 144U;
  for (uint32_t i = 0U; i < inputByteLen / rateInBytes1; i++)
  {
    uint8_t b[256U] = { 0U };
    uint8_t *b_ = b;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    absorb_inner_32(b_, s);
  }
  uint8_t b1[256U] = { 0U };
  uint8_t *b_ = b1;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u = load64_le(b);
  ws0[0U] = u;
  uint64_t u0 = load64_le(b + 8U);
  ws0[1U] = u0;
  uint64_t u1 = load64_le(b + 16U);
  ws0[2U] = u1;
  uint64_t u2 = load64_le(b + 24U);
  ws0[3U] = u2;
  uint64_t u3 = load64_le(b + 32U);
  ws0[4U] = u3;
  uint64_t u4 = load64_le(b + 40U);
  ws0[5U] = u4;
  uint64_t u5 = load64_le(b + 48U);
  ws0[6U] = u5;
  uint64_t u6 = load64_le(b + 56U);
  ws0[7U] = u6;
  uint64_t u7 = load64_le(b + 64U);
  ws0[8U] = u7;
  uint64_t u8 = load64_le(b + 72U);
  ws0[9U] = u8;
  uint64_t u9 = load64_le(b + 80U);
  ws0[10U] = u9;
  uint64_t u10 = load64_le(b + 88U);
  ws0[11U] = u10;
  uint64_t u11 = load64_le(b + 96U);
  ws0[12U] = u11;
  uint64_t u12 = load64_le(b + 104U);
  ws0[13U] = u12;
  uint64_t u13 = load64_le(b + 112U);
  ws0[14U] = u13;
  uint64_t u14 = load64_le(b + 120U);
  ws0[15U] = u14;
  uint64_t u15 = load64_le(b + 128U);
  ws0[16U] = u15;
  uint64_t u16 = load64_le(b + 136U);
  ws0[17U] = u16;
  uint64_t u17 = load64_le(b + 144U);
  ws0[18U] = u17;
  uint64_t u18 = load64_le(b + 152U);
  ws0[19U] = u18;
  uint64_t u19 = load64_le(b + 160U);
  ws0[20U] = u19;
  uint64_t u20 = load64_le(b + 168U);
  ws0[21U] = u20;
  uint64_t u21 = load64_le(b + 176U);
  ws0[22U] = u21;
  uint64_t u22 = load64_le(b + 184U);
  ws0[23U] = u22;
  uint64_t u23 = load64_le(b + 192U);
  ws0[24U] = u23;
  uint64_t u24 = load64_le(b + 200U);
  ws0[25U] = u24;
  uint64_t u25 = load64_le(b + 208U);
  ws0[26U] = u25;
  uint64_t u26 = load64_le(b + 216U);
  ws0[27U] = u26;
  uint64_t u27 = load64_le(b + 224U);
  ws0[28U] = u27;
  uint64_t u28 = load64_le(b + 232U);
  ws0[29U] = u28;
  uint64_t u29 = load64_le(b + 240U);
  ws0[30U] = u29;
  uint64_t u30 = load64_le(b + 248U);
  ws0[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b3 = b2;
  uint8_t *b0 = b3;
  b0[rateInBytes1 - 1U] = 0x80U;
  absorb_inner_32(b3, s);
  for (uint32_t i0 = 0U; i0 < 28U / rateInBytes1; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, s, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b02 = rb;
    memcpy(b02 + i0 * rateInBytes1, hbuf, rateInBytes1 * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      for (uint32_t i = 0U; i < 5U; i++)
      {
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
      }
      for (uint32_t i2 = 0U; i2 < 5U; i2++)
      {
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        for (uint32_t i = 0U; i < 5U; i++)
        {
          s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;
        }
      }
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____1 = current;
        s[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      for (uint32_t i = 0U; i < 5U; i++)
      {
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;
      }
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint32_t remOut = 28U % rateInBytes1;
  uint8_t hbuf[256U] = { 0U };
  uint64_t ws[32U] = { 0U };
  memcpy(ws, s, 25U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    store64_le(hbuf + i * 8U, ws[i]);
  }
  memcpy(rb + 28U - remOut, hbuf, remOut * sizeof (uint8_t));
}

static void sha3_256(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 136U;
  for (uint32_t i = 0U; i < inputByteLen / rateInBytes1; i++)
  {
    uint8_t b[256U] = { 0U };
    uint8_t *b_ = b;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    absorb_inner_32(b_, s);
  }
  uint8_t b1[256U] = { 0U };
  uint8_t *b_ = b1;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u = load64_le(b);
  ws0[0U] = u;
  uint64_t u0 = load64_le(b + 8U);
  ws0[1U] = u0;
  uint64_t u1 = load64_le(b + 16U);
  ws0[2U] = u1;
  uint64_t u2 = load64_le(b + 24U);
  ws0[3U] = u2;
  uint64_t u3 = load64_le(b + 32U);
  ws0[4U] = u3;
  uint64_t u4 = load64_le(b + 40U);
  ws0[5U] = u4;
  uint64_t u5 = load64_le(b + 48U);
  ws0[6U] = u5;
  uint64_t u6 = load64_le(b + 56U);
  ws0[7U] = u6;
  uint64_t u7 = load64_le(b + 64U);
  ws0[8U] = u7;
  uint64_t u8 = load64_le(b + 72U);
  ws0[9U] = u8;
  uint64_t u9 = load64_le(b + 80U);
  ws0[10U] = u9;
  uint64_t u10 = load64_le(b + 88U);
  ws0[11U] = u10;
  uint64_t u11 = load64_le(b + 96U);
  ws0[12U] = u11;
  uint64_t u12 = load64_le(b + 104U);
  ws0[13U] = u12;
  uint64_t u13 = load64_le(b + 112U);
  ws0[14U] = u13;
  uint64_t u14 = load64_le(b + 120U);
  ws0[15U] = u14;
  uint64_t u15 = load64_le(b + 128U);
  ws0[16U] = u15;
  uint64_t u16 = load64_le(b + 136U);
  ws0[17U] = u16;
  uint64_t u17 = load64_le(b + 144U);
  ws0[18U] = u17;
  uint64_t u18 = load64_le(b + 152U);
  ws0[19U] = u18;
  uint64_t u19 = load64_le(b + 160U);
  ws0[20U] = u19;
  uint64_t u20 = load64_le(b + 168U);
  ws0[21U] = u20;
  uint64_t u21 = load64_le(b + 176U);
  ws0[22U] = u21;
  uint64_t u22 = load64_le(b + 184U);
  ws0[23U] = u22;
  uint64_t u23 = load64_le(b + 192U);
  ws0[24U] = u23;
  uint64_t u24 = load64_le(b + 200U);
  ws0[25U] = u24;
  uint64_t u25 = load64_le(b + 208U);
  ws0[26U] = u25;
  uint64_t u26 = load64_le(b + 216U);
  ws0[27U] = u26;
  uint64_t u27 = load64_le(b + 224U);
  ws0[28U] = u27;
  uint64_t u28 = load64_le(b + 232U);
  ws0[29U] = u28;
  uint64_t u29 = load64_le(b + 240U);
  ws0[30U] = u29;
  uint64_t u30 = load64_le(b + 248U);
  ws0[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b3 = b2;
  uint8_t *b0 = b3;
  b0[rateInBytes1 - 1U] = 0x80U;
  absorb_inner_32(b3, s);
  for (uint32_t i0 = 0U; i0 < 32U / rateInBytes1; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, s, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b02 = rb;
    memcpy(b02 + i0 * rateInBytes1, hbuf, rateInBytes1 * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      for (uint32_t i = 0U; i < 5U; i++)
      {
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
      }
      for (uint32_t i2 = 0U; i2 < 5U; i2++)
      {
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        for (uint32_t i = 0U; i < 5U; i++)
        {
          s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;
        }
      }
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____1 = current;
        s[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      for (uint32_t i = 0U; i < 5U; i++)
      {
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;
      }
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint32_t remOut = 32U % rateInBytes1;
  uint8_t hbuf[256U] = { 0U };
  uint64_t ws[32U] = { 0U };
  memcpy(ws, s, 25U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    store64_le(hbuf + i * 8U, ws[i]);
  }
  memcpy(rb + 32U - remOut, hbuf, remOut * sizeof (uint8_t));
}

static void sha3_384(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 104U;
  for (uint32_t i = 0U; i < inputByteLen / rateInBytes1; i++)
  {
    uint8_t b[256U] = { 0U };
    uint8_t *b_ = b;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    absorb_inner_32(b_, s);
  }
  uint8_t b1[256U] = { 0U };
  uint8_t *b_ = b1;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u = load64_le(b);
  ws0[0U] = u;
  uint64_t u0 = load64_le(b + 8U);
  ws0[1U] = u0;
  uint64_t u1 = load64_le(b + 16U);
  ws0[2U] = u1;
  uint64_t u2 = load64_le(b + 24U);
  ws0[3U] = u2;
  uint64_t u3 = load64_le(b + 32U);
  ws0[4U] = u3;
  uint64_t u4 = load64_le(b + 40U);
  ws0[5U] = u4;
  uint64_t u5 = load64_le(b + 48U);
  ws0[6U] = u5;
  uint64_t u6 = load64_le(b + 56U);
  ws0[7U] = u6;
  uint64_t u7 = load64_le(b + 64U);
  ws0[8U] = u7;
  uint64_t u8 = load64_le(b + 72U);
  ws0[9U] = u8;
  uint64_t u9 = load64_le(b + 80U);
  ws0[10U] = u9;
  uint64_t u10 = load64_le(b + 88U);
  ws0[11U] = u10;
  uint64_t u11 = load64_le(b + 96U);
  ws0[12U] = u11;
  uint64_t u12 = load64_le(b + 104U);
  ws0[13U] = u12;
  uint64_t u13 = load64_le(b + 112U);
  ws0[14U] = u13;
  uint64_t u14 = load64_le(b + 120U);
  ws0[15U] = u14;
  uint64_t u15 = load64_le(b + 128U);
  ws0[16U] = u15;
  uint64_t u16 = load64_le(b + 136U);
  ws0[17U] = u16;
  uint64_t u17 = load64_le(b + 144U);
  ws0[18U] = u17;
  uint64_t u18 = load64_le(b + 152U);
  ws0[19U] = u18;
  uint64_t u19 = load64_le(b + 160U);
  ws0[20U] = u19;
  uint64_t u20 = load64_le(b + 168U);
  ws0[21U] = u20;
  uint64_t u21 = load64_le(b + 176U);
  ws0[22U] = u21;
  uint64_t u22 = load64_le(b + 184U);
  ws0[23U] = u22;
  uint64_t u23 = load64_le(b + 192U);
  ws0[24U] = u23;
  uint64_t u24 = load64_le(b + 200U);
  ws0[25U] = u24;
  uint64_t u25 = load64_le(b + 208U);
  ws0[26U] = u25;
  uint64_t u26 = load64_le(b + 216U);
  ws0[27U] = u26;
  uint64_t u27 = load64_le(b + 224U);
  ws0[28U] = u27;
  uint64_t u28 = load64_le(b + 232U);
  ws0[29U] = u28;
  uint64_t u29 = load64_le(b + 240U);
  ws0[30U] = u29;
  uint64_t u30 = load64_le(b + 248U);
  ws0[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b3 = b2;
  uint8_t *b0 = b3;
  b0[rateInBytes1 - 1U] = 0x80U;
  absorb_inner_32(b3, s);
  for (uint32_t i0 = 0U; i0 < 48U / rateInBytes1; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, s, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b02 = rb;
    memcpy(b02 + i0 * rateInBytes1, hbuf, rateInBytes1 * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      for (uint32_t i = 0U; i < 5U; i++)
      {
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
      }
      for (uint32_t i2 = 0U; i2 < 5U; i2++)
      {
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        for (uint32_t i = 0U; i < 5U; i++)
        {
          s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;
        }
      }
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____1 = current;
        s[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      for (uint32_t i = 0U; i < 5U; i++)
      {
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;
      }
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint32_t remOut = 48U % rateInBytes1;
  uint8_t hbuf[256U] = { 0U };
  uint64_t ws[32U] = { 0U };
  memcpy(ws, s, 25U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    store64_le(hbuf + i * 8U, ws[i]);
  }
  memcpy(rb + 48U - remOut, hbuf, remOut * sizeof (uint8_t));
}

static void sha3_512(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 72U;
  for (uint32_t i = 0U; i < inputByteLen / rateInBytes1; i++)
  {
    uint8_t b[256U] = { 0U };
    uint8_t *b_ = b;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    absorb_inner_32(b_, s);
  }
  uint8_t b1[256U] = { 0U };
  uint8_t *b_ = b1;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u = load64_le(b);
  ws0[0U] = u;
  uint64_t u0 = load64_le(b + 8U);
  ws0[1U] = u0;
  uint64_t u1 = load64_le(b + 16U);
  ws0[2U] = u1;
  uint64_t u2 = load64_le(b + 24U);
  ws0[3U] = u2;
  uint64_t u3 = load64_le(b + 32U);
  ws0[4U] = u3;
  uint64_t u4 = load64_le(b + 40U);
  ws0[5U] = u4;
  uint64_t u5 = load64_le(b + 48U);
  ws0[6U] = u5;
  uint64_t u6 = load64_le(b + 56U);
  ws0[7U] = u6;
  uint64_t u7 = load64_le(b + 64U);
  ws0[8U] = u7;
  uint64_t u8 = load64_le(b + 72U);
  ws0[9U] = u8;
  uint64_t u9 = load64_le(b + 80U);
  ws0[10U] = u9;
  uint64_t u10 = load64_le(b + 88U);
  ws0[11U] = u10;
  uint64_t u11 = load64_le(b + 96U);
  ws0[12U] = u11;
  uint64_t u12 = load64_le(b + 104U);
  ws0[13U] = u12;
  uint64_t u13 = load64_le(b + 112U);
  ws0[14U] = u13;
  uint64_t u14 = load64_le(b + 120U);
  ws0[15U] = u14;
  uint64_t u15 = load64_le(b + 128U);
  ws0[16U] = u15;
  uint64_t u16 = load64_le(b + 136U);
  ws0[17U] = u16;
  uint64_t u17 = load64_le(b + 144U);
  ws0[18U] = u17;
  uint64_t u18 = load64_le(b + 152U);
  ws0[19U] = u18;
  uint64_t u19 = load64_le(b + 160U);
  ws0[20U] = u19;
  uint64_t u20 = load64_le(b + 168U);
  ws0[21U] = u20;
  uint64_t u21 = load64_le(b + 176U);
  ws0[22U] = u21;
  uint64_t u22 = load64_le(b + 184U);
  ws0[23U] = u22;
  uint64_t u23 = load64_le(b + 192U);
  ws0[24U] = u23;
  uint64_t u24 = load64_le(b + 200U);
  ws0[25U] = u24;
  uint64_t u25 = load64_le(b + 208U);
  ws0[26U] = u25;
  uint64_t u26 = load64_le(b + 216U);
  ws0[27U] = u26;
  uint64_t u27 = load64_le(b + 224U);
  ws0[28U] = u27;
  uint64_t u28 = load64_le(b + 232U);
  ws0[29U] = u28;
  uint64_t u29 = load64_le(b + 240U);
  ws0[30U] = u29;
  uint64_t u30 = load64_le(b + 248U);
  ws0[31U] = u30;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b3 = b2;
  uint8_t *b0 = b3;
  b0[rateInBytes1 - 1U] = 0x80U;
  absorb_inner_32(b3, s);
  for (uint32_t i0 = 0U; i0 < 64U / rateInBytes1; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, s, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b02 = rb;
    memcpy(b02 + i0 * rateInBytes1, hbuf, rateInBytes1 * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      for (uint32_t i = 0U; i < 5U; i++)
      {
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U])));
      }
      for (uint32_t i2 = 0U; i2 < 5U; i2++)
      {
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        for (uint32_t i = 0U; i < 5U; i++)
        {
          s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;
        }
      }
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____1 = current;
        s[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      for (uint32_t i = 0U; i < 5U; i++)
      {
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;
      }
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint32_t remOut = 64U % rateInBytes1;
  uint8_t hbuf[256U] = { 0U };
  uint64_t ws[32U] = { 0U };
  memcpy(ws, s, 25U * sizeof (uint64_t));
  for (uint32_t i = 0U; i < 32U; i++)
  {
    store64_le(hbuf + i * 8U, ws[i]);
  }
  memcpy(rb + 64U - remOut, hbuf, remOut * sizeof (uint8_t));
}

extern bool
Lib_PrintBuffer_result_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);

static void
test_sha3(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *expected224,
  uint8_t *expected256,
  uint8_t *expected384,
  uint8_t *expected512
)
{
  uint8_t test224[28U] = { 0U };
  uint8_t test256[32U] = { 0U };
  uint8_t test384[48U] = { 0U };
  uint8_t test512[64U] = { 0U };
  sha3_224(test224, msg, msg_len);
  sha3_256(test256, msg, msg_len);
  sha3_384(test384, msg, msg_len);
  sha3_512(test512, msg, msg_len);
  if (!Lib_PrintBuffer_result_compare_display(28U, test224, expected224))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display(32U, test256, expected256))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display(48U, test384, expected384))
  {
    exit((int32_t)255);
  }
  if (!Lib_PrintBuffer_result_compare_display(64U, test512, expected512))
  {
    exit((int32_t)255);
  }
}

static void test_shake128(uint32_t msg_len, uint8_t *msg, uint32_t out_len, uint8_t *expected)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), out_len);
  uint8_t test[out_len];
  memset(test, 0U, out_len * sizeof (uint8_t));
  shake128(test, out_len, msg, msg_len);
  if (!Lib_PrintBuffer_result_compare_display(out_len, test, expected))
  {
    exit((int32_t)255);
  }
}

static void test_shake256(uint32_t msg_len, uint8_t *msg, uint32_t out_len, uint8_t *expected)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), out_len);
  uint8_t test[out_len];
  memset(test, 0U, out_len * sizeof (uint8_t));
  shake256(test, out_len, msg, msg_len);
  if (!Lib_PrintBuffer_result_compare_display(out_len, test, expected))
  {
    exit((int32_t)255);
  }
}

static uint8_t test1_plaintext[0U] = {  };

static uint8_t
test1_expected_sha3_224[28U] =
  {
    0x6bU, 0x4eU, 0x03U, 0x42U, 0x36U, 0x67U, 0xdbU, 0xb7U, 0x3bU, 0x6eU, 0x15U, 0x45U, 0x4fU,
    0x0eU, 0xb1U, 0xabU, 0xd4U, 0x59U, 0x7fU, 0x9aU, 0x1bU, 0x07U, 0x8eU, 0x3fU, 0x5bU, 0x5aU,
    0x6bU, 0xc7U
  };

static uint8_t
test1_expected_sha3_256[32U] =
  {
    0xa7U, 0xffU, 0xc6U, 0xf8U, 0xbfU, 0x1eU, 0xd7U, 0x66U, 0x51U, 0xc1U, 0x47U, 0x56U, 0xa0U,
    0x61U, 0xd6U, 0x62U, 0xf5U, 0x80U, 0xffU, 0x4dU, 0xe4U, 0x3bU, 0x49U, 0xfaU, 0x82U, 0xd8U,
    0x0aU, 0x4bU, 0x80U, 0xf8U, 0x43U, 0x4aU
  };

static uint8_t
test1_expected_sha3_384[48U] =
  {
    0x0cU, 0x63U, 0xa7U, 0x5bU, 0x84U, 0x5eU, 0x4fU, 0x7dU, 0x01U, 0x10U, 0x7dU, 0x85U, 0x2eU,
    0x4cU, 0x24U, 0x85U, 0xc5U, 0x1aU, 0x50U, 0xaaU, 0xaaU, 0x94U, 0xfcU, 0x61U, 0x99U, 0x5eU,
    0x71U, 0xbbU, 0xeeU, 0x98U, 0x3aU, 0x2aU, 0xc3U, 0x71U, 0x38U, 0x31U, 0x26U, 0x4aU, 0xdbU,
    0x47U, 0xfbU, 0x6bU, 0xd1U, 0xe0U, 0x58U, 0xd5U, 0xf0U, 0x04U
  };

static uint8_t
test1_expected_sha3_512[64U] =
  {
    0xa6U, 0x9fU, 0x73U, 0xccU, 0xa2U, 0x3aU, 0x9aU, 0xc5U, 0xc8U, 0xb5U, 0x67U, 0xdcU, 0x18U,
    0x5aU, 0x75U, 0x6eU, 0x97U, 0xc9U, 0x82U, 0x16U, 0x4fU, 0xe2U, 0x58U, 0x59U, 0xe0U, 0xd1U,
    0xdcU, 0xc1U, 0x47U, 0x5cU, 0x80U, 0xa6U, 0x15U, 0xb2U, 0x12U, 0x3aU, 0xf1U, 0xf5U, 0xf9U,
    0x4cU, 0x11U, 0xe3U, 0xe9U, 0x40U, 0x2cU, 0x3aU, 0xc5U, 0x58U, 0xf5U, 0x00U, 0x19U, 0x9dU,
    0x95U, 0xb6U, 0xd3U, 0xe3U, 0x01U, 0x75U, 0x85U, 0x86U, 0x28U, 0x1dU, 0xcdU, 0x26U
  };

static uint8_t test2_plaintext[3U] = { 0x61U, 0x62U, 0x63U };

static uint8_t
test2_expected_sha3_224[28U] =
  {
    0xe6U, 0x42U, 0x82U, 0x4cU, 0x3fU, 0x8cU, 0xf2U, 0x4aU, 0xd0U, 0x92U, 0x34U, 0xeeU, 0x7dU,
    0x3cU, 0x76U, 0x6fU, 0xc9U, 0xa3U, 0xa5U, 0x16U, 0x8dU, 0x0cU, 0x94U, 0xadU, 0x73U, 0xb4U,
    0x6fU, 0xdfU
  };

static uint8_t
test2_expected_sha3_256[32U] =
  {
    0x3aU, 0x98U, 0x5dU, 0xa7U, 0x4fU, 0xe2U, 0x25U, 0xb2U, 0x04U, 0x5cU, 0x17U, 0x2dU, 0x6bU,
    0xd3U, 0x90U, 0xbdU, 0x85U, 0x5fU, 0x08U, 0x6eU, 0x3eU, 0x9dU, 0x52U, 0x5bU, 0x46U, 0xbfU,
    0xe2U, 0x45U, 0x11U, 0x43U, 0x15U, 0x32U
  };

static uint8_t
test2_expected_sha3_384[48U] =
  {
    0xecU, 0x01U, 0x49U, 0x82U, 0x88U, 0x51U, 0x6fU, 0xc9U, 0x26U, 0x45U, 0x9fU, 0x58U, 0xe2U,
    0xc6U, 0xadU, 0x8dU, 0xf9U, 0xb4U, 0x73U, 0xcbU, 0x0fU, 0xc0U, 0x8cU, 0x25U, 0x96U, 0xdaU,
    0x7cU, 0xf0U, 0xe4U, 0x9bU, 0xe4U, 0xb2U, 0x98U, 0xd8U, 0x8cU, 0xeaU, 0x92U, 0x7aU, 0xc7U,
    0xf5U, 0x39U, 0xf1U, 0xedU, 0xf2U, 0x28U, 0x37U, 0x6dU, 0x25U
  };

static uint8_t
test2_expected_sha3_512[64U] =
  {
    0xb7U, 0x51U, 0x85U, 0x0bU, 0x1aU, 0x57U, 0x16U, 0x8aU, 0x56U, 0x93U, 0xcdU, 0x92U, 0x4bU,
    0x6bU, 0x09U, 0x6eU, 0x08U, 0xf6U, 0x21U, 0x82U, 0x74U, 0x44U, 0xf7U, 0x0dU, 0x88U, 0x4fU,
    0x5dU, 0x02U, 0x40U, 0xd2U, 0x71U, 0x2eU, 0x10U, 0xe1U, 0x16U, 0xe9U, 0x19U, 0x2aU, 0xf3U,
    0xc9U, 0x1aU, 0x7eU, 0xc5U, 0x76U, 0x47U, 0xe3U, 0x93U, 0x40U, 0x57U, 0x34U, 0x0bU, 0x4cU,
    0xf4U, 0x08U, 0xd5U, 0xa5U, 0x65U, 0x92U, 0xf8U, 0x27U, 0x4eU, 0xecU, 0x53U, 0xf0U
  };

static uint8_t
test3_plaintext[56U] =
  {
    0x61U, 0x62U, 0x63U, 0x64U, 0x62U, 0x63U, 0x64U, 0x65U, 0x63U, 0x64U, 0x65U, 0x66U, 0x64U,
    0x65U, 0x66U, 0x67U, 0x65U, 0x66U, 0x67U, 0x68U, 0x66U, 0x67U, 0x68U, 0x69U, 0x67U, 0x68U,
    0x69U, 0x6aU, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6aU, 0x6bU, 0x6cU,
    0x6dU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x6dU, 0x6eU, 0x6fU, 0x70U,
    0x6eU, 0x6fU, 0x70U, 0x71U
  };

static uint8_t
test3_expected_sha3_224[28U] =
  {
    0x8aU, 0x24U, 0x10U, 0x8bU, 0x15U, 0x4aU, 0xdaU, 0x21U, 0xc9U, 0xfdU, 0x55U, 0x74U, 0x49U,
    0x44U, 0x79U, 0xbaU, 0x5cU, 0x7eU, 0x7aU, 0xb7U, 0x6eU, 0xf2U, 0x64U, 0xeaU, 0xd0U, 0xfcU,
    0xceU, 0x33U
  };

static uint8_t
test3_expected_sha3_256[32U] =
  {
    0x41U, 0xc0U, 0xdbU, 0xa2U, 0xa9U, 0xd6U, 0x24U, 0x08U, 0x49U, 0x10U, 0x03U, 0x76U, 0xa8U,
    0x23U, 0x5eU, 0x2cU, 0x82U, 0xe1U, 0xb9U, 0x99U, 0x8aU, 0x99U, 0x9eU, 0x21U, 0xdbU, 0x32U,
    0xddU, 0x97U, 0x49U, 0x6dU, 0x33U, 0x76U
  };

static uint8_t
test3_expected_sha3_384[48U] =
  {
    0x99U, 0x1cU, 0x66U, 0x57U, 0x55U, 0xebU, 0x3aU, 0x4bU, 0x6bU, 0xbdU, 0xfbU, 0x75U, 0xc7U,
    0x8aU, 0x49U, 0x2eU, 0x8cU, 0x56U, 0xa2U, 0x2cU, 0x5cU, 0x4dU, 0x7eU, 0x42U, 0x9bU, 0xfdU,
    0xbcU, 0x32U, 0xb9U, 0xd4U, 0xadU, 0x5aU, 0xa0U, 0x4aU, 0x1fU, 0x07U, 0x6eU, 0x62U, 0xfeU,
    0xa1U, 0x9eU, 0xefU, 0x51U, 0xacU, 0xd0U, 0x65U, 0x7cU, 0x22U
  };

static uint8_t
test3_expected_sha3_512[64U] =
  {
    0x04U, 0xa3U, 0x71U, 0xe8U, 0x4eU, 0xcfU, 0xb5U, 0xb8U, 0xb7U, 0x7cU, 0xb4U, 0x86U, 0x10U,
    0xfcU, 0xa8U, 0x18U, 0x2dU, 0xd4U, 0x57U, 0xceU, 0x6fU, 0x32U, 0x6aU, 0x0fU, 0xd3U, 0xd7U,
    0xecU, 0x2fU, 0x1eU, 0x91U, 0x63U, 0x6dU, 0xeeU, 0x69U, 0x1fU, 0xbeU, 0x0cU, 0x98U, 0x53U,
    0x02U, 0xbaU, 0x1bU, 0x0dU, 0x8dU, 0xc7U, 0x8cU, 0x08U, 0x63U, 0x46U, 0xb5U, 0x33U, 0xb4U,
    0x9cU, 0x03U, 0x0dU, 0x99U, 0xa2U, 0x7dU, 0xafU, 0x11U, 0x39U, 0xd6U, 0xe7U, 0x5eU
  };

static uint8_t
test4_plaintext[112U] =
  {
    0x61U, 0x62U, 0x63U, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U, 0x62U, 0x63U, 0x64U, 0x65U, 0x66U,
    0x67U, 0x68U, 0x69U, 0x63U, 0x64U, 0x65U, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x64U, 0x65U,
    0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x65U, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU,
    0x6cU, 0x66U, 0x67U, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x67U, 0x68U, 0x69U, 0x6aU,
    0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x68U, 0x69U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x69U,
    0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x6aU, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU,
    0x70U, 0x71U, 0x6bU, 0x6cU, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x6cU, 0x6dU, 0x6eU,
    0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x6dU, 0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x74U,
    0x6eU, 0x6fU, 0x70U, 0x71U, 0x72U, 0x73U, 0x74U, 0x75U
  };

static uint8_t
test4_expected_sha3_224[28U] =
  {
    0x54U, 0x3eU, 0x68U, 0x68U, 0xe1U, 0x66U, 0x6cU, 0x1aU, 0x64U, 0x36U, 0x30U, 0xdfU, 0x77U,
    0x36U, 0x7aU, 0xe5U, 0xa6U, 0x2aU, 0x85U, 0x07U, 0x0aU, 0x51U, 0xc1U, 0x4cU, 0xbfU, 0x66U,
    0x5cU, 0xbcU
  };

static uint8_t
test4_expected_sha3_256[32U] =
  {
    0x91U, 0x6fU, 0x60U, 0x61U, 0xfeU, 0x87U, 0x97U, 0x41U, 0xcaU, 0x64U, 0x69U, 0xb4U, 0x39U,
    0x71U, 0xdfU, 0xdbU, 0x28U, 0xb1U, 0xa3U, 0x2dU, 0xc3U, 0x6cU, 0xb3U, 0x25U, 0x4eU, 0x81U,
    0x2bU, 0xe2U, 0x7aU, 0xadU, 0x1dU, 0x18U
  };

static uint8_t
test4_expected_sha3_384[48U] =
  {
    0x79U, 0x40U, 0x7dU, 0x3bU, 0x59U, 0x16U, 0xb5U, 0x9cU, 0x3eU, 0x30U, 0xb0U, 0x98U, 0x22U,
    0x97U, 0x47U, 0x91U, 0xc3U, 0x13U, 0xfbU, 0x9eU, 0xccU, 0x84U, 0x9eU, 0x40U, 0x6fU, 0x23U,
    0x59U, 0x2dU, 0x04U, 0xf6U, 0x25U, 0xdcU, 0x8cU, 0x70U, 0x9bU, 0x98U, 0xb4U, 0x3bU, 0x38U,
    0x52U, 0xb3U, 0x37U, 0x21U, 0x61U, 0x79U, 0xaaU, 0x7fU, 0xc7U
  };

static uint8_t
test4_expected_sha3_512[64U] =
  {
    0xafU, 0xebU, 0xb2U, 0xefU, 0x54U, 0x2eU, 0x65U, 0x79U, 0xc5U, 0x0cU, 0xadU, 0x06U, 0xd2U,
    0xe5U, 0x78U, 0xf9U, 0xf8U, 0xddU, 0x68U, 0x81U, 0xd7U, 0xdcU, 0x82U, 0x4dU, 0x26U, 0x36U,
    0x0fU, 0xeeU, 0xbfU, 0x18U, 0xa4U, 0xfaU, 0x73U, 0xe3U, 0x26U, 0x11U, 0x22U, 0x94U, 0x8eU,
    0xfcU, 0xfdU, 0x49U, 0x2eU, 0x74U, 0xe8U, 0x2eU, 0x21U, 0x89U, 0xedU, 0x0fU, 0xb4U, 0x40U,
    0xd1U, 0x87U, 0xf3U, 0x82U, 0x27U, 0x0cU, 0xb4U, 0x55U, 0xf2U, 0x1dU, 0xd1U, 0x85U
  };

static uint8_t test5_plaintext_shake128[0U] = {  };

static uint8_t
test5_expected_shake128[16U] =
  {
    0x7fU, 0x9cU, 0x2bU, 0xa4U, 0xe8U, 0x8fU, 0x82U, 0x7dU, 0x61U, 0x60U, 0x45U, 0x50U, 0x76U,
    0x05U, 0x85U, 0x3eU
  };

static uint8_t
test6_plaintext_shake128[14U] =
  {
    0x52U, 0x97U, 0x7eU, 0x53U, 0x2bU, 0xccU, 0xdbU, 0x89U, 0xdfU, 0xefU, 0xf7U, 0xe9U, 0xe4U,
    0xadU
  };

static uint8_t
test6_expected_shake128[16U] =
  {
    0xfbU, 0xfbU, 0xa5U, 0xc1U, 0xe1U, 0x79U, 0xdfU, 0x14U, 0x69U, 0xfcU, 0xc8U, 0x58U, 0x8aU,
    0xe5U, 0xd2U, 0xccU
  };

static uint8_t
test7_plaintext_shake128[34U] =
  {
    0x4aU, 0x20U, 0x6aU, 0x5bU, 0x8aU, 0xa3U, 0x58U, 0x6cU, 0x06U, 0x67U, 0xa4U, 0x00U, 0x20U,
    0xd6U, 0x5fU, 0xf5U, 0x11U, 0xd5U, 0x2bU, 0x73U, 0x2eU, 0xf7U, 0xa0U, 0xc5U, 0x69U, 0xf1U,
    0xeeU, 0x68U, 0x1aU, 0x4fU, 0xc3U, 0x62U, 0x00U, 0x65U
  };

static uint8_t
test7_expected_shake128[16U] =
  {
    0x7bU, 0xb4U, 0x33U, 0x75U, 0x2bU, 0x98U, 0xf9U, 0x15U, 0xbeU, 0x51U, 0x82U, 0xbcU, 0x1fU,
    0x09U, 0x66U, 0x48U
  };

static uint8_t
test8_plaintext_shake128[83U] =
  {
    0x24U, 0x69U, 0xf1U, 0x01U, 0xc9U, 0xb4U, 0x99U, 0xa9U, 0x30U, 0xa9U, 0x7eU, 0xf1U, 0xb3U,
    0x46U, 0x73U, 0xecU, 0x74U, 0x39U, 0x3fU, 0xd9U, 0xfaU, 0xf6U, 0x58U, 0xe3U, 0x1fU, 0x06U,
    0xeeU, 0x0bU, 0x29U, 0xa2U, 0x2bU, 0x62U, 0x37U, 0x80U, 0xbaU, 0x7bU, 0xdfU, 0xedU, 0x86U,
    0x20U, 0x15U, 0x1cU, 0xc4U, 0x44U, 0x4eU, 0xbeU, 0x33U, 0x39U, 0xe6U, 0xd2U, 0xa2U, 0x23U,
    0xbfU, 0xbfU, 0xb4U, 0xadU, 0x2cU, 0xa0U, 0xe0U, 0xfaU, 0x0dU, 0xdfU, 0xbbU, 0xdfU, 0x3bU,
    0x05U, 0x7aU, 0x4fU, 0x26U, 0xd0U, 0xb2U, 0x16U, 0xbcU, 0x87U, 0x63U, 0xcaU, 0x8dU, 0x8aU,
    0x35U, 0xffU, 0x2dU, 0x2dU, 0x01U
  };

static uint8_t
test8_expected_shake128[16U] =
  {
    0x00U, 0xffU, 0x5eU, 0xf0U, 0xcdU, 0x7fU, 0x8fU, 0x90U, 0xadU, 0x94U, 0xb7U, 0x97U, 0xe9U,
    0xd4U, 0xddU, 0x30U
  };

static uint8_t test9_plaintext_shake256[0U] = {  };

static uint8_t
test9_expected_shake256[32U] =
  {
    0x46U, 0xb9U, 0xddU, 0x2bU, 0x0bU, 0xa8U, 0x8dU, 0x13U, 0x23U, 0x3bU, 0x3fU, 0xebU, 0x74U,
    0x3eU, 0xebU, 0x24U, 0x3fU, 0xcdU, 0x52U, 0xeaU, 0x62U, 0xb8U, 0x1bU, 0x82U, 0xb5U, 0x0cU,
    0x27U, 0x64U, 0x6eU, 0xd5U, 0x76U, 0x2fU
  };

static uint8_t
test10_plaintext_shake256[17U] =
  {
    0xf9U, 0xdaU, 0x78U, 0xc8U, 0x90U, 0x84U, 0x70U, 0x40U, 0x45U, 0x4bU, 0xa6U, 0x42U, 0x98U,
    0x82U, 0xb0U, 0x54U, 0x09U
  };

static uint8_t
test10_expected_shake256[32U] =
  {
    0xa8U, 0x49U, 0x83U, 0xc9U, 0xfeU, 0x75U, 0xadU, 0x0dU, 0xe1U, 0x9eU, 0x2cU, 0x84U, 0x20U,
    0xa7U, 0xeaU, 0x85U, 0xb2U, 0x51U, 0x02U, 0x19U, 0x56U, 0x14U, 0xdfU, 0xa5U, 0x34U, 0x7dU,
    0xe6U, 0x0aU, 0x1cU, 0xe1U, 0x3bU, 0x60U
  };

static uint8_t
test11_plaintext_shake256[32U] =
  {
    0xefU, 0x89U, 0x6cU, 0xdcU, 0xb3U, 0x63U, 0xa6U, 0x15U, 0x91U, 0x78U, 0xa1U, 0xbbU, 0x1cU,
    0x99U, 0x39U, 0x46U, 0xc5U, 0x04U, 0x02U, 0x09U, 0x5cU, 0xdaU, 0xeaU, 0x4fU, 0xd4U, 0xd4U,
    0x19U, 0xaaU, 0x47U, 0x32U, 0x1cU, 0x88U
  };

static uint8_t
test11_expected_shake256[32U] =
  {
    0x7aU, 0xbbU, 0xa4U, 0xe8U, 0xb8U, 0xddU, 0x76U, 0x6bU, 0xbaU, 0xbeU, 0x98U, 0xf8U, 0xf1U,
    0x69U, 0xcbU, 0x62U, 0x08U, 0x67U, 0x4dU, 0xe1U, 0x9aU, 0x51U, 0xd7U, 0x3cU, 0x92U, 0xb7U,
    0xdcU, 0x04U, 0xa4U, 0xb5U, 0xeeU, 0x3dU
  };

static uint8_t
test12_plaintext_shake256[78U] =
  {
    0xdeU, 0x70U, 0x1fU, 0x10U, 0xadU, 0x39U, 0x61U, 0xb0U, 0xdaU, 0xccU, 0x96U, 0x87U, 0x3aU,
    0x3cU, 0xd5U, 0x58U, 0x55U, 0x81U, 0x88U, 0xffU, 0x69U, 0x6dU, 0x85U, 0x01U, 0xb2U, 0xe2U,
    0x7bU, 0x67U, 0xe9U, 0x41U, 0x90U, 0xcdU, 0x0bU, 0x25U, 0x48U, 0xb6U, 0x5bU, 0x52U, 0xa9U,
    0x22U, 0xaaU, 0xe8U, 0x9dU, 0x63U, 0xd6U, 0xddU, 0x97U, 0x2cU, 0x91U, 0xa9U, 0x79U, 0xebU,
    0x63U, 0x43U, 0xb6U, 0x58U, 0xf2U, 0x4dU, 0xb3U, 0x4eU, 0x82U, 0x8bU, 0x74U, 0xdbU, 0xb8U,
    0x9aU, 0x74U, 0x93U, 0xa3U, 0xdfU, 0xd4U, 0x29U, 0xfdU, 0xbdU, 0xb8U, 0x40U, 0xadU, 0x0bU
  };

static uint8_t
test12_expected_shake256[32U] =
  {
    0x64U, 0x2fU, 0x3fU, 0x23U, 0x5aU, 0xc7U, 0xe3U, 0xd4U, 0x34U, 0x06U, 0x3bU, 0x5fU, 0xc9U,
    0x21U, 0x5fU, 0xc3U, 0xf0U, 0xe5U, 0x91U, 0xe2U, 0xe7U, 0xfdU, 0x17U, 0x66U, 0x8dU, 0x1aU,
    0x0cU, 0x87U, 0x46U, 0x87U, 0x35U, 0xc2U
  };

exit_code main(void)
{
  C_String_print("\nTEST 1. SHA3\n");
  test_sha3(0U,
    test1_plaintext,
    test1_expected_sha3_224,
    test1_expected_sha3_256,
    test1_expected_sha3_384,
    test1_expected_sha3_512);
  C_String_print("\nTEST 2. SHA3\n");
  test_sha3(3U,
    test2_plaintext,
    test2_expected_sha3_224,
    test2_expected_sha3_256,
    test2_expected_sha3_384,
    test2_expected_sha3_512);
  C_String_print("\nTEST 3. SHA3\n");
  test_sha3(56U,
    test3_plaintext,
    test3_expected_sha3_224,
    test3_expected_sha3_256,
    test3_expected_sha3_384,
    test3_expected_sha3_512);
  C_String_print("\nTEST 4. SHA3\n");
  test_sha3(112U,
    test4_plaintext,
    test4_expected_sha3_224,
    test4_expected_sha3_256,
    test4_expected_sha3_384,
    test4_expected_sha3_512);
  C_String_print("\nTEST 5. SHAKE128\n");
  test_shake128(0U, test5_plaintext_shake128, 16U, test5_expected_shake128);
  C_String_print("\nTEST 6. SHAKE128\n");
  test_shake128(14U, test6_plaintext_shake128, 16U, test6_expected_shake128);
  C_String_print("\nTEST 7. SHAKE128\n");
  test_shake128(34U, test7_plaintext_shake128, 16U, test7_expected_shake128);
  C_String_print("\nTEST 8. SHAKE128\n");
  test_shake128(83U, test8_plaintext_shake128, 16U, test8_expected_shake128);
  C_String_print("\nTEST 9. SHAKE256\n");
  test_shake256(0U, test9_plaintext_shake256, 32U, test9_expected_shake256);
  C_String_print("\nTEST 10. SHAKE256\n");
  test_shake256(17U, test10_plaintext_shake256, 32U, test10_expected_shake256);
  C_String_print("\nTEST 11. SHAKE256\n");
  test_shake256(32U, test11_plaintext_shake256, 32U, test11_expected_shake256);
  C_String_print("\nTEST 12. SHAKE256\n");
  test_shake256(78U, test12_plaintext_shake256, 32U, test12_expected_shake256);
  return EXIT_SUCCESS;
}

