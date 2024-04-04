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


#include "internal/Hacl_Hash_SHA3_Scalar.h"

const
uint32_t
Hacl_Impl_SHA3_Vec_keccak_rotc[24U] =
  {
    1U, 3U, 6U, 10U, 15U, 21U, 28U, 36U, 45U, 55U, 2U, 14U, 27U, 41U, 56U, 8U, 25U, 43U, 62U, 18U,
    39U, 61U, 20U, 44U
  };

const
uint32_t
Hacl_Impl_SHA3_Vec_keccak_piln[24U] =
  {
    10U, 7U, 11U, 17U, 18U, 3U, 5U, 16U, 8U, 21U, 24U, 4U, 15U, 23U, 19U, 13U, 12U, 2U, 20U, 14U,
    22U, 9U, 6U, 1U
  };

const
uint64_t
Hacl_Impl_SHA3_Vec_keccak_rndc[24U] =
  {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
  };

void
Hacl_Hash_SHA3_Scalar_shake128(
  uint8_t *output,
  uint32_t outputByteLen,
  uint8_t *input,
  uint32_t inputByteLen
)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 168U;
  for (uint32_t i0 = 0U; i0 < inputByteLen / rateInBytes1; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      s[i] = s[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x1FU;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws0[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws0[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws0[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws0[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws0[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws0[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws0[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws0[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws0[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws0[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws0[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws0[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws0[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws0[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws0[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws0[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws0[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws0[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws0[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws0[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws0[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws0[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws0[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws0[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws0[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws0[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws0[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws0[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws0[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws0[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws0[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws0[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[rateInBytes1 - 1U] = 0x80U;
  uint64_t ws1[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws1[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws1[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws1[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws1[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws1[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws1[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws1[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws1[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws1[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws1[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws1[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws1[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws1[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws1[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws1[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws1[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws1[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws1[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws1[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws1[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws1[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws1[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws1[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws1[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws1[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws1[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws1[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws1[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws1[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws1[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws1[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws1[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws1[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____2 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____2 << 1U | uu____2 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____3 = current;
      s[_Y] = uu____3 << r | uu____3 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____4 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____4 << 1U | uu____4 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____5 = current;
        s[_Y] = uu____5 << r | uu____5 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
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

void
Hacl_Hash_SHA3_Scalar_shake256(
  uint8_t *output,
  uint32_t outputByteLen,
  uint8_t *input,
  uint32_t inputByteLen
)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 136U;
  for (uint32_t i0 = 0U; i0 < inputByteLen / rateInBytes1; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      s[i] = s[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x1FU;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws0[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws0[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws0[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws0[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws0[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws0[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws0[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws0[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws0[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws0[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws0[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws0[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws0[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws0[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws0[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws0[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws0[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws0[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws0[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws0[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws0[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws0[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws0[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws0[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws0[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws0[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws0[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws0[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws0[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws0[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws0[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws0[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[rateInBytes1 - 1U] = 0x80U;
  uint64_t ws1[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws1[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws1[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws1[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws1[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws1[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws1[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws1[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws1[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws1[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws1[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws1[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws1[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws1[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws1[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws1[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws1[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws1[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws1[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws1[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws1[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws1[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws1[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws1[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws1[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws1[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws1[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws1[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws1[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws1[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws1[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws1[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws1[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws1[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____2 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____2 << 1U | uu____2 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____3 = current;
      s[_Y] = uu____3 << r | uu____3 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____4 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____4 << 1U | uu____4 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____5 = current;
        s[_Y] = uu____5 << r | uu____5 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
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

void Hacl_Hash_SHA3_Scalar_sha3_224(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 144U;
  for (uint32_t i0 = 0U; i0 < inputByteLen / rateInBytes1; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      s[i] = s[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws0[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws0[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws0[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws0[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws0[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws0[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws0[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws0[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws0[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws0[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws0[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws0[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws0[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws0[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws0[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws0[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws0[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws0[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws0[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws0[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws0[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws0[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws0[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws0[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws0[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws0[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws0[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws0[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws0[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws0[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws0[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws0[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[rateInBytes1 - 1U] = 0x80U;
  uint64_t ws1[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws1[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws1[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws1[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws1[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws1[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws1[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws1[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws1[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws1[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws1[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws1[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws1[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws1[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws1[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws1[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws1[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws1[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws1[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws1[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws1[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws1[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws1[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws1[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws1[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws1[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws1[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws1[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws1[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws1[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws1[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws1[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws1[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws1[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____2 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____2 << 1U | uu____2 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____3 = current;
      s[_Y] = uu____3 << r | uu____3 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____4 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____4 << 1U | uu____4 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____5 = current;
        s[_Y] = uu____5 << r | uu____5 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
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

void Hacl_Hash_SHA3_Scalar_sha3_256(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 136U;
  for (uint32_t i0 = 0U; i0 < inputByteLen / rateInBytes1; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      s[i] = s[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws0[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws0[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws0[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws0[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws0[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws0[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws0[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws0[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws0[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws0[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws0[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws0[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws0[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws0[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws0[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws0[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws0[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws0[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws0[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws0[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws0[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws0[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws0[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws0[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws0[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws0[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws0[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws0[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws0[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws0[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws0[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws0[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[rateInBytes1 - 1U] = 0x80U;
  uint64_t ws1[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws1[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws1[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws1[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws1[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws1[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws1[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws1[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws1[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws1[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws1[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws1[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws1[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws1[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws1[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws1[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws1[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws1[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws1[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws1[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws1[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws1[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws1[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws1[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws1[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws1[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws1[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws1[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws1[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws1[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws1[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws1[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws1[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws1[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____2 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____2 << 1U | uu____2 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____3 = current;
      s[_Y] = uu____3 << r | uu____3 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____4 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____4 << 1U | uu____4 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____5 = current;
        s[_Y] = uu____5 << r | uu____5 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
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

void Hacl_Hash_SHA3_Scalar_sha3_384(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 104U;
  for (uint32_t i0 = 0U; i0 < inputByteLen / rateInBytes1; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      s[i] = s[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws0[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws0[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws0[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws0[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws0[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws0[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws0[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws0[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws0[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws0[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws0[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws0[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws0[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws0[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws0[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws0[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws0[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws0[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws0[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws0[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws0[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws0[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws0[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws0[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws0[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws0[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws0[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws0[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws0[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws0[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws0[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws0[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[rateInBytes1 - 1U] = 0x80U;
  uint64_t ws1[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws1[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws1[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws1[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws1[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws1[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws1[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws1[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws1[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws1[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws1[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws1[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws1[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws1[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws1[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws1[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws1[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws1[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws1[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws1[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws1[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws1[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws1[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws1[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws1[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws1[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws1[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws1[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws1[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws1[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws1[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws1[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws1[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws1[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____2 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____2 << 1U | uu____2 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____3 = current;
      s[_Y] = uu____3 << r | uu____3 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____4 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____4 << 1U | uu____4 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____5 = current;
        s[_Y] = uu____5 << r | uu____5 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
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

void Hacl_Hash_SHA3_Scalar_sha3_512(uint8_t *output, uint8_t *input, uint32_t inputByteLen)
{
  uint8_t *ib = input;
  uint8_t *rb = output;
  uint64_t s[25U] = { 0U };
  uint32_t rateInBytes1 = 72U;
  for (uint32_t i0 = 0U; i0 < inputByteLen / rateInBytes1; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = ib;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * rateInBytes1, rateInBytes1 * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      s[i] = s[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      s[0U] = s[0U] ^ c;
    }
  }
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % rateInBytes1;
  uint8_t *b00 = ib;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % rateInBytes1] = 0x06U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws0[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws0[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws0[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws0[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws0[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws0[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws0[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws0[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws0[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws0[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws0[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws0[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws0[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws0[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws0[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws0[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws0[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws0[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws0[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws0[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws0[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws0[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws0[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws0[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws0[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws0[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws0[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws0[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws0[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws0[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws0[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws0[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws0[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[rateInBytes1 - 1U] = 0x80U;
  uint64_t ws1[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws1[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws1[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws1[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws1[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws1[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws1[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws1[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws1[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws1[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws1[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws1[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws1[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws1[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws1[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws1[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws1[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws1[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws1[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws1[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws1[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws1[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws1[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws1[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws1[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws1[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws1[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws1[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws1[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws1[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws1[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws1[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws1[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    s[i] = s[i] ^ ws1[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____2 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____2 << 1U | uu____2 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i1 + 5U * i] = s[i1 + 5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____3 = current;
      s[_Y] = uu____3 << r | uu____3 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
      uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
      uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
      uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
      uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
      s[0U + 5U * i] = v0;
      s[1U + 5U * i] = v1;
      s[2U + 5U * i] = v2;
      s[3U + 5U * i] = v3;
      s[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
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
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] = s[i + 0U] ^ (s[i + 5U] ^ (s[i + 10U] ^ (s[i + 15U] ^ s[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____4 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____4 << 1U | uu____4 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, s[i2 + 5U * i] = s[i2 + 5U * i] ^ _D;););
      uint64_t x = s[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = s[_Y];
        uint64_t uu____5 = current;
        s[_Y] = uu____5 << r | uu____5 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = s[0U + 5U * i] ^ (~s[1U + 5U * i] & s[2U + 5U * i]);
        uint64_t v1 = s[1U + 5U * i] ^ (~s[2U + 5U * i] & s[3U + 5U * i]);
        uint64_t v2 = s[2U + 5U * i] ^ (~s[3U + 5U * i] & s[4U + 5U * i]);
        uint64_t v3 = s[3U + 5U * i] ^ (~s[4U + 5U * i] & s[0U + 5U * i]);
        uint64_t v4 = s[4U + 5U * i] ^ (~s[0U + 5U * i] & s[1U + 5U * i]);
        s[0U + 5U * i] = v0;
        s[1U + 5U * i] = v1;
        s[2U + 5U * i] = v2;
        s[3U + 5U * i] = v3;
        s[4U + 5U * i] = v4;);
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

/**
Allocate state buffer of 200-bytes
*/
uint64_t *Hacl_Hash_SHA3_Scalar_state_malloc(void)
{
  uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC(25U, sizeof (uint64_t));
  return buf;
}

/**
Free state buffer
*/
void Hacl_Hash_SHA3_Scalar_state_free(uint64_t *s)
{
  KRML_HOST_FREE(s);
}

/**
Absorb number of input blocks and write the output state

  This function is intended to receive a hash state and input buffer.
  It prcoesses an input of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block are ignored.

  The argument `state` (IN/OUT) points to hash state, i.e., uint64_t[25]
  The argument `input` (IN) points to `inputByteLen` bytes of valid memory,
  i.e., uint8_t[inputByteLen]
*/
void
Hacl_Hash_SHA3_Scalar_shake128_absorb_nblocks(
  uint64_t *state,
  uint8_t *input,
  uint32_t inputByteLen
)
{
  for (uint32_t i0 = 0U; i0 < inputByteLen / 168U; i0++)
  {
    uint8_t b1[256U] = { 0U };
    uint8_t *b_ = b1;
    uint8_t *b0 = input;
    uint8_t *bl0 = b_;
    memcpy(bl0, b0 + i0 * 168U, 168U * sizeof (uint8_t));
    uint64_t ws[32U] = { 0U };
    uint8_t *b = b_;
    uint64_t u = load64_le(b);
    ws[0U] = u;
    uint64_t u0 = load64_le(b + 8U);
    ws[1U] = u0;
    uint64_t u1 = load64_le(b + 16U);
    ws[2U] = u1;
    uint64_t u2 = load64_le(b + 24U);
    ws[3U] = u2;
    uint64_t u3 = load64_le(b + 32U);
    ws[4U] = u3;
    uint64_t u4 = load64_le(b + 40U);
    ws[5U] = u4;
    uint64_t u5 = load64_le(b + 48U);
    ws[6U] = u5;
    uint64_t u6 = load64_le(b + 56U);
    ws[7U] = u6;
    uint64_t u7 = load64_le(b + 64U);
    ws[8U] = u7;
    uint64_t u8 = load64_le(b + 72U);
    ws[9U] = u8;
    uint64_t u9 = load64_le(b + 80U);
    ws[10U] = u9;
    uint64_t u10 = load64_le(b + 88U);
    ws[11U] = u10;
    uint64_t u11 = load64_le(b + 96U);
    ws[12U] = u11;
    uint64_t u12 = load64_le(b + 104U);
    ws[13U] = u12;
    uint64_t u13 = load64_le(b + 112U);
    ws[14U] = u13;
    uint64_t u14 = load64_le(b + 120U);
    ws[15U] = u14;
    uint64_t u15 = load64_le(b + 128U);
    ws[16U] = u15;
    uint64_t u16 = load64_le(b + 136U);
    ws[17U] = u16;
    uint64_t u17 = load64_le(b + 144U);
    ws[18U] = u17;
    uint64_t u18 = load64_le(b + 152U);
    ws[19U] = u18;
    uint64_t u19 = load64_le(b + 160U);
    ws[20U] = u19;
    uint64_t u20 = load64_le(b + 168U);
    ws[21U] = u20;
    uint64_t u21 = load64_le(b + 176U);
    ws[22U] = u21;
    uint64_t u22 = load64_le(b + 184U);
    ws[23U] = u22;
    uint64_t u23 = load64_le(b + 192U);
    ws[24U] = u23;
    uint64_t u24 = load64_le(b + 200U);
    ws[25U] = u24;
    uint64_t u25 = load64_le(b + 208U);
    ws[26U] = u25;
    uint64_t u26 = load64_le(b + 216U);
    ws[27U] = u26;
    uint64_t u27 = load64_le(b + 224U);
    ws[28U] = u27;
    uint64_t u28 = load64_le(b + 232U);
    ws[29U] = u28;
    uint64_t u29 = load64_le(b + 240U);
    ws[30U] = u29;
    uint64_t u30 = load64_le(b + 248U);
    ws[31U] = u30;
    for (uint32_t i = 0U; i < 25U; i++)
    {
      state[i] = state[i] ^ ws[i];
    }
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] =
          state[i
          + 0U]
          ^ (state[i + 5U] ^ (state[i + 10U] ^ (state[i + 15U] ^ state[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, state[i2 + 5U * i] = state[i2 + 5U * i] ^ _D;););
      uint64_t x = state[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = state[_Y];
        uint64_t uu____1 = current;
        state[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = state[0U + 5U * i] ^ (~state[1U + 5U * i] & state[2U + 5U * i]);
        uint64_t v1 = state[1U + 5U * i] ^ (~state[2U + 5U * i] & state[3U + 5U * i]);
        uint64_t v2 = state[2U + 5U * i] ^ (~state[3U + 5U * i] & state[4U + 5U * i]);
        uint64_t v3 = state[3U + 5U * i] ^ (~state[4U + 5U * i] & state[0U + 5U * i]);
        uint64_t v4 = state[4U + 5U * i] ^ (~state[0U + 5U * i] & state[1U + 5U * i]);
        state[0U + 5U * i] = v0;
        state[1U + 5U * i] = v1;
        state[2U + 5U * i] = v2;
        state[3U + 5U * i] = v3;
        state[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      state[0U] = state[0U] ^ c;
    }
  }
}

/**
Absorb a final partial block of input and write the output state

  This function is intended to receive a hash state and input buffer.
  It prcoesses a sequence of bytes at end of input buffer that is less 
  than 168-bytes (SHAKE128 block size),
  any bytes of full blocks at start of input buffer are ignored.

  The argument `state` (IN/OUT) points to hash state, i.e., uint64_t[25]
  The argument `input` (IN) points to `inputByteLen` bytes of valid memory,
  i.e., uint8_t[inputByteLen]
  
  Note: Full size of input buffer must be passed to `inputByteLen` including
  the number of full-block bytes at start of input buffer that are ignored
*/
void
Hacl_Hash_SHA3_Scalar_shake128_absorb_final(
  uint64_t *state,
  uint8_t *input,
  uint32_t inputByteLen
)
{
  uint8_t b2[256U] = { 0U };
  uint8_t *b_ = b2;
  uint32_t rem = inputByteLen % 168U;
  uint8_t *b00 = input;
  uint8_t *bl0 = b_;
  memcpy(bl0, b00 + inputByteLen - rem, rem * sizeof (uint8_t));
  uint8_t *b01 = b_;
  b01[inputByteLen % 168U] = 0x1FU;
  uint64_t ws[32U] = { 0U };
  uint8_t *b = b_;
  uint64_t u0 = load64_le(b);
  ws[0U] = u0;
  uint64_t u1 = load64_le(b + 8U);
  ws[1U] = u1;
  uint64_t u2 = load64_le(b + 16U);
  ws[2U] = u2;
  uint64_t u3 = load64_le(b + 24U);
  ws[3U] = u3;
  uint64_t u4 = load64_le(b + 32U);
  ws[4U] = u4;
  uint64_t u5 = load64_le(b + 40U);
  ws[5U] = u5;
  uint64_t u6 = load64_le(b + 48U);
  ws[6U] = u6;
  uint64_t u7 = load64_le(b + 56U);
  ws[7U] = u7;
  uint64_t u8 = load64_le(b + 64U);
  ws[8U] = u8;
  uint64_t u9 = load64_le(b + 72U);
  ws[9U] = u9;
  uint64_t u10 = load64_le(b + 80U);
  ws[10U] = u10;
  uint64_t u11 = load64_le(b + 88U);
  ws[11U] = u11;
  uint64_t u12 = load64_le(b + 96U);
  ws[12U] = u12;
  uint64_t u13 = load64_le(b + 104U);
  ws[13U] = u13;
  uint64_t u14 = load64_le(b + 112U);
  ws[14U] = u14;
  uint64_t u15 = load64_le(b + 120U);
  ws[15U] = u15;
  uint64_t u16 = load64_le(b + 128U);
  ws[16U] = u16;
  uint64_t u17 = load64_le(b + 136U);
  ws[17U] = u17;
  uint64_t u18 = load64_le(b + 144U);
  ws[18U] = u18;
  uint64_t u19 = load64_le(b + 152U);
  ws[19U] = u19;
  uint64_t u20 = load64_le(b + 160U);
  ws[20U] = u20;
  uint64_t u21 = load64_le(b + 168U);
  ws[21U] = u21;
  uint64_t u22 = load64_le(b + 176U);
  ws[22U] = u22;
  uint64_t u23 = load64_le(b + 184U);
  ws[23U] = u23;
  uint64_t u24 = load64_le(b + 192U);
  ws[24U] = u24;
  uint64_t u25 = load64_le(b + 200U);
  ws[25U] = u25;
  uint64_t u26 = load64_le(b + 208U);
  ws[26U] = u26;
  uint64_t u27 = load64_le(b + 216U);
  ws[27U] = u27;
  uint64_t u28 = load64_le(b + 224U);
  ws[28U] = u28;
  uint64_t u29 = load64_le(b + 232U);
  ws[29U] = u29;
  uint64_t u30 = load64_le(b + 240U);
  ws[30U] = u30;
  uint64_t u31 = load64_le(b + 248U);
  ws[31U] = u31;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    state[i] = state[i] ^ ws[i];
  }
  uint8_t b3[256U] = { 0U };
  uint8_t *b4 = b3;
  uint8_t *b0 = b4;
  b0[167U] = 0x80U;
  uint64_t ws0[32U] = { 0U };
  uint8_t *b1 = b4;
  uint64_t u = load64_le(b1);
  ws0[0U] = u;
  uint64_t u32 = load64_le(b1 + 8U);
  ws0[1U] = u32;
  uint64_t u33 = load64_le(b1 + 16U);
  ws0[2U] = u33;
  uint64_t u34 = load64_le(b1 + 24U);
  ws0[3U] = u34;
  uint64_t u35 = load64_le(b1 + 32U);
  ws0[4U] = u35;
  uint64_t u36 = load64_le(b1 + 40U);
  ws0[5U] = u36;
  uint64_t u37 = load64_le(b1 + 48U);
  ws0[6U] = u37;
  uint64_t u38 = load64_le(b1 + 56U);
  ws0[7U] = u38;
  uint64_t u39 = load64_le(b1 + 64U);
  ws0[8U] = u39;
  uint64_t u40 = load64_le(b1 + 72U);
  ws0[9U] = u40;
  uint64_t u41 = load64_le(b1 + 80U);
  ws0[10U] = u41;
  uint64_t u42 = load64_le(b1 + 88U);
  ws0[11U] = u42;
  uint64_t u43 = load64_le(b1 + 96U);
  ws0[12U] = u43;
  uint64_t u44 = load64_le(b1 + 104U);
  ws0[13U] = u44;
  uint64_t u45 = load64_le(b1 + 112U);
  ws0[14U] = u45;
  uint64_t u46 = load64_le(b1 + 120U);
  ws0[15U] = u46;
  uint64_t u47 = load64_le(b1 + 128U);
  ws0[16U] = u47;
  uint64_t u48 = load64_le(b1 + 136U);
  ws0[17U] = u48;
  uint64_t u49 = load64_le(b1 + 144U);
  ws0[18U] = u49;
  uint64_t u50 = load64_le(b1 + 152U);
  ws0[19U] = u50;
  uint64_t u51 = load64_le(b1 + 160U);
  ws0[20U] = u51;
  uint64_t u52 = load64_le(b1 + 168U);
  ws0[21U] = u52;
  uint64_t u53 = load64_le(b1 + 176U);
  ws0[22U] = u53;
  uint64_t u54 = load64_le(b1 + 184U);
  ws0[23U] = u54;
  uint64_t u55 = load64_le(b1 + 192U);
  ws0[24U] = u55;
  uint64_t u56 = load64_le(b1 + 200U);
  ws0[25U] = u56;
  uint64_t u57 = load64_le(b1 + 208U);
  ws0[26U] = u57;
  uint64_t u58 = load64_le(b1 + 216U);
  ws0[27U] = u58;
  uint64_t u59 = load64_le(b1 + 224U);
  ws0[28U] = u59;
  uint64_t u60 = load64_le(b1 + 232U);
  ws0[29U] = u60;
  uint64_t u61 = load64_le(b1 + 240U);
  ws0[30U] = u61;
  uint64_t u62 = load64_le(b1 + 248U);
  ws0[31U] = u62;
  for (uint32_t i = 0U; i < 25U; i++)
  {
    state[i] = state[i] ^ ws0[i];
  }
  for (uint32_t i0 = 0U; i0 < 24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      _C[i] = state[i + 0U] ^ (state[i + 5U] ^ (state[i + 10U] ^ (state[i + 15U] ^ state[i + 20U]))););
    KRML_MAYBE_FOR5(i1,
      0U,
      5U,
      1U,
      uint64_t uu____0 = _C[(i1 + 1U) % 5U];
      uint64_t _D = _C[(i1 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
      KRML_MAYBE_FOR5(i, 0U, 5U, 1U, state[i1 + 5U * i] = state[i1 + 5U * i] ^ _D;););
    uint64_t x = state[1U];
    uint64_t current = x;
    for (uint32_t i = 0U; i < 24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
      uint64_t temp = state[_Y];
      uint64_t uu____1 = current;
      state[_Y] = uu____1 << r | uu____1 >> (64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      0U,
      5U,
      1U,
      uint64_t v0 = state[0U + 5U * i] ^ (~state[1U + 5U * i] & state[2U + 5U * i]);
      uint64_t v1 = state[1U + 5U * i] ^ (~state[2U + 5U * i] & state[3U + 5U * i]);
      uint64_t v2 = state[2U + 5U * i] ^ (~state[3U + 5U * i] & state[4U + 5U * i]);
      uint64_t v3 = state[3U + 5U * i] ^ (~state[4U + 5U * i] & state[0U + 5U * i]);
      uint64_t v4 = state[4U + 5U * i] ^ (~state[0U + 5U * i] & state[1U + 5U * i]);
      state[0U + 5U * i] = v0;
      state[1U + 5U * i] = v1;
      state[2U + 5U * i] = v2;
      state[3U + 5U * i] = v3;
      state[4U + 5U * i] = v4;);
    uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i0];
    state[0U] = state[0U] ^ c;
  }
}

/**
Squeeze a hash state to output buffer

  This function is intended to receive a hash state and output buffer.
  It produces an output of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block are ignored.

  The argument `state` (IN) points to hash state, i.e., uint64_t[25]
  The argument `output` (OUT) points to `outputByteLen` bytes of valid memory,
  i.e., uint8_t[outputByteLen]
*/
void
Hacl_Hash_SHA3_Scalar_shake128_squeeze_nblocks(
  uint64_t *state,
  uint8_t *output,
  uint32_t outputByteLen
)
{
  for (uint32_t i0 = 0U; i0 < outputByteLen / 168U; i0++)
  {
    uint8_t hbuf[256U] = { 0U };
    uint64_t ws[32U] = { 0U };
    memcpy(ws, state, 25U * sizeof (uint64_t));
    for (uint32_t i = 0U; i < 32U; i++)
    {
      store64_le(hbuf + i * 8U, ws[i]);
    }
    uint8_t *b0 = output;
    memcpy(b0 + i0 * 168U, hbuf, 168U * sizeof (uint8_t));
    for (uint32_t i1 = 0U; i1 < 24U; i1++)
    {
      uint64_t _C[5U] = { 0U };
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        _C[i] =
          state[i
          + 0U]
          ^ (state[i + 5U] ^ (state[i + 10U] ^ (state[i + 15U] ^ state[i + 20U]))););
      KRML_MAYBE_FOR5(i2,
        0U,
        5U,
        1U,
        uint64_t uu____0 = _C[(i2 + 1U) % 5U];
        uint64_t _D = _C[(i2 + 4U) % 5U] ^ (uu____0 << 1U | uu____0 >> 63U);
        KRML_MAYBE_FOR5(i, 0U, 5U, 1U, state[i2 + 5U * i] = state[i2 + 5U * i] ^ _D;););
      uint64_t x = state[1U];
      uint64_t current = x;
      for (uint32_t i = 0U; i < 24U; i++)
      {
        uint32_t _Y = Hacl_Impl_SHA3_Vec_keccak_piln[i];
        uint32_t r = Hacl_Impl_SHA3_Vec_keccak_rotc[i];
        uint64_t temp = state[_Y];
        uint64_t uu____1 = current;
        state[_Y] = uu____1 << r | uu____1 >> (64U - r);
        current = temp;
      }
      KRML_MAYBE_FOR5(i,
        0U,
        5U,
        1U,
        uint64_t v0 = state[0U + 5U * i] ^ (~state[1U + 5U * i] & state[2U + 5U * i]);
        uint64_t v1 = state[1U + 5U * i] ^ (~state[2U + 5U * i] & state[3U + 5U * i]);
        uint64_t v2 = state[2U + 5U * i] ^ (~state[3U + 5U * i] & state[4U + 5U * i]);
        uint64_t v3 = state[3U + 5U * i] ^ (~state[4U + 5U * i] & state[0U + 5U * i]);
        uint64_t v4 = state[4U + 5U * i] ^ (~state[0U + 5U * i] & state[1U + 5U * i]);
        state[0U + 5U * i] = v0;
        state[1U + 5U * i] = v1;
        state[2U + 5U * i] = v2;
        state[3U + 5U * i] = v3;
        state[4U + 5U * i] = v4;);
      uint64_t c = Hacl_Impl_SHA3_Vec_keccak_rndc[i1];
      state[0U] = state[0U] ^ c;
    }
  }
}

