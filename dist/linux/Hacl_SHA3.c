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


#include "Hacl_SHA3.h"

const
u32
Hacl_Impl_SHA3_keccak_rotc[24U] =
  {
    (u32)1U, (u32)3U, (u32)6U, (u32)10U, (u32)15U, (u32)21U, (u32)28U, (u32)36U, (u32)45U, (u32)55U,
    (u32)2U, (u32)14U, (u32)27U, (u32)41U, (u32)56U, (u32)8U, (u32)25U, (u32)43U, (u32)62U,
    (u32)18U, (u32)39U, (u32)61U, (u32)20U, (u32)44U
  };

const
u32
Hacl_Impl_SHA3_keccak_piln[24U] =
  {
    (u32)10U, (u32)7U, (u32)11U, (u32)17U, (u32)18U, (u32)3U, (u32)5U, (u32)16U, (u32)8U, (u32)21U,
    (u32)24U, (u32)4U, (u32)15U, (u32)23U, (u32)19U, (u32)13U, (u32)12U, (u32)2U, (u32)20U,
    (u32)14U, (u32)22U, (u32)9U, (u32)6U, (u32)1U
  };

const
u64
Hacl_Impl_SHA3_keccak_rndc[24U] =
  {
    (u64)0x0000000000000001U, (u64)0x0000000000008082U, (u64)0x800000000000808aU,
    (u64)0x8000000080008000U, (u64)0x000000000000808bU, (u64)0x0000000080000001U,
    (u64)0x8000000080008081U, (u64)0x8000000000008009U, (u64)0x000000000000008aU,
    (u64)0x0000000000000088U, (u64)0x0000000080008009U, (u64)0x000000008000000aU,
    (u64)0x000000008000808bU, (u64)0x800000000000008bU, (u64)0x8000000000008089U,
    (u64)0x8000000000008003U, (u64)0x8000000000008002U, (u64)0x8000000000000080U,
    (u64)0x000000000000800aU, (u64)0x800000008000000aU, (u64)0x8000000080008081U,
    (u64)0x8000000000008080U, (u64)0x0000000080000001U, (u64)0x8000000080008008U
  };

inline u64 Hacl_Impl_SHA3_rotl(u64 a, u32 b)
{
  return a << b | a >> ((u32)64U - b);
}

void Hacl_Impl_SHA3_state_permute(u64 *s)
{
  u32 i0;
  for (i0 = (u32)0U; i0 < (u32)24U; i0++)
  {
    u64 b[5U] = { 0U };
    u64 x;
    {
      u32 i;
      for (i = (u32)0U; i < (u32)5U; i++)
        b[i] =
          s[i
          + (u32)0U]
          ^ (s[i + (u32)5U] ^ (s[i + (u32)10U] ^ (s[i + (u32)15U] ^ s[i + (u32)20U])));
    }
    {
      u32 i1;
      for (i1 = (u32)0U; i1 < (u32)5U; i1++)
      {
        u64 uu____0 = b[(i1 + (u32)4U) % (u32)5U];
        u64 _D = uu____0 ^ Hacl_Impl_SHA3_rotl(b[(i1 + (u32)1U) % (u32)5U], (u32)1U);
        {
          u32 i;
          for (i = (u32)0U; i < (u32)5U; i++)
            s[i1 + (u32)5U * i] = s[i1 + (u32)5U * i] ^ _D;
        }
      }
    }
    Lib_Memzero0_memzero(b, (u32)5U * sizeof (b[0U]));
    x = s[1U];
    {
      u64 b0 = x;
      {
        u32 i;
        for (i = (u32)0U; i < (u32)24U; i++)
        {
          u32 _Y = Hacl_Impl_SHA3_keccak_piln[i];
          u32 r = Hacl_Impl_SHA3_keccak_rotc[i];
          u64 temp = s[_Y];
          s[_Y] = Hacl_Impl_SHA3_rotl(b0, r);
          b0 = temp;
        }
      }
      Lib_Memzero0_memzero(&b0, (u32)1U * sizeof ((&b0)[0U]));
      {
        u64 b1[25U] = { 0U };
        u64 c;
        memcpy(b1, s, (u32)25U * sizeof (u64));
        {
          u32 i1;
          for (i1 = (u32)0U; i1 < (u32)5U; i1++)
          {
            u32 i;
            for (i = (u32)0U; i < (u32)5U; i++)
              s[i + (u32)5U * i1] =
                b1[i
                + (u32)5U * i1]
                ^
                  (~b1[(i + (u32)1U)
                  % (u32)5U
                  + (u32)5U * i1]
                  & b1[(i + (u32)2U) % (u32)5U + (u32)5U * i1]);
          }
        }
        Lib_Memzero0_memzero(b1, (u32)25U * sizeof (b1[0U]));
        c = Hacl_Impl_SHA3_keccak_rndc[i0];
        s[0U] = s[0U] ^ c;
      }
    }
  }
}

void Hacl_Impl_SHA3_loadState(u32 rateInBytes, u8 *input, u64 *s)
{
  u8 b[200U] = { 0U };
  memcpy(b, input, rateInBytes * sizeof (u8));
  {
    u32 i;
    for (i = (u32)0U; i < (u32)25U; i++)
    {
      u64 u = load64_le(b + i * (u32)8U);
      u64 x = u;
      s[i] = s[i] ^ x;
    }
  }
  Lib_Memzero0_memzero(b, (u32)200U * sizeof (b[0U]));
}

void Hacl_Impl_SHA3_storeState(u32 rateInBytes, u64 *s, u8 *res)
{
  u8 b[200U] = { 0U };
  {
    u32 i;
    for (i = (u32)0U; i < (u32)25U; i++)
    {
      u64 sj = s[i];
      store64_le(b + i * (u32)8U, sj);
    }
  }
  memcpy(res, b, rateInBytes * sizeof (u8));
  Lib_Memzero0_memzero(b, (u32)200U * sizeof (b[0U]));
}

void
Hacl_Impl_SHA3_absorb(u64 *s, u32 rateInBytes, u32 inputByteLen, u8 *input, u8 delimitedSuffix)
{
  u32 nb = inputByteLen / rateInBytes;
  u32 rem = inputByteLen % rateInBytes;
  u8 *last;
  {
    u32 i;
    for (i = (u32)0U; i < nb; i++)
    {
      u8 *block = input + i * rateInBytes;
      Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
      Hacl_Impl_SHA3_state_permute(s);
    }
  }
  last = input + nb * rateInBytes;
  KRML_CHECK_SIZE(sizeof (u8), rateInBytes);
  {
    u8 b[rateInBytes];
    memset(b, 0U, rateInBytes * sizeof (u8));
    memcpy(b, last, rem * sizeof (u8));
    b[rem] = delimitedSuffix;
    Hacl_Impl_SHA3_loadState(rateInBytes, b, s);
    if (!((delimitedSuffix & (u8)0x80U) == (u8)0U) && rem == rateInBytes - (u32)1U)
      Hacl_Impl_SHA3_state_permute(s);
    KRML_CHECK_SIZE(sizeof (u8), rateInBytes);
    {
      u8 b1[rateInBytes];
      memset(b1, 0U, rateInBytes * sizeof (u8));
      b1[rateInBytes - (u32)1U] = (u8)0x80U;
      Hacl_Impl_SHA3_loadState(rateInBytes, b1, s);
      Hacl_Impl_SHA3_state_permute(s);
      Lib_Memzero0_memzero(b1, rateInBytes * sizeof (b1[0U]));
      Lib_Memzero0_memzero(b, rateInBytes * sizeof (b[0U]));
    }
  }
}

void Hacl_Impl_SHA3_squeeze(u64 *s, u32 rateInBytes, u32 outputByteLen, u8 *output)
{
  u32 outBlocks = outputByteLen / rateInBytes;
  u32 remOut = outputByteLen % rateInBytes;
  u8 *last = output + outputByteLen - remOut;
  u8 *blocks = output;
  {
    u32 i;
    for (i = (u32)0U; i < outBlocks; i++)
    {
      Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
      Hacl_Impl_SHA3_state_permute(s);
    }
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

void
Hacl_Impl_SHA3_keccak(
  u32 rate,
  u32 capacity,
  u32 inputByteLen,
  u8 *input,
  u8 delimitedSuffix,
  u32 outputByteLen,
  u8 *output
)
{
  u32 rateInBytes = rate / (u32)8U;
  u64 s[25U] = { 0U };
  Hacl_Impl_SHA3_absorb(s, rateInBytes, inputByteLen, input, delimitedSuffix);
  Hacl_Impl_SHA3_squeeze(s, rateInBytes, outputByteLen, output);
}

void Hacl_SHA3_shake128_hacl(u32 inputByteLen, u8 *input, u32 outputByteLen, u8 *output)
{
  Hacl_Impl_SHA3_keccak((u32)1344U,
    (u32)256U,
    inputByteLen,
    input,
    (u8)0x1FU,
    outputByteLen,
    output);
}

void Hacl_SHA3_shake256_hacl(u32 inputByteLen, u8 *input, u32 outputByteLen, u8 *output)
{
  Hacl_Impl_SHA3_keccak((u32)1088U,
    (u32)512U,
    inputByteLen,
    input,
    (u8)0x1FU,
    outputByteLen,
    output);
}

void Hacl_SHA3_sha3_224(u32 inputByteLen, u8 *input, u8 *output)
{
  Hacl_Impl_SHA3_keccak((u32)1152U, (u32)448U, inputByteLen, input, (u8)0x06U, (u32)28U, output);
}

void Hacl_SHA3_sha3_256(u32 inputByteLen, u8 *input, u8 *output)
{
  Hacl_Impl_SHA3_keccak((u32)1088U, (u32)512U, inputByteLen, input, (u8)0x06U, (u32)32U, output);
}

void Hacl_SHA3_sha3_384(u32 inputByteLen, u8 *input, u8 *output)
{
  Hacl_Impl_SHA3_keccak((u32)832U, (u32)768U, inputByteLen, input, (u8)0x06U, (u32)48U, output);
}

void Hacl_SHA3_sha3_512(u32 inputByteLen, u8 *input, u8 *output)
{
  Hacl_Impl_SHA3_keccak((u32)576U, (u32)1024U, inputByteLen, input, (u8)0x06U, (u32)64U, output);
}

