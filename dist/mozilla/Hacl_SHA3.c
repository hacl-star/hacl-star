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

#include "internal/Hacl_Lib.h"

const
uint32_t
Hacl_Impl_SHA3_keccak_rotc[24U] =
  {
    (uint32_t)1U, (uint32_t)3U, (uint32_t)6U, (uint32_t)10U, (uint32_t)15U, (uint32_t)21U,
    (uint32_t)28U, (uint32_t)36U, (uint32_t)45U, (uint32_t)55U, (uint32_t)2U, (uint32_t)14U,
    (uint32_t)27U, (uint32_t)41U, (uint32_t)56U, (uint32_t)8U, (uint32_t)25U, (uint32_t)43U,
    (uint32_t)62U, (uint32_t)18U, (uint32_t)39U, (uint32_t)61U, (uint32_t)20U, (uint32_t)44U
  };

const
uint32_t
Hacl_Impl_SHA3_keccak_piln[24U] =
  {
    (uint32_t)10U, (uint32_t)7U, (uint32_t)11U, (uint32_t)17U, (uint32_t)18U, (uint32_t)3U,
    (uint32_t)5U, (uint32_t)16U, (uint32_t)8U, (uint32_t)21U, (uint32_t)24U, (uint32_t)4U,
    (uint32_t)15U, (uint32_t)23U, (uint32_t)19U, (uint32_t)13U, (uint32_t)12U, (uint32_t)2U,
    (uint32_t)20U, (uint32_t)14U, (uint32_t)22U, (uint32_t)9U, (uint32_t)6U, (uint32_t)1U
  };

const
uint64_t
Hacl_Impl_SHA3_keccak_rndc[24U] =
  {
    (uint64_t)0x0000000000000001U, (uint64_t)0x0000000000008082U, (uint64_t)0x800000000000808aU,
    (uint64_t)0x8000000080008000U, (uint64_t)0x000000000000808bU, (uint64_t)0x0000000080000001U,
    (uint64_t)0x8000000080008081U, (uint64_t)0x8000000000008009U, (uint64_t)0x000000000000008aU,
    (uint64_t)0x0000000000000088U, (uint64_t)0x0000000080008009U, (uint64_t)0x000000008000000aU,
    (uint64_t)0x000000008000808bU, (uint64_t)0x800000000000008bU, (uint64_t)0x8000000000008089U,
    (uint64_t)0x8000000000008003U, (uint64_t)0x8000000000008002U, (uint64_t)0x8000000000000080U,
    (uint64_t)0x000000000000800aU, (uint64_t)0x800000008000000aU, (uint64_t)0x8000000080008081U,
    (uint64_t)0x8000000000008080U, (uint64_t)0x0000000080000001U, (uint64_t)0x8000000080008008U
  };

inline uint64_t Hacl_Impl_SHA3_rotl(uint64_t a, uint32_t b)
{
  return a << b | a >> ((uint32_t)64U - b);
}

void Hacl_Impl_SHA3_state_permute(uint64_t *s)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)24U; i0++)
  {
    uint64_t b[5U] = { 0U };
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
    {
      b[i] =
        s[i
        + (uint32_t)0U]
        ^
          (s[i
          + (uint32_t)5U]
          ^ (s[i + (uint32_t)10U] ^ (s[i + (uint32_t)15U] ^ s[i + (uint32_t)20U])));
    }
    for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)5U; i1++)
    {
      uint64_t uu____0 = b[(i1 + (uint32_t)4U) % (uint32_t)5U];
      uint64_t
      _D = uu____0 ^ Hacl_Impl_SHA3_rotl(b[(i1 + (uint32_t)1U) % (uint32_t)5U], (uint32_t)1U);
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
      {
        s[i1 + (uint32_t)5U * i] = s[i1 + (uint32_t)5U * i] ^ _D;
      }
    }
    Lib_Memzero0_memzero(b, (uint32_t)5U * sizeof (b[0U]));
    uint64_t x = s[1U];
    uint64_t b0 = x;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)24U; i++)
    {
      uint32_t _Y = Hacl_Impl_SHA3_keccak_piln[i];
      uint32_t r = Hacl_Impl_SHA3_keccak_rotc[i];
      uint64_t temp = s[_Y];
      s[_Y] = Hacl_Impl_SHA3_rotl(b0, r);
      b0 = temp;
    }
    Lib_Memzero0_memzero(&b0, (uint32_t)1U * sizeof ((&b0)[0U]));
    uint64_t b1[25U] = { 0U };
    memcpy(b1, s, (uint32_t)25U * sizeof (uint64_t));
    for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)5U; i1++)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
      {
        s[i + (uint32_t)5U * i1] =
          b1[i
          + (uint32_t)5U * i1]
          ^
            (~b1[(i + (uint32_t)1U)
            % (uint32_t)5U
            + (uint32_t)5U * i1]
            & b1[(i + (uint32_t)2U) % (uint32_t)5U + (uint32_t)5U * i1]);
      }
    }
    Lib_Memzero0_memzero(b1, (uint32_t)25U * sizeof (b1[0U]));
    uint64_t c = Hacl_Impl_SHA3_keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
}

void Hacl_Impl_SHA3_loadState(uint32_t rateInBytes, uint8_t *input, uint64_t *s)
{
  uint8_t b[200U] = { 0U };
  memcpy(b, input, rateInBytes * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)25U; i++)
  {
    uint64_t u = load64_le(b + i * (uint32_t)8U);
    uint64_t x = u;
    s[i] = s[i] ^ x;
  }
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
}

void Hacl_Impl_SHA3_storeState(uint32_t rateInBytes, uint64_t *s, uint8_t *res)
{
  uint8_t b[200U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)25U; i++)
  {
    uint64_t sj = s[i];
    store64_le(b + i * (uint32_t)8U, sj);
  }
  memcpy(res, b, rateInBytes * sizeof (uint8_t));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
}

bool
Hacl_Impl_SHA3_absorb_last(
  uint8_t delimitedSuffix,
  uint32_t rateInBytes,
  uint32_t rem,
  uint8_t *input,
  uint64_t *s
)
{
  bool a_is_zero = rateInBytes == (uint32_t)0U;
  bool a_gt_b = rateInBytes > (uint32_t)200U;
  if (a_is_zero || a_gt_b || rem >= rateInBytes)
  {
    return false;
  }
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, input, rem * sizeof (uint8_t));
  lastBlock[rem] = delimitedSuffix;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((delimitedSuffix & (uint8_t)0x80U) == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  return true;
}

bool Hacl_Impl_SHA3_absorb_inner(uint32_t rateInBytes, uint8_t *block, uint64_t *s)
{
  bool a_is_zero = rateInBytes == (uint32_t)0U;
  bool a_gt_b = rateInBytes > (uint32_t)200U;
  if (a_is_zero || a_gt_b)
  {
    return false;
  }
  Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
  Hacl_Impl_SHA3_state_permute(s);
  return true;
}

bool
Hacl_Impl_SHA3_absorb(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix
)
{
  bool a_is_zero = rateInBytes == (uint32_t)0U;
  bool a_gt_b = rateInBytes > (uint32_t)200U;
  if (a_is_zero || a_gt_b)
  {
    return false;
  }
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last, rem * sizeof (uint8_t));
  lastBlock[rem] = delimitedSuffix;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((delimitedSuffix & (uint8_t)0x80U) == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  return true;
}

bool
Hacl_Impl_SHA3_squeeze(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  bool a_is_zero = rateInBytes == (uint32_t)0U;
  bool a_gt_b = rateInBytes > (uint32_t)200U;
  if (a_is_zero || a_gt_b)
  {
    return false;
  }
  uint32_t outBlocks = outputByteLen / rateInBytes;
  uint32_t remOut = outputByteLen % rateInBytes;
  uint8_t *last = output + outputByteLen - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
  return true;
}

bool
Hacl_Impl_SHA3_keccak(
  uint32_t rate,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  uint32_t bit3mask = (uint32_t)7U;
  bool rate_mod_8 = (rate & bit3mask) == (uint32_t)0U;
  uint32_t rateInBytes = rate / (uint32_t)8U;
  bool rate_is_zero = rateInBytes == (uint32_t)0U;
  bool rate_lte_200 = rateInBytes > (uint32_t)200U;
  if (!rate_mod_8 || rate_is_zero || rate_lte_200)
  {
    return false;
  }
  uint32_t rateInBytes1 = rate / (uint32_t)8U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes1;
  uint32_t rem = inputByteLen % rateInBytes1;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes1;
    Hacl_Impl_SHA3_loadState(rateInBytes1, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes1;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = delimitedSuffix;
  Hacl_Impl_SHA3_loadState(rateInBytes1, lastBlock, s);
  if (!((delimitedSuffix & (uint8_t)0x80U) == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = outputByteLen / rateInBytes1;
  uint32_t remOut = outputByteLen % rateInBytes1;
  uint8_t *last = output + outputByteLen - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes1, s, blocks + i * rateInBytes1);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
  return true;
}

void
Hacl_SHA3_shake128_hacl(
  uint32_t inputByteLen,
  uint8_t *input,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  uint32_t rateInBytes = (uint32_t)168U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = (uint8_t)0x1FU;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = outputByteLen / rateInBytes;
  uint32_t remOut = outputByteLen % rateInBytes;
  uint8_t *last = output + outputByteLen - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

void
Hacl_SHA3_shake256_hacl(
  uint32_t inputByteLen,
  uint8_t *input,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  uint32_t rateInBytes = (uint32_t)136U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = (uint8_t)0x1FU;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = outputByteLen / rateInBytes;
  uint32_t remOut = outputByteLen % rateInBytes;
  uint8_t *last = output + outputByteLen - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

void Hacl_SHA3_sha3_224(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  uint32_t rateInBytes = (uint32_t)144U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = (uint32_t)28U / rateInBytes;
  uint32_t remOut = (uint32_t)28U % rateInBytes;
  uint8_t *last = output + (uint32_t)28U - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

void Hacl_SHA3_sha3_256(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  uint32_t rateInBytes = (uint32_t)136U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = (uint32_t)32U / rateInBytes;
  uint32_t remOut = (uint32_t)32U % rateInBytes;
  uint8_t *last = output + (uint32_t)32U - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

void Hacl_SHA3_sha3_384(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  uint32_t rateInBytes = (uint32_t)104U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = (uint32_t)48U / rateInBytes;
  uint32_t remOut = (uint32_t)48U % rateInBytes;
  uint8_t *last = output + (uint32_t)48U - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

void Hacl_SHA3_sha3_512(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  uint32_t rateInBytes = (uint32_t)72U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = (uint32_t)64U / rateInBytes;
  uint32_t remOut = (uint32_t)64U % rateInBytes;
  uint8_t *last = output + (uint32_t)64U - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

/*
Keccak instantiation with the rate equal to 1088 bits 
*/
void
Hacl_SHA3_keccak_1088(
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  uint32_t rateInBytes = (uint32_t)136U;
  uint64_t s[25U] = { 0U };
  uint32_t nb = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < nb; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last0 = input + nb * rateInBytes;
  uint8_t b[200U] = { 0U };
  uint8_t *lastBlock = b;
  memcpy(lastBlock, last0, rem * sizeof (uint8_t));
  lastBlock[rem] = delimitedSuffix;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((delimitedSuffix & (uint8_t)0x80U) == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t b1[200U] = { 0U };
  uint8_t *nextBlock = b1;
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, (uint32_t)200U * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, (uint32_t)200U * sizeof (b[0U]));
  uint32_t outBlocks = outputByteLen / rateInBytes;
  uint32_t remOut = outputByteLen % rateInBytes;
  uint8_t *last = output + outputByteLen - remOut;
  uint8_t *blocks = output;
  for (uint32_t i = (uint32_t)0U; i < outBlocks; i++)
  {
    Hacl_Impl_SHA3_storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  Hacl_Impl_SHA3_storeState(remOut, s, last);
}

