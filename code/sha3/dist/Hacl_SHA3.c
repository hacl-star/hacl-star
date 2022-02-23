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
  uint32_t rateInBytes1 = (uint32_t)144U;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b[rateInBytes1];
  memset(b, 0U, rateInBytes1 * sizeof (uint8_t));
  memcpy(b, last0, rem * sizeof (uint8_t));
  b[rem] = (uint8_t)0x1FU;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b1[rateInBytes1];
  memset(b1, 0U, rateInBytes1 * sizeof (uint8_t));
  b1[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b1, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, rateInBytes1 * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, rateInBytes1 * sizeof (b[0U]));
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
  uint32_t rateInBytes1 = (uint32_t)144U;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b[rateInBytes1];
  memset(b, 0U, rateInBytes1 * sizeof (uint8_t));
  memcpy(b, last0, rem * sizeof (uint8_t));
  b[rem] = (uint8_t)0x1FU;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b1[rateInBytes1];
  memset(b1, 0U, rateInBytes1 * sizeof (uint8_t));
  b1[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b1, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, rateInBytes1 * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, rateInBytes1 * sizeof (b[0U]));
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
  uint32_t rateInBytes1 = (uint32_t)144U;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b[rateInBytes1];
  memset(b, 0U, rateInBytes1 * sizeof (uint8_t));
  memcpy(b, last0, rem * sizeof (uint8_t));
  b[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b1[rateInBytes1];
  memset(b1, 0U, rateInBytes1 * sizeof (uint8_t));
  b1[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b1, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, rateInBytes1 * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, rateInBytes1 * sizeof (b[0U]));
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
  uint32_t rateInBytes1 = (uint32_t)144U;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b[rateInBytes1];
  memset(b, 0U, rateInBytes1 * sizeof (uint8_t));
  memcpy(b, last0, rem * sizeof (uint8_t));
  b[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b1[rateInBytes1];
  memset(b1, 0U, rateInBytes1 * sizeof (uint8_t));
  b1[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b1, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, rateInBytes1 * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, rateInBytes1 * sizeof (b[0U]));
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
  uint32_t rateInBytes1 = (uint32_t)144U;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b[rateInBytes1];
  memset(b, 0U, rateInBytes1 * sizeof (uint8_t));
  memcpy(b, last0, rem * sizeof (uint8_t));
  b[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b1[rateInBytes1];
  memset(b1, 0U, rateInBytes1 * sizeof (uint8_t));
  b1[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b1, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, rateInBytes1 * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, rateInBytes1 * sizeof (b[0U]));
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
  uint32_t rateInBytes1 = (uint32_t)144U;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b[rateInBytes1];
  memset(b, 0U, rateInBytes1 * sizeof (uint8_t));
  memcpy(b, last0, rem * sizeof (uint8_t));
  b[rem] = (uint8_t)0x06U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b, s);
  if (!((uint8_t)0U == (uint8_t)0U) && rem == rateInBytes1 - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes1);
  uint8_t b1[rateInBytes1];
  memset(b1, 0U, rateInBytes1 * sizeof (uint8_t));
  b1[rateInBytes1 - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes1, b1, s);
  Hacl_Impl_SHA3_state_permute(s);
  Lib_Memzero0_memzero(b1, rateInBytes1 * sizeof (b1[0U]));
  Lib_Memzero0_memzero(b, rateInBytes1 * sizeof (b[0U]));
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

