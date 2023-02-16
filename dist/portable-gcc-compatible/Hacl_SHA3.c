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


#include "Hacl_SHA3.h"

#include "internal/Hacl_Krmllib.h"

/* SNIPPET_START: keccak_rotc */

static const
uint32_t
keccak_rotc[24U] =
  {
    (uint32_t)1U, (uint32_t)3U, (uint32_t)6U, (uint32_t)10U, (uint32_t)15U, (uint32_t)21U,
    (uint32_t)28U, (uint32_t)36U, (uint32_t)45U, (uint32_t)55U, (uint32_t)2U, (uint32_t)14U,
    (uint32_t)27U, (uint32_t)41U, (uint32_t)56U, (uint32_t)8U, (uint32_t)25U, (uint32_t)43U,
    (uint32_t)62U, (uint32_t)18U, (uint32_t)39U, (uint32_t)61U, (uint32_t)20U, (uint32_t)44U
  };

/* SNIPPET_END: keccak_rotc */

/* SNIPPET_START: keccak_piln */

static const
uint32_t
keccak_piln[24U] =
  {
    (uint32_t)10U, (uint32_t)7U, (uint32_t)11U, (uint32_t)17U, (uint32_t)18U, (uint32_t)3U,
    (uint32_t)5U, (uint32_t)16U, (uint32_t)8U, (uint32_t)21U, (uint32_t)24U, (uint32_t)4U,
    (uint32_t)15U, (uint32_t)23U, (uint32_t)19U, (uint32_t)13U, (uint32_t)12U, (uint32_t)2U,
    (uint32_t)20U, (uint32_t)14U, (uint32_t)22U, (uint32_t)9U, (uint32_t)6U, (uint32_t)1U
  };

/* SNIPPET_END: keccak_piln */

/* SNIPPET_START: keccak_rndc */

static const
uint64_t
keccak_rndc[24U] =
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

/* SNIPPET_END: keccak_rndc */

/* SNIPPET_START: Hacl_Impl_SHA3_state_permute */

void Hacl_Impl_SHA3_state_permute(uint64_t *s)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)24U; i0++)
  {
    uint64_t _C[5U] = { 0U };
    KRML_MAYBE_FOR5(i,
      (uint32_t)0U,
      (uint32_t)5U,
      (uint32_t)1U,
      _C[i] =
        s[i
        + (uint32_t)0U]
        ^
          (s[i
          + (uint32_t)5U]
          ^ (s[i + (uint32_t)10U] ^ (s[i + (uint32_t)15U] ^ s[i + (uint32_t)20U]))););
    KRML_MAYBE_FOR5(i1,
      (uint32_t)0U,
      (uint32_t)5U,
      (uint32_t)1U,
      uint64_t uu____0 = _C[(i1 + (uint32_t)1U) % (uint32_t)5U];
      uint64_t
      _D =
        _C[(i1 + (uint32_t)4U)
        % (uint32_t)5U]
        ^ (uu____0 << (uint32_t)1U | uu____0 >> (uint32_t)63U);
      KRML_MAYBE_FOR5(i,
        (uint32_t)0U,
        (uint32_t)5U,
        (uint32_t)1U,
        s[i1 + (uint32_t)5U * i] = s[i1 + (uint32_t)5U * i] ^ _D;););
    uint64_t x = s[1U];
    uint64_t current = x;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)24U; i++)
    {
      uint32_t _Y = keccak_piln[i];
      uint32_t r = keccak_rotc[i];
      uint64_t temp = s[_Y];
      uint64_t uu____1 = current;
      s[_Y] = uu____1 << r | uu____1 >> ((uint32_t)64U - r);
      current = temp;
    }
    KRML_MAYBE_FOR5(i,
      (uint32_t)0U,
      (uint32_t)5U,
      (uint32_t)1U,
      uint64_t
      v0 =
        s[(uint32_t)0U
        + (uint32_t)5U * i]
        ^ (~s[(uint32_t)1U + (uint32_t)5U * i] & s[(uint32_t)2U + (uint32_t)5U * i]);
      uint64_t
      v1 =
        s[(uint32_t)1U
        + (uint32_t)5U * i]
        ^ (~s[(uint32_t)2U + (uint32_t)5U * i] & s[(uint32_t)3U + (uint32_t)5U * i]);
      uint64_t
      v2 =
        s[(uint32_t)2U
        + (uint32_t)5U * i]
        ^ (~s[(uint32_t)3U + (uint32_t)5U * i] & s[(uint32_t)4U + (uint32_t)5U * i]);
      uint64_t
      v3 =
        s[(uint32_t)3U
        + (uint32_t)5U * i]
        ^ (~s[(uint32_t)4U + (uint32_t)5U * i] & s[(uint32_t)0U + (uint32_t)5U * i]);
      uint64_t
      v4 =
        s[(uint32_t)4U
        + (uint32_t)5U * i]
        ^ (~s[(uint32_t)0U + (uint32_t)5U * i] & s[(uint32_t)1U + (uint32_t)5U * i]);
      s[(uint32_t)0U + (uint32_t)5U * i] = v0;
      s[(uint32_t)1U + (uint32_t)5U * i] = v1;
      s[(uint32_t)2U + (uint32_t)5U * i] = v2;
      s[(uint32_t)3U + (uint32_t)5U * i] = v3;
      s[(uint32_t)4U + (uint32_t)5U * i] = v4;);
    uint64_t c = keccak_rndc[i0];
    s[0U] = s[0U] ^ c;
  }
}

/* SNIPPET_END: Hacl_Impl_SHA3_state_permute */

/* SNIPPET_START: Hacl_Impl_SHA3_loadState */

void Hacl_Impl_SHA3_loadState(uint32_t rateInBytes, uint8_t *input, uint64_t *s)
{
  uint8_t block[200U] = { 0U };
  memcpy(block, input, rateInBytes * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)25U; i++)
  {
    uint64_t u = load64_le(block + i * (uint32_t)8U);
    uint64_t x = u;
    s[i] = s[i] ^ x;
  }
}

/* SNIPPET_END: Hacl_Impl_SHA3_loadState */

/* SNIPPET_START: Hacl_Impl_SHA3_storeState */

void Hacl_Impl_SHA3_storeState(uint32_t rateInBytes, uint64_t *s, uint8_t *res)
{
  uint8_t block[200U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)25U; i++)
  {
    uint64_t sj = s[i];
    store64_le(block + i * (uint32_t)8U, sj);
  }
  memcpy(res, block, rateInBytes * sizeof (uint8_t));
}

/* SNIPPET_END: Hacl_Impl_SHA3_storeState */

/* SNIPPET_START: Hacl_Impl_SHA3_absorb */

void
Hacl_Impl_SHA3_absorb(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix
)
{
  uint32_t n_blocks = inputByteLen / rateInBytes;
  uint32_t rem = inputByteLen % rateInBytes;
  for (uint32_t i = (uint32_t)0U; i < n_blocks; i++)
  {
    uint8_t *block = input + i * rateInBytes;
    Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
    Hacl_Impl_SHA3_state_permute(s);
  }
  uint8_t *last = input + n_blocks * rateInBytes;
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes);
  uint8_t lastBlock[rateInBytes];
  memset(lastBlock, 0U, rateInBytes * sizeof (uint8_t));
  memcpy(lastBlock, last, rem * sizeof (uint8_t));
  lastBlock[rem] = delimitedSuffix;
  Hacl_Impl_SHA3_loadState(rateInBytes, lastBlock, s);
  if (!((delimitedSuffix & (uint8_t)0x80U) == (uint8_t)0U) && rem == rateInBytes - (uint32_t)1U)
  {
    Hacl_Impl_SHA3_state_permute(s);
  }
  KRML_CHECK_SIZE(sizeof (uint8_t), rateInBytes);
  uint8_t nextBlock[rateInBytes];
  memset(nextBlock, 0U, rateInBytes * sizeof (uint8_t));
  nextBlock[rateInBytes - (uint32_t)1U] = (uint8_t)0x80U;
  Hacl_Impl_SHA3_loadState(rateInBytes, nextBlock, s);
  Hacl_Impl_SHA3_state_permute(s);
}

/* SNIPPET_END: Hacl_Impl_SHA3_absorb */

/* SNIPPET_START: Hacl_Impl_SHA3_squeeze */

void
Hacl_Impl_SHA3_squeeze(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t outputByteLen,
  uint8_t *output
)
{
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

/* SNIPPET_END: Hacl_Impl_SHA3_squeeze */

/* SNIPPET_START: Hacl_Impl_SHA3_keccak */

void
Hacl_Impl_SHA3_keccak(
  uint32_t rate,
  uint32_t capacity,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  uint32_t rateInBytes = rate / (uint32_t)8U;
  uint64_t s[25U] = { 0U };
  Hacl_Impl_SHA3_absorb(s, rateInBytes, inputByteLen, input, delimitedSuffix);
  Hacl_Impl_SHA3_squeeze(s, rateInBytes, outputByteLen, output);
}

/* SNIPPET_END: Hacl_Impl_SHA3_keccak */

/* SNIPPET_START: Hacl_SHA3_shake128_hacl */

void
Hacl_SHA3_shake128_hacl(
  uint32_t inputByteLen,
  uint8_t *input,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1344U,
    (uint32_t)256U,
    inputByteLen,
    input,
    (uint8_t)0x1FU,
    outputByteLen,
    output);
}

/* SNIPPET_END: Hacl_SHA3_shake128_hacl */

/* SNIPPET_START: Hacl_SHA3_shake256_hacl */

void
Hacl_SHA3_shake256_hacl(
  uint32_t inputByteLen,
  uint8_t *input,
  uint32_t outputByteLen,
  uint8_t *output
)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1088U,
    (uint32_t)512U,
    inputByteLen,
    input,
    (uint8_t)0x1FU,
    outputByteLen,
    output);
}

/* SNIPPET_END: Hacl_SHA3_shake256_hacl */

/* SNIPPET_START: Hacl_SHA3_sha3_224 */

void Hacl_SHA3_sha3_224(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1152U,
    (uint32_t)448U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)28U,
    output);
}

/* SNIPPET_END: Hacl_SHA3_sha3_224 */

/* SNIPPET_START: Hacl_SHA3_sha3_256 */

void Hacl_SHA3_sha3_256(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)1088U,
    (uint32_t)512U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)32U,
    output);
}

/* SNIPPET_END: Hacl_SHA3_sha3_256 */

/* SNIPPET_START: Hacl_SHA3_sha3_384 */

void Hacl_SHA3_sha3_384(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)832U,
    (uint32_t)768U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)48U,
    output);
}

/* SNIPPET_END: Hacl_SHA3_sha3_384 */

/* SNIPPET_START: Hacl_SHA3_sha3_512 */

void Hacl_SHA3_sha3_512(uint32_t inputByteLen, uint8_t *input, uint8_t *output)
{
  Hacl_Impl_SHA3_keccak((uint32_t)576U,
    (uint32_t)1024U,
    inputByteLen,
    input,
    (uint8_t)0x06U,
    (uint32_t)64U,
    output);
}

/* SNIPPET_END: Hacl_SHA3_sha3_512 */

