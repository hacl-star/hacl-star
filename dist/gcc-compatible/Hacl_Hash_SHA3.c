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


#include "internal/Hacl_Hash_SHA3.h"

Hacl_Streaming_MD_state_64 *Hacl_Streaming_SHA3_create_in_256(void)
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC((uint32_t)136U, sizeof (uint8_t));
  uint64_t *block_state = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
  Hacl_Streaming_MD_state_64
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)(uint32_t)0U };
  Hacl_Streaming_MD_state_64
  *p = (Hacl_Streaming_MD_state_64 *)KRML_HOST_MALLOC(sizeof (Hacl_Streaming_MD_state_64));
  p[0U] = s;
  memset(block_state, 0U, (uint32_t)25U * sizeof (uint64_t));
  return p;
}

void Hacl_Streaming_SHA3_init_256(Hacl_Streaming_MD_state_64 *s)
{
  Hacl_Streaming_MD_state_64 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  memset(block_state, 0U, (uint32_t)25U * sizeof (uint64_t));
  Hacl_Streaming_MD_state_64
  tmp = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)(uint32_t)0U };
  s[0U] = tmp;
}

/**
0 = success, 1 = max length exceeded. Due to internal limitations, there is currently an arbitrary limit of 2^64-1 bytes that can be hashed through this interface.
*/
uint32_t
Hacl_Streaming_SHA3_update_256(Hacl_Streaming_MD_state_64 *p, uint8_t *data, uint32_t len)
{
  Hacl_Streaming_MD_state_64 s = *p;
  uint64_t total_len = s.total_len;
  if ((uint64_t)len > (uint64_t)18446744073709551615U - total_len)
  {
    return (uint32_t)1U;
  }
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)136U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)136U);
  }
  if (len <= (uint32_t)136U - sz)
  {
    Hacl_Streaming_MD_state_64 s1 = *p;
    uint64_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)136U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)136U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_MD_state_64){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
  }
  else if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_MD_state_64 s1 = *p;
    uint64_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)136U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)136U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      {
        uint8_t *block = buf + (uint32_t)0U * (uint32_t)136U;
        Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, block, block_state1);
      }
    }
    uint32_t ite;
    if ((uint64_t)len % (uint64_t)(uint32_t)136U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite = (uint32_t)136U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)136U);
    }
    uint32_t n_blocks = (len - ite) / (uint32_t)136U;
    uint32_t data1_len = n_blocks * (uint32_t)136U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    for (uint32_t i = (uint32_t)0U; i < data1_len / (uint32_t)136U; i++)
    {
      uint8_t *block = data1 + i * (uint32_t)136U;
      Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, block, block_state1);
    }
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_MD_state_64){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
  }
  else
  {
    uint32_t diff = (uint32_t)136U - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_MD_state_64 s1 = *p;
    uint64_t *block_state10 = s1.block_state;
    uint8_t *buf0 = s1.buf;
    uint64_t total_len10 = s1.total_len;
    uint32_t sz10;
    if (total_len10 % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len10 > (uint64_t)0U)
    {
      sz10 = (uint32_t)136U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)136U);
    }
    uint8_t *buf2 = buf0 + sz10;
    memcpy(buf2, data1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *p
    =
      (
        (Hacl_Streaming_MD_state_64){
          .block_state = block_state10,
          .buf = buf0,
          .total_len = total_len2
        }
      );
    Hacl_Streaming_MD_state_64 s10 = *p;
    uint64_t *block_state1 = s10.block_state;
    uint8_t *buf = s10.buf;
    uint64_t total_len1 = s10.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)136U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)136U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      {
        uint8_t *block = buf + (uint32_t)0U * (uint32_t)136U;
        Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, block, block_state1);
      }
    }
    uint32_t ite;
    if
    (
      (uint64_t)(len - diff)
      % (uint64_t)(uint32_t)136U
      == (uint64_t)0U
      && (uint64_t)(len - diff) > (uint64_t)0U
    )
    {
      ite = (uint32_t)136U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)136U);
    }
    uint32_t n_blocks = (len - diff - ite) / (uint32_t)136U;
    uint32_t data1_len = n_blocks * (uint32_t)136U;
    uint32_t data2_len = len - diff - data1_len;
    uint8_t *data11 = data2;
    uint8_t *data21 = data2 + data1_len;
    for (uint32_t i = (uint32_t)0U; i < data1_len / (uint32_t)136U; i++)
    {
      uint8_t *block = data11 + i * (uint32_t)136U;
      Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, block, block_state1);
    }
    uint8_t *dst = buf;
    memcpy(dst, data21, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_MD_state_64){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(len - diff)
        }
      );
  }
  return (uint32_t)0U;
}

void Hacl_Streaming_SHA3_finish_256(Hacl_Streaming_MD_state_64 *p, uint8_t *dst)
{
  Hacl_Streaming_MD_state_64 scrut = *p;
  uint64_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)136U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)136U);
  }
  uint8_t *buf_1 = buf_;
  uint64_t tmp_block_state[25U] = { 0U };
  memcpy(tmp_block_state, block_state, (uint32_t)25U * sizeof (uint64_t));
  uint32_t ite;
  if (r % (uint32_t)136U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = (uint32_t)136U;
  }
  else
  {
    ite = r % (uint32_t)136U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  if (r == (uint32_t)136U)
  {
    Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, buf_last, tmp_block_state);
    uint8_t *uu____0 = buf_last + r;
    uint8_t lastBlock[136U] = { 0U };
    memcpy(lastBlock, uu____0, (uint32_t)0U * sizeof (uint8_t));
    lastBlock[0U] = (uint8_t)0x06U;
    Hacl_Impl_SHA3_loadState((uint32_t)136U, lastBlock, tmp_block_state);
    uint8_t nextBlock[136U] = { 0U };
    nextBlock[135U] = (uint8_t)0x80U;
    Hacl_Impl_SHA3_loadState((uint32_t)136U, nextBlock, tmp_block_state);
    Hacl_Impl_SHA3_state_permute(tmp_block_state);
  }
  else
  {
    uint8_t lastBlock[136U] = { 0U };
    memcpy(lastBlock, buf_last, r * sizeof (uint8_t));
    lastBlock[r] = (uint8_t)0x06U;
    Hacl_Impl_SHA3_loadState((uint32_t)136U, lastBlock, tmp_block_state);
    uint8_t nextBlock[136U] = { 0U };
    nextBlock[135U] = (uint8_t)0x80U;
    Hacl_Impl_SHA3_loadState((uint32_t)136U, nextBlock, tmp_block_state);
    Hacl_Impl_SHA3_state_permute(tmp_block_state);
  }
  Hacl_Impl_SHA3_squeeze(tmp_block_state, (uint32_t)136U, (uint32_t)32U, dst);
}

void Hacl_Streaming_SHA3_free_256(Hacl_Streaming_MD_state_64 *s)
{
  Hacl_Streaming_MD_state_64 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

Hacl_Streaming_MD_state_64 *Hacl_Streaming_SHA3_copy_256(Hacl_Streaming_MD_state_64 *s0)
{
  Hacl_Streaming_MD_state_64 scrut = *s0;
  uint64_t *block_state0 = scrut.block_state;
  uint8_t *buf0 = scrut.buf;
  uint64_t total_len0 = scrut.total_len;
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC((uint32_t)136U, sizeof (uint8_t));
  memcpy(buf, buf0, (uint32_t)136U * sizeof (uint8_t));
  uint64_t *block_state = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
  memcpy(block_state, block_state0, (uint32_t)25U * sizeof (uint64_t));
  Hacl_Streaming_MD_state_64
  s = { .block_state = block_state, .buf = buf, .total_len = total_len0 };
  Hacl_Streaming_MD_state_64
  *p = (Hacl_Streaming_MD_state_64 *)KRML_HOST_MALLOC(sizeof (Hacl_Streaming_MD_state_64));
  p[0U] = s;
  return p;
}

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

static const
uint32_t
keccak_rotc[24U] =
  {
    (uint32_t)1U, (uint32_t)3U, (uint32_t)6U, (uint32_t)10U, (uint32_t)15U, (uint32_t)21U,
    (uint32_t)28U, (uint32_t)36U, (uint32_t)45U, (uint32_t)55U, (uint32_t)2U, (uint32_t)14U,
    (uint32_t)27U, (uint32_t)41U, (uint32_t)56U, (uint32_t)8U, (uint32_t)25U, (uint32_t)43U,
    (uint32_t)62U, (uint32_t)18U, (uint32_t)39U, (uint32_t)61U, (uint32_t)20U, (uint32_t)44U
  };

static const
uint32_t
keccak_piln[24U] =
  {
    (uint32_t)10U, (uint32_t)7U, (uint32_t)11U, (uint32_t)17U, (uint32_t)18U, (uint32_t)3U,
    (uint32_t)5U, (uint32_t)16U, (uint32_t)8U, (uint32_t)21U, (uint32_t)24U, (uint32_t)4U,
    (uint32_t)15U, (uint32_t)23U, (uint32_t)19U, (uint32_t)13U, (uint32_t)12U, (uint32_t)2U,
    (uint32_t)20U, (uint32_t)14U, (uint32_t)22U, (uint32_t)9U, (uint32_t)6U, (uint32_t)1U
  };

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

static void storeState(uint32_t rateInBytes, uint64_t *s, uint8_t *res)
{
  uint8_t block[200U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)25U; i++)
  {
    uint64_t sj = s[i];
    store64_le(block + i * (uint32_t)8U, sj);
  }
  memcpy(res, block, rateInBytes * sizeof (uint8_t));
}

void Hacl_Impl_SHA3_absorb_inner(uint32_t rateInBytes, uint8_t *block, uint64_t *s)
{
  Hacl_Impl_SHA3_loadState(rateInBytes, block, s);
  Hacl_Impl_SHA3_state_permute(s);
}

static void
absorb(
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
    Hacl_Impl_SHA3_absorb_inner(rateInBytes, block, s);
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
    storeState(rateInBytes, s, blocks + i * rateInBytes);
    Hacl_Impl_SHA3_state_permute(s);
  }
  storeState(remOut, s, last);
}

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
  absorb(s, rateInBytes, inputByteLen, input, delimitedSuffix);
  Hacl_Impl_SHA3_squeeze(s, rateInBytes, outputByteLen, output);
}

