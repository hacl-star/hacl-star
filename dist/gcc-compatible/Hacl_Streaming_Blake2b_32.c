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


#include "Hacl_Streaming_Blake2b_32.h"

/**
  State allocation function when there is no key
*/
Hacl_Streaming_Blake2b_32_state *Hacl_Streaming_Blake2b_32_malloc(void)
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  uint64_t *wv = (uint64_t *)KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
  uint64_t *b = (uint64_t *)KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
  Hacl_Streaming_Blake2b_32_block_state block_state1 = { .fst = wv, .snd = b };
  Hacl_Streaming_Blake2b_32_state
  s = { .block_state = block_state1, .buf = buf, .total_len = (uint64_t)(uint32_t)0U };
  Hacl_Streaming_Blake2b_32_state
  *p =
    (Hacl_Streaming_Blake2b_32_state *)KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Blake2b_32_state));
  p[0U] = s;
  Hacl_Blake2b_32_blake2b_init(block_state1.snd, (uint32_t)0U, (uint32_t)64U);
  return p;
}

/**
  Re-initialization function when there is no key
*/
void Hacl_Streaming_Blake2b_32_reset(Hacl_Streaming_Blake2b_32_state *state1)
{
  Hacl_Streaming_Blake2b_32_state scrut = *state1;
  uint8_t *buf = scrut.buf;
  Hacl_Streaming_Blake2b_32_block_state block_state1 = scrut.block_state;
  Hacl_Blake2b_32_blake2b_init(block_state1.snd, (uint32_t)0U, (uint32_t)64U);
  Hacl_Streaming_Blake2b_32_state
  tmp = { .block_state = block_state1, .buf = buf, .total_len = (uint64_t)(uint32_t)0U };
  state1[0U] = tmp;
}

/**
  Update function when there is no key; 0 = success, 1 = max length exceeded
*/
uint32_t
Hacl_Streaming_Blake2b_32_update(
  Hacl_Streaming_Blake2b_32_state *state1,
  uint8_t *chunk,
  uint32_t chunk_len
)
{
  Hacl_Streaming_Blake2b_32_state s = *state1;
  uint64_t total_len = s.total_len;
  if ((uint64_t)chunk_len > (uint64_t)0xffffffffffffffffU - total_len)
  {
    return (uint32_t)1U;
  }
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)128U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)128U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)128U);
  }
  if (chunk_len <= (uint32_t)128U - sz)
  {
    Hacl_Streaming_Blake2b_32_state s1 = *state1;
    Hacl_Streaming_Blake2b_32_block_state block_state2 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
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
    memcpy(buf2, chunk, chunk_len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)chunk_len;
    *state1
    =
      (
        (Hacl_Streaming_Blake2b_32_state){
          .block_state = block_state2,
          .buf = buf,
          .total_len = total_len2
        }
      );
  }
  else if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Blake2b_32_state s1 = *state1;
    Hacl_Streaming_Blake2b_32_block_state block_state2 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
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
      uint64_t *wv = block_state2.fst;
      uint64_t *hash = block_state2.snd;
      uint32_t nb = (uint32_t)1U;
      Hacl_Blake2b_32_blake2b_update_multi((uint32_t)128U,
        wv,
        hash,
        FStar_UInt128_uint64_to_uint128(prevlen),
        buf,
        nb);
    }
    uint32_t ite;
    if
    (
      (uint64_t)chunk_len
      % (uint64_t)(uint32_t)128U
      == (uint64_t)0U
      && (uint64_t)chunk_len > (uint64_t)0U
    )
    {
      ite = (uint32_t)128U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)chunk_len % (uint64_t)(uint32_t)128U);
    }
    uint32_t n_blocks = (chunk_len - ite) / (uint32_t)128U;
    uint32_t data1_len = n_blocks * (uint32_t)128U;
    uint32_t data2_len = chunk_len - data1_len;
    uint8_t *data1 = chunk;
    uint8_t *data2 = chunk + data1_len;
    uint64_t *wv = block_state2.fst;
    uint64_t *hash = block_state2.snd;
    uint32_t nb = data1_len / (uint32_t)128U;
    Hacl_Blake2b_32_blake2b_update_multi(data1_len,
      wv,
      hash,
      FStar_UInt128_uint64_to_uint128(total_len1),
      data1,
      nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state1
    =
      (
        (Hacl_Streaming_Blake2b_32_state){
          .block_state = block_state2,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)chunk_len
        }
      );
  }
  else
  {
    uint32_t diff = (uint32_t)128U - sz;
    uint8_t *chunk1 = chunk;
    uint8_t *chunk2 = chunk + diff;
    Hacl_Streaming_Blake2b_32_state s1 = *state1;
    Hacl_Streaming_Blake2b_32_block_state block_state20 = s1.block_state;
    uint8_t *buf0 = s1.buf;
    uint64_t total_len10 = s1.total_len;
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
    memcpy(buf2, chunk1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *state1
    =
      (
        (Hacl_Streaming_Blake2b_32_state){
          .block_state = block_state20,
          .buf = buf0,
          .total_len = total_len2
        }
      );
    Hacl_Streaming_Blake2b_32_state s10 = *state1;
    Hacl_Streaming_Blake2b_32_block_state block_state2 = s10.block_state;
    uint8_t *buf = s10.buf;
    uint64_t total_len1 = s10.total_len;
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
      uint64_t *wv = block_state2.fst;
      uint64_t *hash = block_state2.snd;
      uint32_t nb = (uint32_t)1U;
      Hacl_Blake2b_32_blake2b_update_multi((uint32_t)128U,
        wv,
        hash,
        FStar_UInt128_uint64_to_uint128(prevlen),
        buf,
        nb);
    }
    uint32_t ite;
    if
    (
      (uint64_t)(chunk_len - diff)
      % (uint64_t)(uint32_t)128U
      == (uint64_t)0U
      && (uint64_t)(chunk_len - diff) > (uint64_t)0U
    )
    {
      ite = (uint32_t)128U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)(chunk_len - diff) % (uint64_t)(uint32_t)128U);
    }
    uint32_t n_blocks = (chunk_len - diff - ite) / (uint32_t)128U;
    uint32_t data1_len = n_blocks * (uint32_t)128U;
    uint32_t data2_len = chunk_len - diff - data1_len;
    uint8_t *data1 = chunk2;
    uint8_t *data2 = chunk2 + data1_len;
    uint64_t *wv = block_state2.fst;
    uint64_t *hash = block_state2.snd;
    uint32_t nb = data1_len / (uint32_t)128U;
    Hacl_Blake2b_32_blake2b_update_multi(data1_len,
      wv,
      hash,
      FStar_UInt128_uint64_to_uint128(total_len1),
      data1,
      nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state1
    =
      (
        (Hacl_Streaming_Blake2b_32_state){
          .block_state = block_state2,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(chunk_len - diff)
        }
      );
  }
  return (uint32_t)0U;
}

/**
  Finish function when there is no key
*/
void Hacl_Streaming_Blake2b_32_digest(Hacl_Streaming_Blake2b_32_state *state1, uint8_t *output)
{
  Hacl_Streaming_Blake2b_32_state scrut = *state1;
  Hacl_Streaming_Blake2b_32_block_state block_state1 = scrut.block_state;
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
  uint64_t wv0[16U] = { 0U };
  uint64_t b[16U] = { 0U };
  Hacl_Streaming_Blake2b_32_block_state tmp_block_state = { .fst = wv0, .snd = b };
  uint64_t *src_b = block_state1.snd;
  uint64_t *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)16U * sizeof (uint64_t));
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = (uint32_t)128U;
  }
  else
  {
    ite = r % (uint32_t)128U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  uint64_t *wv1 = tmp_block_state.fst;
  uint64_t *hash0 = tmp_block_state.snd;
  uint32_t nb = (uint32_t)0U;
  Hacl_Blake2b_32_blake2b_update_multi((uint32_t)0U,
    wv1,
    hash0,
    FStar_UInt128_uint64_to_uint128(prev_len),
    buf_multi,
    nb);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  uint64_t *wv = tmp_block_state.fst;
  uint64_t *hash = tmp_block_state.snd;
  Hacl_Blake2b_32_blake2b_update_last(r,
    wv,
    hash,
    FStar_UInt128_uint64_to_uint128(prev_len_last),
    r,
    buf_last);
  Hacl_Blake2b_32_blake2b_finish((uint32_t)64U, output, tmp_block_state.snd);
}

/**
  Free state function when there is no key
*/
void Hacl_Streaming_Blake2b_32_free(Hacl_Streaming_Blake2b_32_state *state1)
{
  Hacl_Streaming_Blake2b_32_state scrut = *state1;
  uint8_t *buf = scrut.buf;
  Hacl_Streaming_Blake2b_32_block_state block_state1 = scrut.block_state;
  uint64_t *wv = block_state1.fst;
  uint64_t *b = block_state1.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(state1);
}

