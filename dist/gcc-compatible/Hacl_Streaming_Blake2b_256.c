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


#include "Hacl_Streaming_Blake2b_256.h"



/**
  State allocation function when there is no key
*/
Hacl_Streaming_Blake2b_256_blake2b_256_state
*Hacl_Streaming_Blake2b_256_blake2b_256_no_key_create_in()
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec256
  *wv =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * (uint32_t)4U);
  memset(wv, 0U, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Lib_IntVector_Intrinsics_vec256
  *b =
    (Lib_IntVector_Intrinsics_vec256 *)KRML_ALIGNED_MALLOC(32,
      sizeof (Lib_IntVector_Intrinsics_vec256) * (uint32_t)4U);
  memset(b, 0U, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec256));
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = { .fst = wv, .snd = b };
  Hacl_Streaming_Blake2b_256_blake2b_256_state
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  Hacl_Streaming_Blake2b_256_blake2b_256_state
  *p =
    (Hacl_Streaming_Blake2b_256_blake2b_256_state *)KRML_HOST_MALLOC(sizeof (
        Hacl_Streaming_Blake2b_256_blake2b_256_state
      ));
  p[0U] = s;
  Hacl_Blake2b_256_blake2b_init(block_state.snd, (uint32_t)0U, (uint32_t)64U);
  return p;
}

/**
  (Re-)initialization function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_init(
  Hacl_Streaming_Blake2b_256_blake2b_256_state *s
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state scrut = *s;
  uint8_t *buf = scrut.buf;
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = scrut.block_state;
  Hacl_Blake2b_256_blake2b_init(block_state.snd, (uint32_t)0U, (uint32_t)64U);
  s[0U] =
    (
      (Hacl_Streaming_Blake2b_256_blake2b_256_state){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

/**
  Update function when there is no key; 0 = success, 1 = max length exceeded
*/
uint32_t
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_update(
  Hacl_Streaming_Blake2b_256_blake2b_256_state *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state s = *p;
  uint64_t total_len = s.total_len;
  if ((uint64_t)len > (uint64_t)0xffffffffffffffffU - total_len)
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
  if (len <= (uint32_t)128U - sz)
  {
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s1.block_state;
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
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Blake2b_256_blake2b_256_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
  }
  else if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s1.block_state;
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
      Lib_IntVector_Intrinsics_vec256 *wv = block_state1.fst;
      Lib_IntVector_Intrinsics_vec256 *hash = block_state1.snd;
      uint32_t nb = (uint32_t)1U;
      Hacl_Blake2b_256_blake2b_update_multi((uint32_t)128U,
        wv,
        hash,
        FStar_UInt128_uint64_to_uint128(prevlen),
        buf,
        nb);
    }
    uint32_t ite;
    if ((uint64_t)len % (uint64_t)(uint32_t)128U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite = (uint32_t)128U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)128U);
    }
    uint32_t n_blocks = (len - ite) / (uint32_t)128U;
    uint32_t data1_len = n_blocks * (uint32_t)128U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    Lib_IntVector_Intrinsics_vec256 *wv = block_state1.fst;
    Lib_IntVector_Intrinsics_vec256 *hash = block_state1.snd;
    uint32_t nb = data1_len / (uint32_t)128U;
    Hacl_Blake2b_256_blake2b_update_multi(data1_len,
      wv,
      hash,
      FStar_UInt128_uint64_to_uint128(total_len1),
      data1,
      nb);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Blake2b_256_blake2b_256_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
  }
  else
  {
    uint32_t diff = (uint32_t)128U - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state10 = s1.block_state;
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
    memcpy(buf2, data1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *p
    =
      (
        (Hacl_Streaming_Blake2b_256_blake2b_256_state){
          .block_state = block_state10,
          .buf = buf0,
          .total_len = total_len2
        }
      );
    Hacl_Streaming_Blake2b_256_blake2b_256_state s10 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s10.block_state;
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
      Lib_IntVector_Intrinsics_vec256 *wv = block_state1.fst;
      Lib_IntVector_Intrinsics_vec256 *hash = block_state1.snd;
      uint32_t nb = (uint32_t)1U;
      Hacl_Blake2b_256_blake2b_update_multi((uint32_t)128U,
        wv,
        hash,
        FStar_UInt128_uint64_to_uint128(prevlen),
        buf,
        nb);
    }
    uint32_t ite;
    if
    (
      (uint64_t)(len - diff)
      % (uint64_t)(uint32_t)128U
      == (uint64_t)0U
      && (uint64_t)(len - diff) > (uint64_t)0U
    )
    {
      ite = (uint32_t)128U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)128U);
    }
    uint32_t n_blocks = (len - diff - ite) / (uint32_t)128U;
    uint32_t data1_len = n_blocks * (uint32_t)128U;
    uint32_t data2_len = len - diff - data1_len;
    uint8_t *data11 = data2;
    uint8_t *data21 = data2 + data1_len;
    Lib_IntVector_Intrinsics_vec256 *wv = block_state1.fst;
    Lib_IntVector_Intrinsics_vec256 *hash = block_state1.snd;
    uint32_t nb = data1_len / (uint32_t)128U;
    Hacl_Blake2b_256_blake2b_update_multi(data1_len,
      wv,
      hash,
      FStar_UInt128_uint64_to_uint128(total_len1),
      data11,
      nb);
    uint8_t *dst = buf;
    memcpy(dst, data21, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Blake2b_256_blake2b_256_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(len - diff)
        }
      );
  }
  return (uint32_t)0U;
}

/**
  Finish function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_finish(
  Hacl_Streaming_Blake2b_256_blake2b_256_state *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state scrut = *p;
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = scrut.block_state;
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
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv0[4U] KRML_POST_ALIGN(32) = { 0U };
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 b[4U] KRML_POST_ALIGN(32) = { 0U };
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state tmp_block_state = { .fst = wv0, .snd = b };
  Lib_IntVector_Intrinsics_vec256 *src_b = block_state.snd;
  Lib_IntVector_Intrinsics_vec256 *dst_b = tmp_block_state.snd;
  memcpy(dst_b, src_b, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec256));
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
  Lib_IntVector_Intrinsics_vec256 *wv1 = tmp_block_state.fst;
  Lib_IntVector_Intrinsics_vec256 *hash0 = tmp_block_state.snd;
  uint32_t nb = (uint32_t)0U;
  Hacl_Blake2b_256_blake2b_update_multi((uint32_t)0U,
    wv1,
    hash0,
    FStar_UInt128_uint64_to_uint128(prev_len),
    buf_multi,
    nb);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  Lib_IntVector_Intrinsics_vec256 *wv = tmp_block_state.fst;
  Lib_IntVector_Intrinsics_vec256 *hash = tmp_block_state.snd;
  Hacl_Blake2b_256_blake2b_update_last(r,
    wv,
    hash,
    FStar_UInt128_uint64_to_uint128(prev_len_last),
    r,
    buf_last);
  Hacl_Blake2b_256_blake2b_finish((uint32_t)64U, dst, tmp_block_state.snd);
}

/**
  Free state function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_free(
  Hacl_Streaming_Blake2b_256_blake2b_256_state *s
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state scrut = *s;
  uint8_t *buf = scrut.buf;
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec256 *wv = block_state.fst;
  Lib_IntVector_Intrinsics_vec256 *b = block_state.snd;
  KRML_ALIGNED_FREE(wv);
  KRML_ALIGNED_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

