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


#include "Hacl_Streaming_Poly1305_128.h"

Hacl_Streaming_Poly1305_128_poly1305_128_state *Hacl_Streaming_Poly1305_128_malloc(uint8_t *k)
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  Lib_IntVector_Intrinsics_vec128
  *r1 =
    (Lib_IntVector_Intrinsics_vec128 *)KRML_ALIGNED_MALLOC(16,
      sizeof (Lib_IntVector_Intrinsics_vec128) * (uint32_t)25U);
  memset(r1, 0U, (uint32_t)25U * sizeof (Lib_IntVector_Intrinsics_vec128));
  Lib_IntVector_Intrinsics_vec128 *block_state = r1;
  uint8_t *k_ = (uint8_t *)KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  memcpy(k_, k, (uint32_t)32U * sizeof (uint8_t));
  uint8_t *k_0 = k_;
  Hacl_Streaming_Poly1305_128_poly1305_128_state
  s =
    { .block_state = block_state, .buf = buf, .total_len = (uint64_t)(uint32_t)0U, .p_key = k_0 };
  Hacl_Streaming_Poly1305_128_poly1305_128_state
  *p =
    (Hacl_Streaming_Poly1305_128_poly1305_128_state *)KRML_HOST_MALLOC(sizeof (
        Hacl_Streaming_Poly1305_128_poly1305_128_state
      ));
  p[0U] = s;
  Hacl_Poly1305_128_poly1305_init(block_state, k);
  return p;
}

void
Hacl_Streaming_Poly1305_128_reset(
  uint8_t *k,
  Hacl_Streaming_Poly1305_128_poly1305_128_state *state
)
{
  Hacl_Streaming_Poly1305_128_poly1305_128_state scrut = *state;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  Lib_IntVector_Intrinsics_vec128 *block_state = scrut.block_state;
  Hacl_Poly1305_128_poly1305_init(block_state, k);
  memcpy(k_, k, (uint32_t)32U * sizeof (uint8_t));
  uint8_t *k_1 = k_;
  Hacl_Streaming_Poly1305_128_poly1305_128_state
  tmp =
    { .block_state = block_state, .buf = buf, .total_len = (uint64_t)(uint32_t)0U, .p_key = k_1 };
  state[0U] = tmp;
}

/**
0 = success, 1 = max length exceeded
*/
uint32_t
Hacl_Streaming_Poly1305_128_update(
  Hacl_Streaming_Poly1305_128_poly1305_128_state *state,
  uint8_t *chunk,
  uint32_t chunk_len
)
{
  Hacl_Streaming_Poly1305_128_poly1305_128_state s = *state;
  uint64_t total_len = s.total_len;
  if ((uint64_t)chunk_len > (uint64_t)0xffffffffU - total_len)
  {
    return (uint32_t)1U;
  }
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)32U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)32U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)32U);
  }
  if (chunk_len <= (uint32_t)32U - sz)
  {
    Hacl_Streaming_Poly1305_128_poly1305_128_state s1 = *state;
    Lib_IntVector_Intrinsics_vec128 *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)32U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)32U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)32U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, chunk, chunk_len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)chunk_len;
    *state
    =
      (
        (Hacl_Streaming_Poly1305_128_poly1305_128_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2,
          .p_key = k_1
        }
      );
  }
  else if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Poly1305_128_poly1305_128_state s1 = *state;
    Lib_IntVector_Intrinsics_vec128 *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)32U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)32U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)32U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      Hacl_Poly1305_128_poly1305_update(block_state1, (uint32_t)32U, buf);
    }
    uint32_t ite;
    if
    (
      (uint64_t)chunk_len
      % (uint64_t)(uint32_t)32U
      == (uint64_t)0U
      && (uint64_t)chunk_len > (uint64_t)0U
    )
    {
      ite = (uint32_t)32U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)chunk_len % (uint64_t)(uint32_t)32U);
    }
    uint32_t n_blocks = (chunk_len - ite) / (uint32_t)32U;
    uint32_t data1_len = n_blocks * (uint32_t)32U;
    uint32_t data2_len = chunk_len - data1_len;
    uint8_t *data1 = chunk;
    uint8_t *data2 = chunk + data1_len;
    Hacl_Poly1305_128_poly1305_update(block_state1, data1_len, data1);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Streaming_Poly1305_128_poly1305_128_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)chunk_len,
          .p_key = k_1
        }
      );
  }
  else
  {
    uint32_t diff = (uint32_t)32U - sz;
    uint8_t *chunk1 = chunk;
    uint8_t *chunk2 = chunk + diff;
    Hacl_Streaming_Poly1305_128_poly1305_128_state s1 = *state;
    Lib_IntVector_Intrinsics_vec128 *block_state10 = s1.block_state;
    uint8_t *buf0 = s1.buf;
    uint64_t total_len10 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint32_t sz10;
    if (total_len10 % (uint64_t)(uint32_t)32U == (uint64_t)0U && total_len10 > (uint64_t)0U)
    {
      sz10 = (uint32_t)32U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)32U);
    }
    uint8_t *buf2 = buf0 + sz10;
    memcpy(buf2, chunk1, diff * sizeof (uint8_t));
    uint64_t total_len2 = total_len10 + (uint64_t)diff;
    *state
    =
      (
        (Hacl_Streaming_Poly1305_128_poly1305_128_state){
          .block_state = block_state10,
          .buf = buf0,
          .total_len = total_len2,
          .p_key = k_1
        }
      );
    Hacl_Streaming_Poly1305_128_poly1305_128_state s10 = *state;
    Lib_IntVector_Intrinsics_vec128 *block_state1 = s10.block_state;
    uint8_t *buf = s10.buf;
    uint64_t total_len1 = s10.total_len;
    uint8_t *k_10 = s10.p_key;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)32U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)32U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)32U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      Hacl_Poly1305_128_poly1305_update(block_state1, (uint32_t)32U, buf);
    }
    uint32_t ite;
    if
    (
      (uint64_t)(chunk_len - diff)
      % (uint64_t)(uint32_t)32U
      == (uint64_t)0U
      && (uint64_t)(chunk_len - diff) > (uint64_t)0U
    )
    {
      ite = (uint32_t)32U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)(chunk_len - diff) % (uint64_t)(uint32_t)32U);
    }
    uint32_t n_blocks = (chunk_len - diff - ite) / (uint32_t)32U;
    uint32_t data1_len = n_blocks * (uint32_t)32U;
    uint32_t data2_len = chunk_len - diff - data1_len;
    uint8_t *data1 = chunk2;
    uint8_t *data2 = chunk2 + data1_len;
    Hacl_Poly1305_128_poly1305_update(block_state1, data1_len, data1);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *state
    =
      (
        (Hacl_Streaming_Poly1305_128_poly1305_128_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)(chunk_len - diff),
          .p_key = k_10
        }
      );
  }
  return (uint32_t)0U;
}

void
Hacl_Streaming_Poly1305_128_digest(
  Hacl_Streaming_Poly1305_128_poly1305_128_state *state,
  uint8_t *output
)
{
  Hacl_Streaming_Poly1305_128_poly1305_128_state scrut = *state;
  Lib_IntVector_Intrinsics_vec128 *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *k_ = scrut.p_key;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)32U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)32U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)32U);
  }
  uint8_t *buf_1 = buf_;
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 r1[25U] KRML_POST_ALIGN(16) = { 0U };
  Lib_IntVector_Intrinsics_vec128 *tmp_block_state = r1;
  memcpy(tmp_block_state, block_state, (uint32_t)25U * sizeof (Lib_IntVector_Intrinsics_vec128));
  uint32_t ite0;
  if (r % (uint32_t)16U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite0 = (uint32_t)16U;
  }
  else
  {
    ite0 = r % (uint32_t)16U;
  }
  uint8_t *buf_last = buf_1 + r - ite0;
  uint8_t *buf_multi = buf_1;
  uint32_t ite;
  if (r % (uint32_t)16U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = (uint32_t)16U;
  }
  else
  {
    ite = r % (uint32_t)16U;
  }
  Hacl_Poly1305_128_poly1305_update(tmp_block_state, r - ite, buf_multi);
  uint32_t ite1;
  if (r % (uint32_t)16U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite1 = (uint32_t)16U;
  }
  else
  {
    ite1 = r % (uint32_t)16U;
  }
  uint64_t prev_len_last = total_len - (uint64_t)ite1;
  uint32_t ite2;
  if (r % (uint32_t)16U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite2 = (uint32_t)16U;
  }
  else
  {
    ite2 = r % (uint32_t)16U;
  }
  Hacl_Poly1305_128_poly1305_update(tmp_block_state, ite2, buf_last);
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 tmp[25U] KRML_POST_ALIGN(16) = { 0U };
  memcpy(tmp, tmp_block_state, (uint32_t)25U * sizeof (Lib_IntVector_Intrinsics_vec128));
  Hacl_Poly1305_128_poly1305_finish(output, k_, tmp);
}

void Hacl_Streaming_Poly1305_128_free(Hacl_Streaming_Poly1305_128_poly1305_128_state *state)
{
  Hacl_Streaming_Poly1305_128_poly1305_128_state scrut = *state;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  Lib_IntVector_Intrinsics_vec128 *block_state = scrut.block_state;
  KRML_HOST_FREE(k_);
  KRML_ALIGNED_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(state);
}

