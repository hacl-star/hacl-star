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


#include "Hacl_Streaming_Poly1305_32.h"



Hacl_Streaming_Poly1305_32_poly1305_32_state *Hacl_Streaming_Poly1305_32_create_in(uint8_t *k)
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
  uint64_t *r1 = KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
  uint64_t *block_state = r1;
  uint8_t *k_ = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  memcpy(k_, k, (uint32_t)32U * sizeof (uint8_t));
  uint8_t *k_0 = k_;
  Hacl_Streaming_Poly1305_32_poly1305_32_state
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U, .p_key = k_0 };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Poly1305_32_poly1305_32_state), (uint32_t)1U);
  Hacl_Streaming_Poly1305_32_poly1305_32_state
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Poly1305_32_poly1305_32_state));
  p[0U] = s;
  Hacl_Poly1305_32_poly1305_init(block_state, k);
  return p;
}

void
Hacl_Streaming_Poly1305_32_init(uint8_t *k, Hacl_Streaming_Poly1305_32_poly1305_32_state *s)
{
  Hacl_Streaming_Poly1305_32_poly1305_32_state scrut = *s;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  Hacl_Poly1305_32_poly1305_init(block_state, k);
  memcpy(k_, k, (uint32_t)32U * sizeof (uint8_t));
  uint8_t *k_1 = k_;
  s[0U] =
    (
      (Hacl_Streaming_Poly1305_32_poly1305_32_state){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U,
        .p_key = k_1
      }
    );
}

void
Hacl_Streaming_Poly1305_32_update(
  Hacl_Streaming_Poly1305_32_poly1305_32_state *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Poly1305_32_poly1305_32_state s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)16U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)16U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)16U);
  }
  if (len <= (uint32_t)16U - sz)
  {
    Hacl_Streaming_Poly1305_32_poly1305_32_state s1 = *p;
    uint64_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)16U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)16U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)16U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Poly1305_32_poly1305_32_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2,
          .p_key = k_1
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Poly1305_32_poly1305_32_state s1 = *p;
    uint64_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)16U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)16U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)16U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      Hacl_Poly1305_32_poly1305_update(block_state1, (uint32_t)16U, buf);
    }
    uint32_t ite;
    if ((uint64_t)len % (uint64_t)(uint32_t)16U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite = (uint32_t)16U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)16U);
    }
    uint32_t n_blocks = (len - ite) / (uint32_t)16U;
    uint32_t data1_len = n_blocks * (uint32_t)16U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    Hacl_Poly1305_32_poly1305_update(block_state1, data1_len, data1);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_Poly1305_32_poly1305_32_state){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len,
          .p_key = k_1
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)16U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Poly1305_32_poly1305_32_state s1 = *p;
  uint64_t *block_state10 = s1.block_state;
  uint8_t *buf0 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  uint8_t *k_1 = s1.p_key;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)16U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)16U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)16U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_Poly1305_32_poly1305_32_state){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2,
        .p_key = k_1
      }
    );
  Hacl_Streaming_Poly1305_32_poly1305_32_state s10 = *p;
  uint64_t *block_state1 = s10.block_state;
  uint8_t *buf = s10.buf;
  uint64_t total_len1 = s10.total_len;
  uint8_t *k_10 = s10.p_key;
  uint32_t sz1;
  if (total_len1 % (uint64_t)(uint32_t)16U == (uint64_t)0U && total_len1 > (uint64_t)0U)
  {
    sz1 = (uint32_t)16U;
  }
  else
  {
    sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)16U);
  }
  if (!(sz1 == (uint32_t)0U))
  {
    Hacl_Poly1305_32_poly1305_update(block_state1, (uint32_t)16U, buf);
  }
  uint32_t ite;
  if
  (
    (uint64_t)(len - diff)
    % (uint64_t)(uint32_t)16U
    == (uint64_t)0U
    && (uint64_t)(len - diff) > (uint64_t)0U
  )
  {
    ite = (uint32_t)16U;
  }
  else
  {
    ite = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)16U);
  }
  uint32_t n_blocks = (len - diff - ite) / (uint32_t)16U;
  uint32_t data1_len = n_blocks * (uint32_t)16U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  Hacl_Poly1305_32_poly1305_update(block_state1, data1_len, data11);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_Poly1305_32_poly1305_32_state){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff),
        .p_key = k_10
      }
    );
}

void
Hacl_Streaming_Poly1305_32_finish(
  Hacl_Streaming_Poly1305_32_poly1305_32_state *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Poly1305_32_poly1305_32_state scrut = *p;
  uint64_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *k_ = scrut.p_key;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)16U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)16U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)16U);
  }
  uint8_t *buf_1 = buf_;
  uint64_t r1[25U] = { 0U };
  uint64_t *tmp_block_state = r1;
  memcpy(tmp_block_state, block_state, (uint32_t)25U * sizeof (uint64_t));
  uint32_t ite;
  if (r % (uint32_t)16U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = (uint32_t)16U;
  }
  else
  {
    ite = r % (uint32_t)16U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  Hacl_Poly1305_32_poly1305_update(tmp_block_state, (uint32_t)0U, buf_multi);
  Hacl_Poly1305_32_poly1305_update(tmp_block_state, r, buf_last);
  uint64_t tmp[25U] = { 0U };
  memcpy(tmp, tmp_block_state, (uint32_t)25U * sizeof (uint64_t));
  Hacl_Poly1305_32_poly1305_finish(dst, k_, tmp);
}

void Hacl_Streaming_Poly1305_32_free(Hacl_Streaming_Poly1305_32_poly1305_32_state *s)
{
  Hacl_Streaming_Poly1305_32_poly1305_32_state scrut = *s;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  KRML_HOST_FREE(k_);
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

