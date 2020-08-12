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

typedef struct Hacl_Streaming_Functor_state_s___uint64_t___uint8_t__s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
  uint8_t *p_key;
}
Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_;

Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_
*Hacl_Streaming_Poly1305_32_create_in(uint8_t *k1)
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint8_t));
  uint64_t *r1 = KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
  uint64_t *block_state = r1;
  uint8_t *k_ = KRML_HOST_CALLOC((uint32_t)32U, sizeof (uint8_t));
  uint8_t *k_0;
  memcpy(k_, k1, (uint32_t)32U * sizeof (uint8_t));
  k_0 = k_;
  {
    Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ s;
    s.block_state = block_state;
    s.buf = buf;
    s.total_len = (uint64_t)0U;
    s.p_key = k_0;
    KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_), (uint32_t)1U);
    {
      Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_
      *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_));
      p[0U] = s;
      Hacl_Poly1305_32_poly1305_init(block_state, k1);
      return p;
    }
  }
}

void
Hacl_Streaming_Poly1305_32_init(
  uint8_t *k1,
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ *s
)
{
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ scrut = *s;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  uint8_t *k_1;
  Hacl_Poly1305_32_poly1305_init(block_state, k1);
  memcpy(k_, k1, (uint32_t)32U * sizeof (uint8_t));
  k_1 = k_;
  {
    Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ lit;
    lit.block_state = block_state;
    lit.buf = buf;
    lit.total_len = (uint64_t)0U;
    lit.p_key = k_1;
    s[0U] = lit;
  }
}

void
Hacl_Streaming_Poly1305_32_update(
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ s = *p;
  uint64_t total_len = s.total_len;
  uint64_t x0 = total_len % (uint64_t)(uint32_t)16U;
  uint32_t sz = (uint32_t)x0;
  if (len < (uint32_t)16U - sz)
  {
    Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ s1 = *p;
    uint64_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint64_t x = total_len1 % (uint64_t)(uint32_t)16U;
    uint32_t sz1 = (uint32_t)x;
    uint8_t *buf2 = buf + sz1;
    uint64_t total_len2;
    memcpy(buf2, data, len * sizeof (uint8_t));
    total_len2 = total_len1 + (uint64_t)len;
    {
      Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ lit;
      lit.block_state = block_state1;
      lit.buf = buf;
      lit.total_len = total_len2;
      lit.p_key = k_1;
      *p = lit;
      return;
    }
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ s1 = *p;
    uint64_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint8_t *k_1 = s1.p_key;
    uint32_t n_blocks = len / (uint32_t)16U;
    uint32_t data1_len = n_blocks * (uint32_t)16U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    uint8_t *dst;
    Hacl_Poly1305_32_poly1305_update(block_state1, data1_len, data1);
    dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    {
      Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ lit;
      lit.block_state = block_state1;
      lit.buf = buf;
      lit.total_len = total_len1 + (uint64_t)len;
      lit.p_key = k_1;
      *p = lit;
      return;
    }
  }
  {
    uint32_t diff = (uint32_t)16U - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ s10 = *p;
    uint64_t *block_state10 = s10.block_state;
    uint8_t *buf_1 = s10.buf;
    uint64_t total_len10 = s10.total_len;
    uint8_t *k_1 = s10.p_key;
    uint64_t x = total_len10 % (uint64_t)(uint32_t)16U;
    uint32_t sz1 = (uint32_t)x;
    uint32_t diff1 = (uint32_t)16U - sz1;
    uint8_t *buf0 = buf_1;
    uint8_t *buf2 = buf0 + sz1;
    memcpy(buf2, data1, diff1 * sizeof (uint8_t));
    Hacl_Poly1305_32_poly1305_update(block_state10, (uint32_t)16U, buf0);
    {
      Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ lit;
      Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ s1;
      uint64_t *block_state1;
      uint8_t *buf;
      uint64_t total_len1;
      uint8_t *k_10;
      uint32_t n_blocks;
      uint32_t data1_len;
      uint32_t data2_len;
      uint8_t *data11;
      uint8_t *data21;
      uint8_t *dst;
      lit.block_state = block_state10;
      lit.buf = buf_1;
      lit.total_len = total_len10 + (uint64_t)diff;
      lit.p_key = k_1;
      *p = lit;
      s1 = *p;
      block_state1 = s1.block_state;
      buf = s1.buf;
      total_len1 = s1.total_len;
      k_10 = s1.p_key;
      n_blocks = (len - diff) / (uint32_t)16U;
      data1_len = n_blocks * (uint32_t)16U;
      data2_len = len - diff - data1_len;
      data11 = data2;
      data21 = data2 + data1_len;
      Hacl_Poly1305_32_poly1305_update(block_state1, data1_len, data11);
      dst = buf;
      memcpy(dst, data21, data2_len * sizeof (uint8_t));
      {
        Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ lit0;
        lit0.block_state = block_state1;
        lit0.buf = buf;
        lit0.total_len = total_len1 + (uint64_t)(len - diff);
        lit0.p_key = k_10;
        *p = lit0;
      }
    }
  }
}

void
Hacl_Streaming_Poly1305_32_finish(
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ scrut = *p;
  uint64_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf_1 = buf_;
  uint64_t r[25U] = { 0U };
  uint64_t *tmp_block_state = r;
  uint32_t len;
  memcpy(tmp_block_state, block_state, (uint32_t)25U * sizeof (uint64_t));
  len = (uint32_t)(total_len % (uint64_t)16U);
  if (len != (uint32_t)0U)
  {
    Hacl_Poly1305_32_poly1305_update(tmp_block_state, len, buf_1);
  }
  {
    uint64_t tmp[25U] = { 0U };
    memcpy(tmp, tmp_block_state, (uint32_t)25U * sizeof (uint64_t));
    Hacl_Poly1305_32_poly1305_finish(dst, k_, tmp);
  }
}

void Hacl_Streaming_Poly1305_32_free(Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ *s)
{
  Hacl_Streaming_Functor_state_s___uint64_t___uint8_t_ scrut = *s;
  uint8_t *k_ = scrut.p_key;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  KRML_HOST_FREE(k_);
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

