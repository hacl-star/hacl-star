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


#include "Hacl_Streaming_SHA2_256.h"

typedef struct Hacl_Streaming_Functor_state_s___uint32_t_____s
{
  uint32_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s___uint32_t____;

Hacl_Streaming_Functor_state_s___uint32_t____ *Hacl_Streaming_SHA2_256_create_in()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  uint32_t *block_state = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  Hacl_Streaming_Functor_state_s___uint32_t____
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s___uint32_t____), (uint32_t)1U);
  Hacl_Streaming_Functor_state_s___uint32_t____
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s___uint32_t____));
  p[0U] = s;
  Hacl_Hash_Core_SHA2_init_256(block_state);
  return p;
}

void Hacl_Streaming_SHA2_256_init(Hacl_Streaming_Functor_state_s___uint32_t____ *s)
{
  Hacl_Streaming_Functor_state_s___uint32_t____ scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  Hacl_Hash_Core_SHA2_init_256(block_state);
  s[0U] =
    (
      (Hacl_Streaming_Functor_state_s___uint32_t____){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

void
Hacl_Streaming_SHA2_256_update(
  Hacl_Streaming_Functor_state_s___uint32_t____ *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Functor_state_s___uint32_t____ s = *p;
  uint64_t total_len = s.total_len;
  uint64_t x0 = total_len % (uint64_t)(uint32_t)64U;
  uint32_t sz = (uint32_t)x0;
  if (len < (uint32_t)64U - sz)
  {
    Hacl_Streaming_Functor_state_s___uint32_t____ s1 = *p;
    uint32_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint64_t x = total_len1 % (uint64_t)(uint32_t)64U;
    uint32_t sz1 = (uint32_t)x;
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (data[0U]));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s___uint32_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_Functor_state_s___uint32_t____ s1 = *p;
    uint32_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t n_blocks = len / (uint32_t)64U;
    uint32_t data1_len = n_blocks * (uint32_t)64U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    Hacl_Hash_SHA2_update_multi_256(block_state1, data1, data1_len / (uint32_t)64U);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (data2[0U]));
    *p
    =
      (
        (Hacl_Streaming_Functor_state_s___uint32_t____){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)64U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_Functor_state_s___uint32_t____ s1 = *p;
  uint32_t *block_state10 = s1.block_state;
  uint8_t *buf_1 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  uint64_t x = total_len10 % (uint64_t)(uint32_t)64U;
  uint32_t sz1 = (uint32_t)x;
  uint32_t diff1 = (uint32_t)64U - sz1;
  uint8_t *buf0 = buf_1;
  uint8_t *buf2 = buf0 + sz1;
  memcpy(buf2, data1, diff1 * sizeof (data1[0U]));
  Hacl_Hash_SHA2_update_multi_256(block_state10, buf0, (uint32_t)1U);
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s___uint32_t____){
        .block_state = block_state10,
        .buf = buf_1,
        .total_len = total_len10 + (uint64_t)diff
      }
    );
  Hacl_Streaming_Functor_state_s___uint32_t____ s10 = *p;
  uint32_t *block_state1 = s10.block_state;
  uint8_t *buf = s10.buf;
  uint64_t total_len1 = s10.total_len;
  uint32_t n_blocks = (len - diff) / (uint32_t)64U;
  uint32_t data1_len = n_blocks * (uint32_t)64U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  Hacl_Hash_SHA2_update_multi_256(block_state1, data11, data1_len / (uint32_t)64U);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (data21[0U]));
  *p
  =
    (
      (Hacl_Streaming_Functor_state_s___uint32_t____){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

void
Hacl_Streaming_SHA2_256_finish(Hacl_Streaming_Functor_state_s___uint32_t____ *p, uint8_t *dst)
{
  Hacl_Streaming_Functor_state_s___uint32_t____ scrut = *p;
  uint32_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1 = buf_;
  uint32_t tmp_block_state[8U] = { 0U };
  memcpy(tmp_block_state, block_state, (uint32_t)8U * sizeof (block_state[0U]));
  uint64_t last_len = total_len % (uint64_t)64U;
  uint64_t prev_len = total_len - last_len;
  uint32_t last_len1 = (uint32_t)last_len;
  Hacl_Hash_SHA2_update_last_256(tmp_block_state, prev_len, buf_1, last_len1);
  Hacl_Hash_Core_SHA2_finish_256(tmp_block_state, dst);
}

void Hacl_Streaming_SHA2_256_free(Hacl_Streaming_Functor_state_s___uint32_t____ *s)
{
  Hacl_Streaming_Functor_state_s___uint32_t____ scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

