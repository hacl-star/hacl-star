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


#include "Hacl_Streaming_SHA2.h"

#include "internal/Hacl_Hash_SHA2.h"

Hacl_Streaming_SHA2_state_sha2_224 *Hacl_Streaming_SHA2_create_in_224()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  uint32_t *block_state = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  Hacl_Streaming_SHA2_state_sha2_224
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_SHA2_state_sha2_224), (uint32_t)1U);
  Hacl_Streaming_SHA2_state_sha2_224
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_SHA2_state_sha2_224));
  p[0U] = s;
  Hacl_Hash_Core_SHA2_init_224(block_state);
  return p;
}

void Hacl_Streaming_SHA2_init_224(Hacl_Streaming_SHA2_state_sha2_224 *s)
{
  Hacl_Streaming_SHA2_state_sha2_224 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  Hacl_Hash_Core_SHA2_init_224(block_state);
  s[0U] =
    (
      (Hacl_Streaming_SHA2_state_sha2_224){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

void
Hacl_Streaming_SHA2_update_224(
  Hacl_Streaming_SHA2_state_sha2_224 *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_SHA2_state_sha2_224 s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)64U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  if (len <= (uint32_t)64U - sz)
  {
    Hacl_Streaming_SHA2_state_sha2_224 s1 = *p;
    uint32_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_SHA2_state_sha2_224){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_SHA2_state_sha2_224 s1 = *p;
    uint32_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      Hacl_Hash_SHA2_update_multi_224(block_state1, buf, (uint32_t)1U);
    }
    uint32_t ite;
    if ((uint64_t)len % (uint64_t)(uint32_t)64U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite = (uint32_t)64U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)64U);
    }
    uint32_t n_blocks = (len - ite) / (uint32_t)64U;
    uint32_t data1_len = n_blocks * (uint32_t)64U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    Hacl_Hash_SHA2_update_multi_224(block_state1, data1, data1_len / (uint32_t)64U);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_SHA2_state_sha2_224){
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
  Hacl_Streaming_SHA2_state_sha2_224 s1 = *p;
  uint32_t *block_state10 = s1.block_state;
  uint8_t *buf0 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)64U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)64U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_SHA2_state_sha2_224){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_SHA2_state_sha2_224 s10 = *p;
  uint32_t *block_state1 = s10.block_state;
  uint8_t *buf = s10.buf;
  uint64_t total_len1 = s10.total_len;
  uint32_t sz1;
  if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
  {
    sz1 = (uint32_t)64U;
  }
  else
  {
    sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
  }
  if (!(sz1 == (uint32_t)0U))
  {
    Hacl_Hash_SHA2_update_multi_224(block_state1, buf, (uint32_t)1U);
  }
  uint32_t ite;
  if
  (
    (uint64_t)(len - diff)
    % (uint64_t)(uint32_t)64U
    == (uint64_t)0U
    && (uint64_t)(len - diff) > (uint64_t)0U
  )
  {
    ite = (uint32_t)64U;
  }
  else
  {
    ite = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)64U);
  }
  uint32_t n_blocks = (len - diff - ite) / (uint32_t)64U;
  uint32_t data1_len = n_blocks * (uint32_t)64U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  Hacl_Hash_SHA2_update_multi_224(block_state1, data11, data1_len / (uint32_t)64U);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_SHA2_state_sha2_224){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

void Hacl_Streaming_SHA2_finish_224(Hacl_Streaming_SHA2_state_sha2_224 *p, uint8_t *dst)
{
  Hacl_Streaming_SHA2_state_sha2_224 scrut = *p;
  uint32_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)64U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  uint8_t *buf_1 = buf_;
  uint32_t tmp_block_state[8U] = { 0U };
  memcpy(tmp_block_state, block_state, (uint32_t)8U * sizeof (uint32_t));
  uint32_t ite;
  if (r % (uint32_t)64U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = (uint32_t)64U;
  }
  else
  {
    ite = r % (uint32_t)64U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  Hacl_Hash_SHA2_update_multi_224(tmp_block_state, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  Hacl_Hash_SHA2_update_last_224(tmp_block_state, prev_len_last, buf_last, r);
  Hacl_Hash_Core_SHA2_finish_224(tmp_block_state, dst);
}

void Hacl_Streaming_SHA2_free_224(Hacl_Streaming_SHA2_state_sha2_224 *s)
{
  Hacl_Streaming_SHA2_state_sha2_224 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

Hacl_Streaming_SHA2_state_sha2_224 *Hacl_Streaming_SHA2_create_in_256()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)64U, sizeof (uint8_t));
  uint32_t *block_state = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
  Hacl_Streaming_SHA2_state_sha2_224
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_SHA2_state_sha2_224), (uint32_t)1U);
  Hacl_Streaming_SHA2_state_sha2_224
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_SHA2_state_sha2_224));
  p[0U] = s;
  Hacl_Hash_Core_SHA2_init_256(block_state);
  return p;
}

void Hacl_Streaming_SHA2_init_256(Hacl_Streaming_SHA2_state_sha2_224 *s)
{
  Hacl_Streaming_SHA2_state_sha2_224 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  Hacl_Hash_Core_SHA2_init_256(block_state);
  s[0U] =
    (
      (Hacl_Streaming_SHA2_state_sha2_224){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

void
Hacl_Streaming_SHA2_update_256(
  Hacl_Streaming_SHA2_state_sha2_224 *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_SHA2_state_sha2_224 s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    sz = (uint32_t)64U;
  }
  else
  {
    sz = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  if (len <= (uint32_t)64U - sz)
  {
    Hacl_Streaming_SHA2_state_sha2_224 s1 = *p;
    uint32_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    uint8_t *buf2 = buf + sz1;
    memcpy(buf2, data, len * sizeof (uint8_t));
    uint64_t total_len2 = total_len1 + (uint64_t)len;
    *p
    =
      (
        (Hacl_Streaming_SHA2_state_sha2_224){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_SHA2_state_sha2_224 s1 = *p;
    uint32_t *block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
    {
      sz1 = (uint32_t)64U;
    }
    else
    {
      sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
    }
    if (!(sz1 == (uint32_t)0U))
    {
      Hacl_Hash_SHA2_update_multi_256(block_state1, buf, (uint32_t)1U);
    }
    uint32_t ite;
    if ((uint64_t)len % (uint64_t)(uint32_t)64U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
    {
      ite = (uint32_t)64U;
    }
    else
    {
      ite = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)64U);
    }
    uint32_t n_blocks = (len - ite) / (uint32_t)64U;
    uint32_t data1_len = n_blocks * (uint32_t)64U;
    uint32_t data2_len = len - data1_len;
    uint8_t *data1 = data;
    uint8_t *data2 = data + data1_len;
    Hacl_Hash_SHA2_update_multi_256(block_state1, data1, data1_len / (uint32_t)64U);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_SHA2_state_sha2_224){
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
  Hacl_Streaming_SHA2_state_sha2_224 s1 = *p;
  uint32_t *block_state10 = s1.block_state;
  uint8_t *buf0 = s1.buf;
  uint64_t total_len10 = s1.total_len;
  uint32_t sz10;
  if (total_len10 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len10 > (uint64_t)0U)
  {
    sz10 = (uint32_t)64U;
  }
  else
  {
    sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)64U);
  }
  uint8_t *buf2 = buf0 + sz10;
  memcpy(buf2, data1, diff * sizeof (uint8_t));
  uint64_t total_len2 = total_len10 + (uint64_t)diff;
  *p
  =
    (
      (Hacl_Streaming_SHA2_state_sha2_224){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_SHA2_state_sha2_224 s10 = *p;
  uint32_t *block_state1 = s10.block_state;
  uint8_t *buf = s10.buf;
  uint64_t total_len1 = s10.total_len;
  uint32_t sz1;
  if (total_len1 % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len1 > (uint64_t)0U)
  {
    sz1 = (uint32_t)64U;
  }
  else
  {
    sz1 = (uint32_t)(total_len1 % (uint64_t)(uint32_t)64U);
  }
  if (!(sz1 == (uint32_t)0U))
  {
    Hacl_Hash_SHA2_update_multi_256(block_state1, buf, (uint32_t)1U);
  }
  uint32_t ite;
  if
  (
    (uint64_t)(len - diff)
    % (uint64_t)(uint32_t)64U
    == (uint64_t)0U
    && (uint64_t)(len - diff) > (uint64_t)0U
  )
  {
    ite = (uint32_t)64U;
  }
  else
  {
    ite = (uint32_t)((uint64_t)(len - diff) % (uint64_t)(uint32_t)64U);
  }
  uint32_t n_blocks = (len - diff - ite) / (uint32_t)64U;
  uint32_t data1_len = n_blocks * (uint32_t)64U;
  uint32_t data2_len = len - diff - data1_len;
  uint8_t *data11 = data2;
  uint8_t *data21 = data2 + data1_len;
  Hacl_Hash_SHA2_update_multi_256(block_state1, data11, data1_len / (uint32_t)64U);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_SHA2_state_sha2_224){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

void Hacl_Streaming_SHA2_finish_256(Hacl_Streaming_SHA2_state_sha2_224 *p, uint8_t *dst)
{
  Hacl_Streaming_SHA2_state_sha2_224 scrut = *p;
  uint32_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if (total_len % (uint64_t)(uint32_t)64U == (uint64_t)0U && total_len > (uint64_t)0U)
  {
    r = (uint32_t)64U;
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)(uint32_t)64U);
  }
  uint8_t *buf_1 = buf_;
  uint32_t tmp_block_state[8U] = { 0U };
  memcpy(tmp_block_state, block_state, (uint32_t)8U * sizeof (uint32_t));
  uint32_t ite;
  if (r % (uint32_t)64U == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = (uint32_t)64U;
  }
  else
  {
    ite = r % (uint32_t)64U;
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  Hacl_Hash_SHA2_update_multi_256(tmp_block_state, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  Hacl_Hash_SHA2_update_last_256(tmp_block_state, prev_len_last, buf_last, r);
  Hacl_Hash_Core_SHA2_finish_256(tmp_block_state, dst);
}

void Hacl_Streaming_SHA2_free_256(Hacl_Streaming_SHA2_state_sha2_224 *s)
{
  Hacl_Streaming_SHA2_state_sha2_224 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

Hacl_Streaming_SHA2_state_sha2_384 *Hacl_Streaming_SHA2_create_in_384()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  uint64_t *block_state = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
  Hacl_Streaming_SHA2_state_sha2_384
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_SHA2_state_sha2_384), (uint32_t)1U);
  Hacl_Streaming_SHA2_state_sha2_384
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_SHA2_state_sha2_384));
  p[0U] = s;
  Hacl_Hash_Core_SHA2_init_384(block_state);
  return p;
}

void Hacl_Streaming_SHA2_init_384(Hacl_Streaming_SHA2_state_sha2_384 *s)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  Hacl_Hash_Core_SHA2_init_384(block_state);
  s[0U] =
    (
      (Hacl_Streaming_SHA2_state_sha2_384){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

void
Hacl_Streaming_SHA2_update_384(
  Hacl_Streaming_SHA2_state_sha2_384 *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_SHA2_state_sha2_384 s = *p;
  uint64_t total_len = s.total_len;
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
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
    uint64_t *block_state1 = s1.block_state;
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
        (Hacl_Streaming_SHA2_state_sha2_384){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
    uint64_t *block_state1 = s1.block_state;
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
      Hacl_Hash_SHA2_update_multi_384(block_state1, buf, (uint32_t)1U);
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
    Hacl_Hash_SHA2_update_multi_384(block_state1, data1, data1_len / (uint32_t)128U);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_SHA2_state_sha2_384){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)128U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
  uint64_t *block_state10 = s1.block_state;
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
      (Hacl_Streaming_SHA2_state_sha2_384){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_SHA2_state_sha2_384 s10 = *p;
  uint64_t *block_state1 = s10.block_state;
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
    Hacl_Hash_SHA2_update_multi_384(block_state1, buf, (uint32_t)1U);
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
  Hacl_Hash_SHA2_update_multi_384(block_state1, data11, data1_len / (uint32_t)128U);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_SHA2_state_sha2_384){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

void Hacl_Streaming_SHA2_finish_384(Hacl_Streaming_SHA2_state_sha2_384 *p, uint8_t *dst)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *p;
  uint64_t *block_state = scrut.block_state;
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
  uint64_t tmp_block_state[8U] = { 0U };
  memcpy(tmp_block_state, block_state, (uint32_t)8U * sizeof (uint64_t));
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
  Hacl_Hash_SHA2_update_multi_384(tmp_block_state, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  Hacl_Hash_SHA2_update_last_384(tmp_block_state,
    FStar_UInt128_uint64_to_uint128(prev_len_last),
    buf_last,
    r);
  Hacl_Hash_Core_SHA2_finish_384(tmp_block_state, dst);
}

void Hacl_Streaming_SHA2_free_384(Hacl_Streaming_SHA2_state_sha2_384 *s)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

Hacl_Streaming_SHA2_state_sha2_384 *Hacl_Streaming_SHA2_create_in_512()
{
  uint8_t *buf = KRML_HOST_CALLOC((uint32_t)128U, sizeof (uint8_t));
  uint64_t *block_state = KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
  Hacl_Streaming_SHA2_state_sha2_384
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)0U };
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_SHA2_state_sha2_384), (uint32_t)1U);
  Hacl_Streaming_SHA2_state_sha2_384
  *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_SHA2_state_sha2_384));
  p[0U] = s;
  Hacl_Hash_Core_SHA2_init_512(block_state);
  return p;
}

void Hacl_Streaming_SHA2_init_512(Hacl_Streaming_SHA2_state_sha2_384 *s)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  Hacl_Hash_Core_SHA2_init_512(block_state);
  s[0U] =
    (
      (Hacl_Streaming_SHA2_state_sha2_384){
        .block_state = block_state,
        .buf = buf,
        .total_len = (uint64_t)0U
      }
    );
}

void
Hacl_Streaming_SHA2_update_512(
  Hacl_Streaming_SHA2_state_sha2_384 *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_SHA2_state_sha2_384 s = *p;
  uint64_t total_len = s.total_len;
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
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
    uint64_t *block_state1 = s1.block_state;
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
        (Hacl_Streaming_SHA2_state_sha2_384){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len2
        }
      );
    return;
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
    uint64_t *block_state1 = s1.block_state;
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
      Hacl_Hash_SHA2_update_multi_512(block_state1, buf, (uint32_t)1U);
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
    Hacl_Hash_SHA2_update_multi_512(block_state1, data1, data1_len / (uint32_t)128U);
    uint8_t *dst = buf;
    memcpy(dst, data2, data2_len * sizeof (uint8_t));
    *p
    =
      (
        (Hacl_Streaming_SHA2_state_sha2_384){
          .block_state = block_state1,
          .buf = buf,
          .total_len = total_len1 + (uint64_t)len
        }
      );
    return;
  }
  uint32_t diff = (uint32_t)128U - sz;
  uint8_t *data1 = data;
  uint8_t *data2 = data + diff;
  Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
  uint64_t *block_state10 = s1.block_state;
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
      (Hacl_Streaming_SHA2_state_sha2_384){
        .block_state = block_state10,
        .buf = buf0,
        .total_len = total_len2
      }
    );
  Hacl_Streaming_SHA2_state_sha2_384 s10 = *p;
  uint64_t *block_state1 = s10.block_state;
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
    Hacl_Hash_SHA2_update_multi_512(block_state1, buf, (uint32_t)1U);
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
  Hacl_Hash_SHA2_update_multi_512(block_state1, data11, data1_len / (uint32_t)128U);
  uint8_t *dst = buf;
  memcpy(dst, data21, data2_len * sizeof (uint8_t));
  *p
  =
    (
      (Hacl_Streaming_SHA2_state_sha2_384){
        .block_state = block_state1,
        .buf = buf,
        .total_len = total_len1 + (uint64_t)(len - diff)
      }
    );
}

void Hacl_Streaming_SHA2_finish_512(Hacl_Streaming_SHA2_state_sha2_384 *p, uint8_t *dst)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *p;
  uint64_t *block_state = scrut.block_state;
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
  uint64_t tmp_block_state[8U] = { 0U };
  memcpy(tmp_block_state, block_state, (uint32_t)8U * sizeof (uint64_t));
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
  Hacl_Hash_SHA2_update_multi_512(tmp_block_state, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  Hacl_Hash_SHA2_update_last_512(tmp_block_state,
    FStar_UInt128_uint64_to_uint128(prev_len_last),
    buf_last,
    r);
  Hacl_Hash_Core_SHA2_finish_512(tmp_block_state, dst);
}

void Hacl_Streaming_SHA2_free_512(Hacl_Streaming_SHA2_state_sha2_384 *s)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

