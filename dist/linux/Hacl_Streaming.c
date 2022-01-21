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


#include "internal/Hacl_Streaming.h"

#include "internal/Hacl_Hash_SHA2.h"

void Hacl_Streaming_SHA2_update_512(Hacl_Streaming_SHA2_state_sha2_384 *p, u8 *data, u32 len)
{
  Hacl_Streaming_SHA2_state_sha2_384 s = *p;
  u64 total_len = s.total_len;
  u32 sz;
  if (total_len % (u64)(u32)128U == (u64)0U && total_len > (u64)0U)
    sz = (u32)128U;
  else
    sz = (u32)(total_len % (u64)(u32)128U);
  if (len <= (u32)128U - sz)
  {
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
    u64 *block_state1 = s1.block_state;
    u8 *buf = s1.buf;
    u64 total_len1 = s1.total_len;
    u32 sz1;
    if (total_len1 % (u64)(u32)128U == (u64)0U && total_len1 > (u64)0U)
      sz1 = (u32)128U;
    else
      sz1 = (u32)(total_len1 % (u64)(u32)128U);
    {
      u8 *buf2 = buf + sz1;
      u64 total_len2;
      memcpy(buf2, data, len * sizeof (u8));
      total_len2 = total_len1 + (u64)len;
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
  }
  if (sz == (u32)0U)
  {
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
    u64 *block_state1 = s1.block_state;
    u8 *buf = s1.buf;
    u64 total_len1 = s1.total_len;
    u32 sz1;
    if (total_len1 % (u64)(u32)128U == (u64)0U && total_len1 > (u64)0U)
      sz1 = (u32)128U;
    else
      sz1 = (u32)(total_len1 % (u64)(u32)128U);
    {
      u32 ite;
      u32 n_blocks;
      u32 data1_len;
      u32 data2_len;
      u8 *data1;
      u8 *data2;
      u8 *dst;
      if (!(sz1 == (u32)0U))
        Hacl_Hash_SHA2_update_multi_512(block_state1, buf, (u32)1U);
      if ((u64)len % (u64)(u32)128U == (u64)0U && (u64)len > (u64)0U)
        ite = (u32)128U;
      else
        ite = (u32)((u64)len % (u64)(u32)128U);
      n_blocks = (len - ite) / (u32)128U;
      data1_len = n_blocks * (u32)128U;
      data2_len = len - data1_len;
      data1 = data;
      data2 = data + data1_len;
      Hacl_Hash_SHA2_update_multi_512(block_state1, data1, data1_len / (u32)128U);
      dst = buf;
      memcpy(dst, data2, data2_len * sizeof (u8));
      *p
      =
        (
          (Hacl_Streaming_SHA2_state_sha2_384){
            .block_state = block_state1,
            .buf = buf,
            .total_len = total_len1 + (u64)len
          }
        );
      return;
    }
  }
  {
    u32 diff = (u32)128U - sz;
    u8 *data1 = data;
    u8 *data2 = data + diff;
    Hacl_Streaming_SHA2_state_sha2_384 s10 = *p;
    u64 *block_state10 = s10.block_state;
    u8 *buf0 = s10.buf;
    u64 total_len10 = s10.total_len;
    u32 sz10;
    if (total_len10 % (u64)(u32)128U == (u64)0U && total_len10 > (u64)0U)
      sz10 = (u32)128U;
    else
      sz10 = (u32)(total_len10 % (u64)(u32)128U);
    {
      u8 *buf2 = buf0 + sz10;
      u64 total_len2;
      Hacl_Streaming_SHA2_state_sha2_384 s1;
      u64 *block_state1;
      u8 *buf;
      u64 total_len1;
      u32 sz1;
      u32 ite;
      u32 n_blocks;
      u32 data1_len;
      u32 data2_len;
      u8 *data11;
      u8 *data21;
      u8 *dst;
      memcpy(buf2, data1, diff * sizeof (u8));
      total_len2 = total_len10 + (u64)diff;
      *p
      =
        (
          (Hacl_Streaming_SHA2_state_sha2_384){
            .block_state = block_state10,
            .buf = buf0,
            .total_len = total_len2
          }
        );
      s1 = *p;
      block_state1 = s1.block_state;
      buf = s1.buf;
      total_len1 = s1.total_len;
      if (total_len1 % (u64)(u32)128U == (u64)0U && total_len1 > (u64)0U)
        sz1 = (u32)128U;
      else
        sz1 = (u32)(total_len1 % (u64)(u32)128U);
      if (!(sz1 == (u32)0U))
        Hacl_Hash_SHA2_update_multi_512(block_state1, buf, (u32)1U);
      if ((u64)(len - diff) % (u64)(u32)128U == (u64)0U && (u64)(len - diff) > (u64)0U)
        ite = (u32)128U;
      else
        ite = (u32)((u64)(len - diff) % (u64)(u32)128U);
      n_blocks = (len - diff - ite) / (u32)128U;
      data1_len = n_blocks * (u32)128U;
      data2_len = len - diff - data1_len;
      data11 = data2;
      data21 = data2 + data1_len;
      Hacl_Hash_SHA2_update_multi_512(block_state1, data11, data1_len / (u32)128U);
      dst = buf;
      memcpy(dst, data21, data2_len * sizeof (u8));
      *p
      =
        (
          (Hacl_Streaming_SHA2_state_sha2_384){
            .block_state = block_state1,
            .buf = buf,
            .total_len = total_len1 + (u64)(len - diff)
          }
        );
    }
  }
}

void Hacl_Streaming_SHA2_finish_512(Hacl_Streaming_SHA2_state_sha2_384 *p, u8 *dst)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *p;
  u64 *block_state = scrut.block_state;
  u8 *buf_ = scrut.buf;
  u64 total_len = scrut.total_len;
  u32 r;
  if (total_len % (u64)(u32)128U == (u64)0U && total_len > (u64)0U)
    r = (u32)128U;
  else
    r = (u32)(total_len % (u64)(u32)128U);
  {
    u8 *buf_1 = buf_;
    u64 tmp_block_state[8U] = { 0U };
    u32 ite;
    u8 *buf_last;
    u8 *buf_multi;
    u64 prev_len_last;
    memcpy(tmp_block_state, block_state, (u32)8U * sizeof (u64));
    if (r % (u32)128U == (u32)0U && r > (u32)0U)
      ite = (u32)128U;
    else
      ite = r % (u32)128U;
    buf_last = buf_1 + r - ite;
    buf_multi = buf_1;
    Hacl_Hash_SHA2_update_multi_512(tmp_block_state, buf_multi, (u32)0U);
    prev_len_last = total_len - (u64)r;
    Hacl_Hash_SHA2_update_last_512(tmp_block_state, (uint128_t)prev_len_last, buf_last, r);
    Hacl_Hash_Core_SHA2_finish_512(tmp_block_state, dst);
  }
}

