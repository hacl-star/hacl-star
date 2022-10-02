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


#include "Hacl_Streaming_SHA3.h"



Hacl_Streaming_SHA2_state_sha2_384 *Hacl_Streaming_SHA3_create_in_256()
{
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC((uint32_t)136U, sizeof (uint8_t));
  uint64_t *block_state = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
  Hacl_Streaming_SHA2_state_sha2_384 s;
  s.block_state = block_state;
  s.buf = buf;
  s.total_len = (uint64_t)0U;
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_SHA2_state_sha2_384), (uint32_t)1U);
  {
    Hacl_Streaming_SHA2_state_sha2_384
    *p =
      (Hacl_Streaming_SHA2_state_sha2_384 *)KRML_HOST_MALLOC(sizeof (
          Hacl_Streaming_SHA2_state_sha2_384
        ));
    p[0U] = s;
    memset(block_state, 0U, (uint32_t)25U * sizeof (uint64_t));
    return p;
  }
}

void Hacl_Streaming_SHA3_init_256(Hacl_Streaming_SHA2_state_sha2_384 *s)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  memset(block_state, 0U, (uint32_t)25U * sizeof (uint64_t));
  {
    Hacl_Streaming_SHA2_state_sha2_384 lit;
    lit.block_state = block_state;
    lit.buf = buf;
    lit.total_len = (uint64_t)0U;
    s[0U] = lit;
  }
}

void
Hacl_Streaming_SHA3_update_256(
  Hacl_Streaming_SHA2_state_sha2_384 *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_SHA2_state_sha2_384 s = *p;
  uint64_t total_len = s.total_len;
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
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
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
    {
      uint8_t *buf2 = buf + sz1;
      uint64_t total_len2;
      memcpy(buf2, data, len * sizeof (uint8_t));
      total_len2 = total_len1 + (uint64_t)len;
      {
        Hacl_Streaming_SHA2_state_sha2_384 lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len2;
        *p = lit;
        return;
      }
    }
  }
  if (sz == (uint32_t)0U)
  {
    Hacl_Streaming_SHA2_state_sha2_384 s1 = *p;
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
    {
      uint32_t ite;
      uint32_t n_blocks;
      uint32_t data1_len;
      uint32_t data2_len;
      uint8_t *data1;
      uint8_t *data2;
      uint8_t *dst;
      if (!(sz1 == (uint32_t)0U))
      {
        {
          uint32_t sz2 = (uint32_t)136U;
          uint8_t *block = buf + sz2 * (uint32_t)0U;
          Hacl_Impl_SHA3_loadState((uint32_t)136U, block, block_state1);
          Hacl_Impl_SHA3_state_permute(block_state1);
        }
      }
      if ((uint64_t)len % (uint64_t)(uint32_t)136U == (uint64_t)0U && (uint64_t)len > (uint64_t)0U)
      {
        ite = (uint32_t)136U;
      }
      else
      {
        ite = (uint32_t)((uint64_t)len % (uint64_t)(uint32_t)136U);
      }
      n_blocks = (len - ite) / (uint32_t)136U;
      data1_len = n_blocks * (uint32_t)136U;
      data2_len = len - data1_len;
      data1 = data;
      data2 = data + data1_len;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < data1_len / (uint32_t)136U; i++)
        {
          uint32_t sz2 = (uint32_t)136U;
          uint8_t *block = data1 + sz2 * i;
          Hacl_Impl_SHA3_loadState((uint32_t)136U, block, block_state1);
          Hacl_Impl_SHA3_state_permute(block_state1);
        }
      }
      dst = buf;
      memcpy(dst, data2, data2_len * sizeof (uint8_t));
      {
        Hacl_Streaming_SHA2_state_sha2_384 lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len1 + (uint64_t)len;
        *p = lit;
        return;
      }
    }
  }
  {
    uint32_t diff = (uint32_t)136U - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_SHA2_state_sha2_384 s10 = *p;
    uint64_t *block_state10 = s10.block_state;
    uint8_t *buf0 = s10.buf;
    uint64_t total_len10 = s10.total_len;
    uint32_t sz10;
    if (total_len10 % (uint64_t)(uint32_t)136U == (uint64_t)0U && total_len10 > (uint64_t)0U)
    {
      sz10 = (uint32_t)136U;
    }
    else
    {
      sz10 = (uint32_t)(total_len10 % (uint64_t)(uint32_t)136U);
    }
    {
      uint8_t *buf2 = buf0 + sz10;
      uint64_t total_len2;
      memcpy(buf2, data1, diff * sizeof (uint8_t));
      total_len2 = total_len10 + (uint64_t)diff;
      {
        Hacl_Streaming_SHA2_state_sha2_384 lit;
        Hacl_Streaming_SHA2_state_sha2_384 s1;
        uint64_t *block_state1;
        uint8_t *buf;
        uint64_t total_len1;
        uint32_t sz1;
        uint32_t ite;
        uint32_t n_blocks;
        uint32_t data1_len;
        uint32_t data2_len;
        uint8_t *data11;
        uint8_t *data21;
        uint8_t *dst;
        lit.block_state = block_state10;
        lit.buf = buf0;
        lit.total_len = total_len2;
        *p = lit;
        s1 = *p;
        block_state1 = s1.block_state;
        buf = s1.buf;
        total_len1 = s1.total_len;
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
            uint32_t sz2 = (uint32_t)136U;
            uint8_t *block = buf + sz2 * (uint32_t)0U;
            Hacl_Impl_SHA3_loadState((uint32_t)136U, block, block_state1);
            Hacl_Impl_SHA3_state_permute(block_state1);
          }
        }
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
        n_blocks = (len - diff - ite) / (uint32_t)136U;
        data1_len = n_blocks * (uint32_t)136U;
        data2_len = len - diff - data1_len;
        data11 = data2;
        data21 = data2 + data1_len;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < data1_len / (uint32_t)136U; i++)
          {
            uint32_t sz2 = (uint32_t)136U;
            uint8_t *block = data11 + sz2 * i;
            Hacl_Impl_SHA3_loadState((uint32_t)136U, block, block_state1);
            Hacl_Impl_SHA3_state_permute(block_state1);
          }
        }
        dst = buf;
        memcpy(dst, data21, data2_len * sizeof (uint8_t));
        {
          Hacl_Streaming_SHA2_state_sha2_384 lit0;
          lit0.block_state = block_state1;
          lit0.buf = buf;
          lit0.total_len = total_len1 + (uint64_t)(len - diff);
          *p = lit0;
        }
      }
    }
  }
}

void Hacl_Streaming_SHA3_finish_256(Hacl_Streaming_SHA2_state_sha2_384 *p, uint8_t *dst)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *p;
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
  {
    uint8_t *buf_1 = buf_;
    uint64_t tmp_block_state[25U] = { 0U };
    uint32_t ite;
    uint8_t *buf_last;
    uint8_t *buf_multi;
    memcpy(tmp_block_state, block_state, (uint32_t)25U * sizeof (uint64_t));
    if (r % (uint32_t)136U == (uint32_t)0U && r > (uint32_t)0U)
    {
      ite = (uint32_t)136U;
    }
    else
    {
      ite = r % (uint32_t)136U;
    }
    buf_last = buf_1 + r - ite;
    buf_multi = buf_1;
    if (r == (uint32_t)136U)
    {
      Hacl_Impl_SHA3_loadState((uint32_t)136U, buf_last, tmp_block_state);
      Hacl_Impl_SHA3_state_permute(tmp_block_state);
      {
        uint8_t *uu____0 = buf_last + r;
        uint8_t b[136U] = { 0U };
        memcpy(b, uu____0, (uint32_t)0U * sizeof (uint8_t));
        b[0U] = (uint8_t)0x06U;
        Hacl_Impl_SHA3_loadState((uint32_t)136U, b, tmp_block_state);
        {
          uint8_t b1[136U] = { 0U };
          b1[135U] = (uint8_t)0x80U;
          Hacl_Impl_SHA3_loadState((uint32_t)136U, b1, tmp_block_state);
          Hacl_Impl_SHA3_state_permute(tmp_block_state);
          Lib_Memzero0_memzero(b1, (uint32_t)136U * sizeof (b1[0U]));
          Lib_Memzero0_memzero(b, (uint32_t)136U * sizeof (b[0U]));
        }
      }
    }
    else
    {
      uint8_t b[136U] = { 0U };
      memcpy(b, buf_last, r * sizeof (uint8_t));
      b[r] = (uint8_t)0x06U;
      Hacl_Impl_SHA3_loadState((uint32_t)136U, b, tmp_block_state);
      {
        uint8_t b1[136U] = { 0U };
        b1[135U] = (uint8_t)0x80U;
        Hacl_Impl_SHA3_loadState((uint32_t)136U, b1, tmp_block_state);
        Hacl_Impl_SHA3_state_permute(tmp_block_state);
        Lib_Memzero0_memzero(b1, (uint32_t)136U * sizeof (b1[0U]));
        Lib_Memzero0_memzero(b, (uint32_t)136U * sizeof (b[0U]));
      }
    }
    Hacl_Impl_SHA3_squeeze(tmp_block_state, (uint32_t)136U, (uint32_t)32U, dst);
  }
}

void Hacl_Streaming_SHA3_free_256(Hacl_Streaming_SHA2_state_sha2_384 *s)
{
  Hacl_Streaming_SHA2_state_sha2_384 scrut = *s;
  uint8_t *buf = scrut.buf;
  uint64_t *block_state = scrut.block_state;
  KRML_HOST_FREE(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

