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
  Hacl_Streaming_Functor_state_s___uint32_t____ s;
  s.block_state = block_state;
  s.buf = buf;
  s.total_len = (uint64_t)0U;
  KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Functor_state_s___uint32_t____), (uint32_t)1U);
  {
    Hacl_Streaming_Functor_state_s___uint32_t____
    *p = KRML_HOST_MALLOC(sizeof (Hacl_Streaming_Functor_state_s___uint32_t____));
    p[0U] = s;
    Hacl_Hash_Core_SHA2_init_256(block_state);
    return p;
  }
}

void Hacl_Streaming_SHA2_256_init(Hacl_Streaming_Functor_state_s___uint32_t____ *s)
{
  Hacl_Streaming_Functor_state_s___uint32_t____ scrut = *s;
  uint8_t *buf = scrut.buf;
  uint32_t *block_state = scrut.block_state;
  Hacl_Hash_Core_SHA2_init_256(block_state);
  {
    Hacl_Streaming_Functor_state_s___uint32_t____ lit;
    lit.block_state = block_state;
    lit.buf = buf;
    lit.total_len = (uint64_t)0U;
    s[0U] = lit;
  }
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
    uint8_t *buf1;
    if (buf == NULL)
    {
      buf1 = NULL;
    }
    else
    {
      buf1 = buf;
    }
    {
      uint8_t *buf2;
      if (buf == NULL)
      {
        buf2 = NULL;
      }
      else
      {
        buf2 = buf + sz1;
      }
      {
        bool uu____0 = data == NULL;
        uint64_t total_len2;
        if (!(uu____0 || buf2 == NULL))
        {
          memcpy(buf2, data, len * sizeof (data[0U]));
        }
        total_len2 = total_len1 + (uint64_t)len;
        {
          Hacl_Streaming_Functor_state_s___uint32_t____ lit;
          lit.block_state = block_state1;
          lit.buf = buf;
          lit.total_len = total_len2;
          *p = lit;
          return;
        }
      }
    }
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
    uint8_t *data1;
    if (data == NULL)
    {
      data1 = NULL;
    }
    else
    {
      data1 = data;
    }
    {
      uint8_t *data2;
      if (data == NULL)
      {
        data2 = NULL;
      }
      else
      {
        data2 = data + data1_len;
      }
      {
        uint8_t *dst;
        bool uu____1;
        Hacl_Hash_SHA2_update_multi_256(block_state1, data1, data1_len / (uint32_t)64U);
        if (buf == NULL)
        {
          dst = NULL;
        }
        else
        {
          dst = buf;
        }
        uu____1 = data2 == NULL;
        if (!(uu____1 || dst == NULL))
        {
          memcpy(dst, data2, data2_len * sizeof (data2[0U]));
        }
        {
          Hacl_Streaming_Functor_state_s___uint32_t____ lit;
          lit.block_state = block_state1;
          lit.buf = buf;
          lit.total_len = total_len1 + (uint64_t)len;
          *p = lit;
          return;
        }
      }
    }
  }
  {
    uint32_t diff = (uint32_t)64U - sz;
    uint8_t *data1;
    if (data == NULL)
    {
      data1 = NULL;
    }
    else
    {
      data1 = data;
    }
    {
      uint8_t *data2;
      if (data == NULL)
      {
        data2 = NULL;
      }
      else
      {
        data2 = data + diff;
      }
      {
        Hacl_Streaming_Functor_state_s___uint32_t____ s10 = *p;
        uint32_t *block_state10 = s10.block_state;
        uint8_t *buf_1 = s10.buf;
        uint64_t total_len10 = s10.total_len;
        uint64_t x = total_len10 % (uint64_t)(uint32_t)64U;
        uint32_t sz1 = (uint32_t)x;
        uint32_t diff1 = (uint32_t)64U - sz1;
        uint8_t *buf0;
        if (buf_1 == NULL)
        {
          buf0 = NULL;
        }
        else
        {
          buf0 = buf_1;
        }
        {
          uint8_t *buf1;
          if (buf0 == NULL)
          {
            buf1 = NULL;
          }
          else
          {
            buf1 = buf0;
          }
          {
            uint8_t *buf2;
            if (buf0 == NULL)
            {
              buf2 = NULL;
            }
            else
            {
              buf2 = buf0 + sz1;
            }
            {
              bool uu____2 = data1 == NULL;
              if (!(uu____2 || buf2 == NULL))
              {
                memcpy(buf2, data1, diff1 * sizeof (data1[0U]));
              }
              Hacl_Hash_SHA2_update_multi_256(block_state10, buf0, (uint32_t)1U);
              {
                Hacl_Streaming_Functor_state_s___uint32_t____ lit;
                Hacl_Streaming_Functor_state_s___uint32_t____ s1;
                uint32_t *block_state1;
                uint8_t *buf;
                uint64_t total_len1;
                uint32_t n_blocks;
                uint32_t data1_len;
                uint32_t data2_len;
                uint8_t *data11;
                uint8_t *data21;
                uint8_t *dst;
                bool uu____3;
                lit.block_state = block_state10;
                lit.buf = buf_1;
                lit.total_len = total_len10 + (uint64_t)diff;
                *p = lit;
                s1 = *p;
                block_state1 = s1.block_state;
                buf = s1.buf;
                total_len1 = s1.total_len;
                n_blocks = (len - diff) / (uint32_t)64U;
                data1_len = n_blocks * (uint32_t)64U;
                data2_len = len - diff - data1_len;
                if (data2 == NULL)
                {
                  data11 = NULL;
                }
                else
                {
                  data11 = data2;
                }
                if (data2 == NULL)
                {
                  data21 = NULL;
                }
                else
                {
                  data21 = data2 + data1_len;
                }
                Hacl_Hash_SHA2_update_multi_256(block_state1, data11, data1_len / (uint32_t)64U);
                if (buf == NULL)
                {
                  dst = NULL;
                }
                else
                {
                  dst = buf;
                }
                uu____3 = data21 == NULL;
                if (!(uu____3 || dst == NULL))
                {
                  memcpy(dst, data21, data2_len * sizeof (data21[0U]));
                }
                {
                  Hacl_Streaming_Functor_state_s___uint32_t____ lit0;
                  lit0.block_state = block_state1;
                  lit0.buf = buf;
                  lit0.total_len = total_len1 + (uint64_t)(len - diff);
                  *p = lit0;
                }
              }
            }
          }
        }
      }
    }
  }
}

void
Hacl_Streaming_SHA2_256_finish(Hacl_Streaming_Functor_state_s___uint32_t____ *p, uint8_t *dst)
{
  Hacl_Streaming_Functor_state_s___uint32_t____ scrut = *p;
  uint32_t *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint8_t *buf_1;
  if (buf_ == NULL)
  {
    buf_1 = NULL;
  }
  else
  {
    buf_1 = buf_;
  }
  {
    uint32_t tmp_block_state[8U] = { 0U };
    bool uu____0 = block_state == NULL;
    uint64_t last_len;
    uint64_t prev_len;
    uint32_t last_len1;
    if (!(uu____0 || tmp_block_state == NULL))
    {
      memcpy(tmp_block_state, block_state, (uint32_t)8U * sizeof (block_state[0U]));
    }
    last_len = total_len % (uint64_t)64U;
    prev_len = total_len - last_len;
    last_len1 = (uint32_t)last_len;
    Hacl_Hash_SHA2_update_last_256(tmp_block_state, prev_len, buf_1, last_len1);
    Hacl_Hash_Core_SHA2_finish_256(tmp_block_state, dst);
  }
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

