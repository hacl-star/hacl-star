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

/*
  State allocation function when there is no key
*/
Hacl_Streaming_Blake2b_256_blake2b_256_state
*Hacl_Streaming_Blake2b_256_blake2b_256_no_key_create_in()
{
  KRML_CHECK_SIZE(sizeof (uint8_t),
    Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256));
  {
    uint8_t
    *buf =
      (uint8_t *)KRML_HOST_CALLOC(Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256),
        sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec256
    *wv =
      (Lib_IntVector_Intrinsics_vec256 *)KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256)
        * (uint32_t)4U);
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)4U; ++_i)
        wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    }
    {
      Lib_IntVector_Intrinsics_vec256
      *b =
        (Lib_IntVector_Intrinsics_vec256 *)KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256)
          * (uint32_t)4U);
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U; ++_i)
          b[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      }
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_block_state lit;
        Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state;
        lit.fst = wv;
        lit.snd = b;
        block_state = lit;
        {
          Hacl_Streaming_Blake2b_256_blake2b_256_state s;
          s.block_state = block_state;
          s.buf = buf;
          s.total_len = (uint64_t)0U;
          KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Blake2b_256_blake2b_256_state), (uint32_t)1U);
          {
            Hacl_Streaming_Blake2b_256_blake2b_256_state
            *p =
              (Hacl_Streaming_Blake2b_256_blake2b_256_state *)KRML_HOST_MALLOC(sizeof (
                  Hacl_Streaming_Blake2b_256_blake2b_256_state
                ));
            p[0U] = s;
            Hacl_Blake2b_256_blake2b_init(block_state.fst,
              block_state.snd,
              (uint32_t)0U,
              NULL,
              (uint32_t)64U);
            return p;
          }
        }
      }
    }
  }
}

/*
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
  Hacl_Blake2b_256_blake2b_init(block_state.fst,
    block_state.snd,
    (uint32_t)0U,
    NULL,
    (uint32_t)64U);
  {
    Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
    lit.block_state = block_state;
    lit.buf = buf;
    lit.total_len = (uint64_t)0U;
    s[0U] = lit;
  }
}

/*
  Update function when there is no key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_no_key_update(
  Hacl_Streaming_Blake2b_256_blake2b_256_state *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if
  (
    total_len
    %
      (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
        Hacl_Impl_Blake2_Core_M256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    sz = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
  }
  else
  {
    sz =
      (uint32_t)(total_len
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256));
  }
  if
  (
    len
    <= Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256) - sz
  )
  {
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if
    (
      total_len1
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256)
      == (uint64_t)0U
      && total_len1 > (uint64_t)0U
    )
    {
      sz1 = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256));
    }
    {
      uint8_t *buf2 = buf + sz1;
      uint64_t total_len2;
      memcpy(buf2, data, len * sizeof (uint8_t));
      total_len2 = total_len1 + (uint64_t)len;
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
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
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if
    (
      total_len1
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256)
      == (uint64_t)0U
      && total_len1 > (uint64_t)0U
    )
    {
      sz1 = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256));
    }
    {
      uint32_t ite0;
      uint32_t n_blocks;
      uint32_t data1_len;
      uint32_t data2_len;
      uint8_t *data1;
      uint8_t *data2;
      uint32_t nb0;
      uint64_t ite1;
      uint8_t *dst;
      if (!(sz1 == (uint32_t)0U))
      {
        uint64_t prevlen = total_len1 - (uint64_t)sz1;
        uint32_t
        nb =
          Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256)
          / (uint32_t)128U;
        uint64_t ite;
        if ((uint32_t)0U == (uint32_t)0U)
        {
          ite = prevlen;
        }
        else
        {
          ite = prevlen + (uint64_t)(uint32_t)128U;
        }
        Hacl_Blake2b_256_blake2b_update_multi(Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256),
          block_state1.fst,
          block_state1.snd,
          FStar_UInt128_uint64_to_uint128(ite),
          buf,
          nb);
      }
      if
      (
        (uint64_t)len
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256)
        == (uint64_t)0U
        && (uint64_t)len > (uint64_t)0U
      )
      {
        ite0 =
          Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256);
      }
      else
      {
        ite0 =
          (uint32_t)((uint64_t)len
          %
            (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256));
      }
      n_blocks =
        (len - ite0)
        / Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
      data1_len =
        n_blocks
        * Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
      data2_len = len - data1_len;
      data1 = data;
      data2 = data + data1_len;
      nb0 = data1_len / (uint32_t)128U;
      if ((uint32_t)0U == (uint32_t)0U)
      {
        ite1 = total_len1;
      }
      else
      {
        ite1 = total_len1 + (uint64_t)(uint32_t)128U;
      }
      Hacl_Blake2b_256_blake2b_update_multi(data1_len,
        block_state1.fst,
        block_state1.snd,
        FStar_UInt128_uint64_to_uint128(ite1),
        data1,
        nb0);
      dst = buf;
      memcpy(dst, data2, data2_len * sizeof (uint8_t));
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len1 + (uint64_t)len;
        *p = lit;
        return;
      }
    }
  }
  {
    uint32_t
    diff =
      Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
        Hacl_Impl_Blake2_Core_M256)
      - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_Blake2b_256_blake2b_256_state s10 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state10 = s10.block_state;
    uint8_t *buf0 = s10.buf;
    uint64_t total_len10 = s10.total_len;
    uint32_t sz10;
    if
    (
      total_len10
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256)
      == (uint64_t)0U
      && total_len10 > (uint64_t)0U
    )
    {
      sz10 = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
    }
    else
    {
      sz10 =
        (uint32_t)(total_len10
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256));
    }
    {
      uint8_t *buf2 = buf0 + sz10;
      uint64_t total_len2;
      memcpy(buf2, data1, diff * sizeof (uint8_t));
      total_len2 = total_len10 + (uint64_t)diff;
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
        Hacl_Streaming_Blake2b_256_blake2b_256_state s1;
        Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1;
        uint8_t *buf;
        uint64_t total_len1;
        uint32_t sz1;
        uint32_t ite0;
        uint32_t n_blocks;
        uint32_t data1_len;
        uint32_t data2_len;
        uint8_t *data11;
        uint8_t *data21;
        uint32_t nb0;
        uint64_t ite1;
        uint8_t *dst;
        lit.block_state = block_state10;
        lit.buf = buf0;
        lit.total_len = total_len2;
        *p = lit;
        s1 = *p;
        block_state1 = s1.block_state;
        buf = s1.buf;
        total_len1 = s1.total_len;
        if
        (
          total_len1
          %
            (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256)
          == (uint64_t)0U
          && total_len1 > (uint64_t)0U
        )
        {
          sz1 =
            Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256);
        }
        else
        {
          sz1 =
            (uint32_t)(total_len1
            %
              (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256));
        }
        if (!(sz1 == (uint32_t)0U))
        {
          uint64_t prevlen = total_len1 - (uint64_t)sz1;
          uint32_t
          nb =
            Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256)
            / (uint32_t)128U;
          uint64_t ite;
          if ((uint32_t)0U == (uint32_t)0U)
          {
            ite = prevlen;
          }
          else
          {
            ite = prevlen + (uint64_t)(uint32_t)128U;
          }
          Hacl_Blake2b_256_blake2b_update_multi(Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256),
            block_state1.fst,
            block_state1.snd,
            FStar_UInt128_uint64_to_uint128(ite),
            buf,
            nb);
        }
        if
        (
          (uint64_t)(len - diff)
          %
            (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256)
          == (uint64_t)0U
          && (uint64_t)(len - diff) > (uint64_t)0U
        )
        {
          ite0 =
            Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256);
        }
        else
        {
          ite0 =
            (uint32_t)((uint64_t)(len - diff)
            %
              (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256));
        }
        n_blocks =
          (len - diff - ite0)
          / Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
        data1_len =
          n_blocks
          * Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
        data2_len = len - diff - data1_len;
        data11 = data2;
        data21 = data2 + data1_len;
        nb0 = data1_len / (uint32_t)128U;
        if ((uint32_t)0U == (uint32_t)0U)
        {
          ite1 = total_len1;
        }
        else
        {
          ite1 = total_len1 + (uint64_t)(uint32_t)128U;
        }
        Hacl_Blake2b_256_blake2b_update_multi(data1_len,
          block_state1.fst,
          block_state1.snd,
          FStar_UInt128_uint64_to_uint128(ite1),
          data11,
          nb0);
        dst = buf;
        memcpy(dst, data21, data2_len * sizeof (uint8_t));
        {
          Hacl_Streaming_Blake2b_256_blake2b_256_state lit0;
          lit0.block_state = block_state1;
          lit0.buf = buf;
          lit0.total_len = total_len1 + (uint64_t)(len - diff);
          *p = lit0;
        }
      }
    }
  }
}

/*
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
  if
  (
    total_len
    %
      (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
        Hacl_Impl_Blake2_Core_M256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
  }
  else
  {
    r =
      (uint32_t)(total_len
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256));
  }
  {
    uint8_t *buf_1 = buf_;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
    {
      Lib_IntVector_Intrinsics_vec256 wv[(uint32_t)4U * (uint32_t)1U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
      {
        Lib_IntVector_Intrinsics_vec256 b[(uint32_t)4U * (uint32_t)1U];
        {
          uint32_t _i;
          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
            b[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        }
        {
          Hacl_Streaming_Blake2b_256_blake2b_256_block_state lit;
          Hacl_Streaming_Blake2b_256_blake2b_256_block_state tmp_block_state;
          Lib_IntVector_Intrinsics_vec256 *src_b;
          Lib_IntVector_Intrinsics_vec256 *dst_b;
          uint64_t prev_len;
          uint32_t ite0;
          uint8_t *buf_last;
          uint8_t *buf_multi;
          uint32_t ite1;
          uint32_t nb;
          uint32_t ite2;
          uint64_t ite3;
          uint32_t ite4;
          uint64_t prev_len_last;
          uint32_t ite5;
          uint64_t ite6;
          uint32_t ite;
          lit.fst = wv;
          lit.snd = b;
          tmp_block_state = lit;
          src_b = block_state.snd;
          dst_b = tmp_block_state.snd;
          memcpy(dst_b, src_b, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec256));
          prev_len = total_len - (uint64_t)r;
          if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite0 = (uint32_t)128U;
          }
          else
          {
            ite0 = r % (uint32_t)128U;
          }
          buf_last = buf_1 + r - ite0;
          buf_multi = buf_1;
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite1 = (uint32_t)0U;
          }
          else
          {
            uint32_t ite7;
            if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
            {
              ite7 = (uint32_t)128U;
            }
            else
            {
              ite7 = r % (uint32_t)128U;
            }
            ite1 = r - ite7;
          }
          nb = ite1 / (uint32_t)128U;
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite2 = (uint32_t)0U;
          }
          else
          {
            uint32_t ite7;
            if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
            {
              ite7 = (uint32_t)128U;
            }
            else
            {
              ite7 = r % (uint32_t)128U;
            }
            ite2 = r - ite7;
          }
          if ((uint32_t)0U == (uint32_t)0U)
          {
            ite3 = prev_len;
          }
          else
          {
            ite3 = prev_len + (uint64_t)(uint32_t)128U;
          }
          Hacl_Blake2b_256_blake2b_update_multi(ite2,
            tmp_block_state.fst,
            tmp_block_state.snd,
            FStar_UInt128_uint64_to_uint128(ite3),
            buf_multi,
            nb);
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite4 = r;
          }
          else if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite4 = (uint32_t)128U;
          }
          else
          {
            ite4 = r % (uint32_t)128U;
          }
          prev_len_last = total_len - (uint64_t)ite4;
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite5 = r;
          }
          else if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite5 = (uint32_t)128U;
          }
          else
          {
            ite5 = r % (uint32_t)128U;
          }
          if ((uint32_t)0U == (uint32_t)0U)
          {
            ite6 = prev_len_last;
          }
          else
          {
            ite6 = prev_len_last + (uint64_t)(uint32_t)128U;
          }
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite = r;
          }
          else if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite = (uint32_t)128U;
          }
          else
          {
            ite = r % (uint32_t)128U;
          }
          Hacl_Blake2b_256_blake2b_update_last(ite5,
            tmp_block_state.fst,
            tmp_block_state.snd,
            FStar_UInt128_uint64_to_uint128(ite6),
            ite,
            buf_last);
          Hacl_Blake2b_256_blake2b_finish((uint32_t)64U, dst, tmp_block_state.snd);
        }
      }
    }
  }
}

/*
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
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

/*
  State allocation function when using a (potentially null) key
*/
Hacl_Streaming_Blake2b_256_blake2b_256_state
*Hacl_Streaming_Blake2b_256_blake2b_256_with_key_create_in(uint32_t key_size, uint8_t *k)
{
  KRML_CHECK_SIZE(sizeof (uint8_t),
    Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256));
  {
    uint8_t
    *buf =
      (uint8_t *)KRML_HOST_CALLOC(Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256),
        sizeof (uint8_t));
    Lib_IntVector_Intrinsics_vec256
    *wv =
      (Lib_IntVector_Intrinsics_vec256 *)KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256)
        * (uint32_t)4U);
    {
      uint32_t _i;
      for (_i = 0U; _i < (uint32_t)4U; ++_i)
        wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
    }
    {
      Lib_IntVector_Intrinsics_vec256
      *b =
        (Lib_IntVector_Intrinsics_vec256 *)KRML_HOST_MALLOC(sizeof (Lib_IntVector_Intrinsics_vec256)
          * (uint32_t)4U);
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U; ++_i)
          b[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      }
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_block_state lit;
        Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state;
        lit.fst = wv;
        lit.snd = b;
        block_state = lit;
        {
          Hacl_Streaming_Blake2b_256_blake2b_256_state s;
          s.block_state = block_state;
          s.buf = buf;
          s.total_len = (uint64_t)0U;
          KRML_CHECK_SIZE(sizeof (Hacl_Streaming_Blake2b_256_blake2b_256_state), (uint32_t)1U);
          {
            Hacl_Streaming_Blake2b_256_blake2b_256_state
            *p =
              (Hacl_Streaming_Blake2b_256_blake2b_256_state *)KRML_HOST_MALLOC(sizeof (
                  Hacl_Streaming_Blake2b_256_blake2b_256_state
                ));
            p[0U] = s;
            Hacl_Blake2b_256_blake2b_init(block_state.fst,
              block_state.snd,
              key_size,
              k,
              (uint32_t)64U);
            return p;
          }
        }
      }
    }
  }
}

/*
  (Re-)initialization function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_init(
  uint32_t key_size,
  uint8_t *k,
  Hacl_Streaming_Blake2b_256_blake2b_256_state *s
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state scrut = *s;
  uint8_t *buf = scrut.buf;
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = scrut.block_state;
  Hacl_Blake2b_256_blake2b_init(block_state.fst, block_state.snd, key_size, k, (uint32_t)64U);
  {
    Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
    lit.block_state = block_state;
    lit.buf = buf;
    lit.total_len = (uint64_t)0U;
    s[0U] = lit;
  }
}

/*
  Update function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_update(
  uint32_t key_size,
  Hacl_Streaming_Blake2b_256_blake2b_256_state *p,
  uint8_t *data,
  uint32_t len
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state s = *p;
  uint64_t total_len = s.total_len;
  uint32_t sz;
  if
  (
    total_len
    %
      (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
        Hacl_Impl_Blake2_Core_M256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    sz = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
  }
  else
  {
    sz =
      (uint32_t)(total_len
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256));
  }
  if
  (
    len
    <= Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256) - sz
  )
  {
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if
    (
      total_len1
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256)
      == (uint64_t)0U
      && total_len1 > (uint64_t)0U
    )
    {
      sz1 = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256));
    }
    {
      uint8_t *buf2 = buf + sz1;
      uint64_t total_len2;
      memcpy(buf2, data, len * sizeof (uint8_t));
      total_len2 = total_len1 + (uint64_t)len;
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
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
    Hacl_Streaming_Blake2b_256_blake2b_256_state s1 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1 = s1.block_state;
    uint8_t *buf = s1.buf;
    uint64_t total_len1 = s1.total_len;
    uint32_t sz1;
    if
    (
      total_len1
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256)
      == (uint64_t)0U
      && total_len1 > (uint64_t)0U
    )
    {
      sz1 = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
    }
    else
    {
      sz1 =
        (uint32_t)(total_len1
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256));
    }
    {
      uint32_t ite0;
      uint32_t n_blocks;
      uint32_t data1_len;
      uint32_t data2_len;
      uint8_t *data1;
      uint8_t *data2;
      uint32_t nb0;
      uint64_t ite1;
      uint8_t *dst;
      if (!(sz1 == (uint32_t)0U))
      {
        uint64_t prevlen = total_len1 - (uint64_t)sz1;
        uint32_t
        nb =
          Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256)
          / (uint32_t)128U;
        uint64_t ite;
        if (key_size == (uint32_t)0U)
        {
          ite = prevlen;
        }
        else
        {
          ite = prevlen + (uint64_t)(uint32_t)128U;
        }
        Hacl_Blake2b_256_blake2b_update_multi(Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256),
          block_state1.fst,
          block_state1.snd,
          FStar_UInt128_uint64_to_uint128(ite),
          buf,
          nb);
      }
      if
      (
        (uint64_t)len
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256)
        == (uint64_t)0U
        && (uint64_t)len > (uint64_t)0U
      )
      {
        ite0 =
          Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256);
      }
      else
      {
        ite0 =
          (uint32_t)((uint64_t)len
          %
            (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256));
      }
      n_blocks =
        (len - ite0)
        / Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
      data1_len =
        n_blocks
        * Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
      data2_len = len - data1_len;
      data1 = data;
      data2 = data + data1_len;
      nb0 = data1_len / (uint32_t)128U;
      if (key_size == (uint32_t)0U)
      {
        ite1 = total_len1;
      }
      else
      {
        ite1 = total_len1 + (uint64_t)(uint32_t)128U;
      }
      Hacl_Blake2b_256_blake2b_update_multi(data1_len,
        block_state1.fst,
        block_state1.snd,
        FStar_UInt128_uint64_to_uint128(ite1),
        data1,
        nb0);
      dst = buf;
      memcpy(dst, data2, data2_len * sizeof (uint8_t));
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
        lit.block_state = block_state1;
        lit.buf = buf;
        lit.total_len = total_len1 + (uint64_t)len;
        *p = lit;
        return;
      }
    }
  }
  {
    uint32_t
    diff =
      Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
        Hacl_Impl_Blake2_Core_M256)
      - sz;
    uint8_t *data1 = data;
    uint8_t *data2 = data + diff;
    Hacl_Streaming_Blake2b_256_blake2b_256_state s10 = *p;
    Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state10 = s10.block_state;
    uint8_t *buf0 = s10.buf;
    uint64_t total_len10 = s10.total_len;
    uint32_t sz10;
    if
    (
      total_len10
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256)
      == (uint64_t)0U
      && total_len10 > (uint64_t)0U
    )
    {
      sz10 = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
    }
    else
    {
      sz10 =
        (uint32_t)(total_len10
        %
          (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
            Hacl_Impl_Blake2_Core_M256));
    }
    {
      uint8_t *buf2 = buf0 + sz10;
      uint64_t total_len2;
      memcpy(buf2, data1, diff * sizeof (uint8_t));
      total_len2 = total_len10 + (uint64_t)diff;
      {
        Hacl_Streaming_Blake2b_256_blake2b_256_state lit;
        Hacl_Streaming_Blake2b_256_blake2b_256_state s1;
        Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state1;
        uint8_t *buf;
        uint64_t total_len1;
        uint32_t sz1;
        uint32_t ite0;
        uint32_t n_blocks;
        uint32_t data1_len;
        uint32_t data2_len;
        uint8_t *data11;
        uint8_t *data21;
        uint32_t nb0;
        uint64_t ite1;
        uint8_t *dst;
        lit.block_state = block_state10;
        lit.buf = buf0;
        lit.total_len = total_len2;
        *p = lit;
        s1 = *p;
        block_state1 = s1.block_state;
        buf = s1.buf;
        total_len1 = s1.total_len;
        if
        (
          total_len1
          %
            (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256)
          == (uint64_t)0U
          && total_len1 > (uint64_t)0U
        )
        {
          sz1 =
            Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256);
        }
        else
        {
          sz1 =
            (uint32_t)(total_len1
            %
              (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256));
        }
        if (!(sz1 == (uint32_t)0U))
        {
          uint64_t prevlen = total_len1 - (uint64_t)sz1;
          uint32_t
          nb =
            Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256)
            / (uint32_t)128U;
          uint64_t ite;
          if (key_size == (uint32_t)0U)
          {
            ite = prevlen;
          }
          else
          {
            ite = prevlen + (uint64_t)(uint32_t)128U;
          }
          Hacl_Blake2b_256_blake2b_update_multi(Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256),
            block_state1.fst,
            block_state1.snd,
            FStar_UInt128_uint64_to_uint128(ite),
            buf,
            nb);
        }
        if
        (
          (uint64_t)(len - diff)
          %
            (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256)
          == (uint64_t)0U
          && (uint64_t)(len - diff) > (uint64_t)0U
        )
        {
          ite0 =
            Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
              Hacl_Impl_Blake2_Core_M256);
        }
        else
        {
          ite0 =
            (uint32_t)((uint64_t)(len - diff)
            %
              (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256));
        }
        n_blocks =
          (len - diff - ite0)
          / Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
        data1_len =
          n_blocks
          * Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
        data2_len = len - diff - data1_len;
        data11 = data2;
        data21 = data2 + data1_len;
        nb0 = data1_len / (uint32_t)128U;
        if (key_size == (uint32_t)0U)
        {
          ite1 = total_len1;
        }
        else
        {
          ite1 = total_len1 + (uint64_t)(uint32_t)128U;
        }
        Hacl_Blake2b_256_blake2b_update_multi(data1_len,
          block_state1.fst,
          block_state1.snd,
          FStar_UInt128_uint64_to_uint128(ite1),
          data11,
          nb0);
        dst = buf;
        memcpy(dst, data21, data2_len * sizeof (uint8_t));
        {
          Hacl_Streaming_Blake2b_256_blake2b_256_state lit0;
          lit0.block_state = block_state1;
          lit0.buf = buf;
          lit0.total_len = total_len1 + (uint64_t)(len - diff);
          *p = lit0;
        }
      }
    }
  }
}

/*
  Finish function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_finish(
  uint32_t key_size,
  Hacl_Streaming_Blake2b_256_blake2b_256_state *p,
  uint8_t *dst
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state scrut = *p;
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    %
      (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
        Hacl_Impl_Blake2_Core_M256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B, Hacl_Impl_Blake2_Core_M256);
  }
  else
  {
    r =
      (uint32_t)(total_len
      %
        (uint64_t)Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
          Hacl_Impl_Blake2_Core_M256));
  }
  {
    uint8_t *buf_1 = buf_;
    KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
    {
      Lib_IntVector_Intrinsics_vec256 wv[(uint32_t)4U * (uint32_t)1U];
      {
        uint32_t _i;
        for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
          wv[_i] = Lib_IntVector_Intrinsics_vec256_zero;
      }
      KRML_CHECK_SIZE(sizeof (Lib_IntVector_Intrinsics_vec256), (uint32_t)4U * (uint32_t)1U);
      {
        Lib_IntVector_Intrinsics_vec256 b[(uint32_t)4U * (uint32_t)1U];
        {
          uint32_t _i;
          for (_i = 0U; _i < (uint32_t)4U * (uint32_t)1U; ++_i)
            b[_i] = Lib_IntVector_Intrinsics_vec256_zero;
        }
        {
          Hacl_Streaming_Blake2b_256_blake2b_256_block_state lit;
          Hacl_Streaming_Blake2b_256_blake2b_256_block_state tmp_block_state;
          Lib_IntVector_Intrinsics_vec256 *src_b;
          Lib_IntVector_Intrinsics_vec256 *dst_b;
          uint64_t prev_len;
          uint32_t ite0;
          uint8_t *buf_last;
          uint8_t *buf_multi;
          uint32_t ite1;
          uint32_t nb;
          uint32_t ite2;
          uint64_t ite3;
          uint32_t ite4;
          uint64_t prev_len_last;
          uint32_t ite5;
          uint64_t ite6;
          uint32_t ite;
          lit.fst = wv;
          lit.snd = b;
          tmp_block_state = lit;
          src_b = block_state.snd;
          dst_b = tmp_block_state.snd;
          memcpy(dst_b, src_b, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec256));
          prev_len = total_len - (uint64_t)r;
          if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite0 = (uint32_t)128U;
          }
          else
          {
            ite0 = r % (uint32_t)128U;
          }
          buf_last = buf_1 + r - ite0;
          buf_multi = buf_1;
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite1 = (uint32_t)0U;
          }
          else
          {
            uint32_t ite7;
            if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
            {
              ite7 = (uint32_t)128U;
            }
            else
            {
              ite7 = r % (uint32_t)128U;
            }
            ite1 = r - ite7;
          }
          nb = ite1 / (uint32_t)128U;
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite2 = (uint32_t)0U;
          }
          else
          {
            uint32_t ite7;
            if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
            {
              ite7 = (uint32_t)128U;
            }
            else
            {
              ite7 = r % (uint32_t)128U;
            }
            ite2 = r - ite7;
          }
          if (key_size == (uint32_t)0U)
          {
            ite3 = prev_len;
          }
          else
          {
            ite3 = prev_len + (uint64_t)(uint32_t)128U;
          }
          Hacl_Blake2b_256_blake2b_update_multi(ite2,
            tmp_block_state.fst,
            tmp_block_state.snd,
            FStar_UInt128_uint64_to_uint128(ite3),
            buf_multi,
            nb);
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite4 = r;
          }
          else if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite4 = (uint32_t)128U;
          }
          else
          {
            ite4 = r % (uint32_t)128U;
          }
          prev_len_last = total_len - (uint64_t)ite4;
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite5 = r;
          }
          else if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite5 = (uint32_t)128U;
          }
          else
          {
            ite5 = r % (uint32_t)128U;
          }
          if (key_size == (uint32_t)0U)
          {
            ite6 = prev_len_last;
          }
          else
          {
            ite6 = prev_len_last + (uint64_t)(uint32_t)128U;
          }
          if
          (
            (uint32_t)128U
            ==
              Hacl_Streaming_Blake2_blocks_state_len(Spec_Blake2_Blake2B,
                Hacl_Impl_Blake2_Core_M256)
          )
          {
            ite = r;
          }
          else if (r % (uint32_t)128U == (uint32_t)0U && r > (uint32_t)0U)
          {
            ite = (uint32_t)128U;
          }
          else
          {
            ite = r % (uint32_t)128U;
          }
          Hacl_Blake2b_256_blake2b_update_last(ite5,
            tmp_block_state.fst,
            tmp_block_state.snd,
            FStar_UInt128_uint64_to_uint128(ite6),
            ite,
            buf_last);
          Hacl_Blake2b_256_blake2b_finish((uint32_t)64U, dst, tmp_block_state.snd);
        }
      }
    }
  }
}

/*
  Free state function when using a (potentially null) key
*/
void
Hacl_Streaming_Blake2b_256_blake2b_256_with_key_free(
  uint32_t key_size,
  Hacl_Streaming_Blake2b_256_blake2b_256_state *s
)
{
  Hacl_Streaming_Blake2b_256_blake2b_256_state scrut = *s;
  uint8_t *buf = scrut.buf;
  Hacl_Streaming_Blake2b_256_blake2b_256_block_state block_state = scrut.block_state;
  Lib_IntVector_Intrinsics_vec256 *wv = block_state.fst;
  Lib_IntVector_Intrinsics_vec256 *b = block_state.snd;
  KRML_HOST_FREE(wv);
  KRML_HOST_FREE(b);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(s);
}

