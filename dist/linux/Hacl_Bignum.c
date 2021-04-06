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


#include "Hacl_Bignum.h"

inline void Hacl_Bignum_Convert_bn_from_bytes_le_uint64(u32 len, u8 *b, u64 *res)
{
  u32 bnLen = (len - (u32)1U) / (u32)8U + (u32)1U;
  u32 tmpLen = (u32)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (u8), tmpLen);
  {
    u8 tmp[tmpLen];
    memset(tmp, 0U, tmpLen * sizeof (u8));
    memcpy(tmp, b, len * sizeof (u8));
    {
      u32 i;
      for (i = (u32)0U; i < (len - (u32)1U) / (u32)8U + (u32)1U; i++)
      {
        u64 *os = res;
        u8 *bj = tmp + i * (u32)8U;
        u64 u = load64_le(bj);
        u64 r = u;
        u64 x = r;
        os[i] = x;
      }
    }
  }
}

