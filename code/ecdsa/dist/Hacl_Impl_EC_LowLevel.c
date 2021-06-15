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


#include "Hacl_Impl_EC_LowLevel.h"

void
Hacl_Impl_EC_LowLevel_mul(Spec_ECC_Curves_curve c, uint64_t *f, uint64_t *r, uint64_t *out)
{
  uint32_t len;
  switch (c)
  {
    case Spec_ECC_Curves_P256:
      {
        len = (uint32_t)4U;
        break;
      }
    case Spec_ECC_Curves_P384:
      {
        len = (uint32_t)6U;
        break;
      }
    default:
      {
        len = (uint32_t)4U;
      }
  }
  uint32_t resLen = len + len;
  memset(out, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t bj = r[i0];
    uint64_t *res_j = out + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < len / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t a_i = f[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i0);
      uint64_t a_i0 = f[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c1, res_i1);
      uint64_t a_i1 = f[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c1, res_i2);
      uint64_t a_i2 = f[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c1, res_i);
    }
    for (uint32_t i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
    {
      uint64_t a_i = f[i];
      uint64_t *res_i = res_j + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c1, res_i);
    }
    uint64_t r1 = c1;
    out[len + i0] = r1;
  }
}

