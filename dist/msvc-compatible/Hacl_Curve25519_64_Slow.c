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


#include "Hacl_Curve25519_64_Slow.h"

#include "internal/Hacl_Kremlib.h"
#include "internal/Hacl_Bignum.h"

static inline uint64_t add1_(uint64_t *out, uint64_t *f1, uint64_t f2)
{
  uint64_t c0 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, f1[0U], f2, out);
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = f1 + (uint32_t)1U;
    uint64_t *res1 = out + (uint32_t)1U;
    uint64_t c = c0;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c1 = c;
    return c1;
  }
  return c0;
}

static inline void fadd_(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = f1[(uint32_t)4U * i];
    uint64_t t20 = f2[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = f1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = f2[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = f1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = f2[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = f1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = f2[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = f1[i];
    uint64_t t2 = f2[i];
    uint64_t *res_i = out + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t
  c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, out[0U], c00 * (uint64_t)38U, out);
  uint64_t c1;
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = out + (uint32_t)1U;
    uint64_t *res1 = out + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c01;
  }
  out[0U] = out[0U] + c1 * (uint64_t)38U;
}

static inline void fsub_(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = f1[(uint32_t)4U * i];
    uint64_t t20 = f2[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = f1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = f2[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = f1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = f2[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = f1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = f2[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = f1[i];
    uint64_t t2 = f2[i];
    uint64_t *res_i = out + i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  uint64_t
  c01 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, out[0U], c00 * (uint64_t)38U, out);
  uint64_t c1;
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = out + (uint32_t)1U;
    uint64_t *res1 = out + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c01;
  }
  out[0U] = out[0U] - c1 * (uint64_t)38U;
}

static inline void fmul_(uint64_t *out, uint64_t *f1, uint64_t *f2, uint64_t *tmp)
{
  uint64_t *tmp0 = tmp;
  memset(tmp0, 0U, (uint32_t)8U * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t bj = f2[i0];
    uint64_t *res_j = tmp0 + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t a_i = f1[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      uint64_t a_i0 = f1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
      uint64_t a_i1 = f1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
      uint64_t a_i2 = f1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    }
    for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
    {
      uint64_t a_i = f1[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
    }
    uint64_t r = c;
    tmp0[(uint32_t)4U + i0] = r;
  }
  uint64_t *uu____0 = tmp0 + (uint32_t)4U;
  uint64_t *uu____1 = tmp0;
  uint64_t *res_j = uu____1;
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t a_i = uu____0[(uint32_t)4U * i];
    uint64_t *res_i0 = res_j + (uint32_t)4U * i;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)38U, c0, res_i0);
    uint64_t a_i0 = uu____0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (uint64_t)38U, c0, res_i1);
    uint64_t a_i1 = uu____0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (uint64_t)38U, c0, res_i2);
    uint64_t a_i2 = uu____0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (uint64_t)38U, c0, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t a_i = uu____0[i];
    uint64_t *res_i = res_j + i;
    c0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)38U, c0, res_i);
  }
  uint64_t r = c0;
  uint64_t c00 = r;
  uint64_t *uu____2 = tmp0;
  uint64_t
  c01 =
    Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U,
      uu____2[0U],
      c00 * (uint64_t)38U,
      out);
  uint64_t c1;
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = uu____2 + (uint32_t)1U;
    uint64_t *res1 = out + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c01;
  }
  out[0U] = out[0U] + c1 * (uint64_t)38U;
}

static inline void fmul2_(uint64_t *out, uint64_t *f1, uint64_t *f2, uint64_t *tmp)
{
  uint64_t *out1 = out;
  uint64_t *out2 = out + (uint32_t)4U;
  uint64_t *f11 = f1;
  uint64_t *f12 = f1 + (uint32_t)4U;
  uint64_t *f21 = f2;
  uint64_t *f22 = f2 + (uint32_t)4U;
  fmul_(out1, f11, f21, tmp);
  fmul_(out2, f12, f22, tmp);
}

static inline void fmul1_(uint64_t *out, uint64_t *f1, uint64_t f2)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t a_i = f1[(uint32_t)4U * i];
    uint64_t *res_i0 = out + (uint32_t)4U * i;
    c0 = Hacl_Bignum_Base_mul_wide_add_u64(a_i, f2, c0, res_i0);
    uint64_t a_i0 = f1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = out + (uint32_t)4U * i + (uint32_t)1U;
    c0 = Hacl_Bignum_Base_mul_wide_add_u64(a_i0, f2, c0, res_i1);
    uint64_t a_i1 = f1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = out + (uint32_t)4U * i + (uint32_t)2U;
    c0 = Hacl_Bignum_Base_mul_wide_add_u64(a_i1, f2, c0, res_i2);
    uint64_t a_i2 = f1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = out + (uint32_t)4U * i + (uint32_t)3U;
    c0 = Hacl_Bignum_Base_mul_wide_add_u64(a_i2, f2, c0, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t a_i = f1[i];
    uint64_t *res_i = out + i;
    c0 = Hacl_Bignum_Base_mul_wide_add_u64(a_i, f2, c0, res_i);
  }
  uint64_t c00 = c0;
  uint64_t
  c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, out[0U], c00 * (uint64_t)38U, out);
  uint64_t c1;
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = out + (uint32_t)1U;
    uint64_t *res1 = out + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c01;
  }
  out[0U] = out[0U] + c1 * (uint64_t)38U;
}

static inline void fsqr_(uint64_t *out, uint64_t *f1, uint64_t *tmp)
{
  memset(tmp, 0U, (uint32_t)8U * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t *ab = f1;
    uint64_t a_j = f1[i0];
    uint64_t *res_j = tmp + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
    {
      uint64_t a_i = ab[(uint32_t)4U * i];
      uint64_t *res_i0 = res_j + (uint32_t)4U * i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
      uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
      uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
      uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
    }
    for (uint32_t i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
    {
      uint64_t a_i = ab[i];
      uint64_t *res_i = res_j + i;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
    }
    uint64_t r = c;
    tmp[i0 + i0] = r;
  }
  uint64_t c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, tmp, tmp, tmp);
  uint64_t tmp1[8U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    FStar_UInt128_uint128 res = FStar_UInt128_mul_wide(f1[i], f1[i]);
    uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
    uint64_t lo = FStar_UInt128_uint128_to_uint64(res);
    tmp1[(uint32_t)2U * i] = lo;
    tmp1[(uint32_t)2U * i + (uint32_t)1U] = hi;
  }
  uint64_t c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, tmp, tmp1, tmp);
  uint64_t *uu____0 = tmp + (uint32_t)4U;
  uint64_t *uu____1 = tmp;
  uint64_t *res_j = uu____1;
  uint64_t c2 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint64_t a_i = uu____0[(uint32_t)4U * i];
    uint64_t *res_i0 = res_j + (uint32_t)4U * i;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)38U, c2, res_i0);
    uint64_t a_i0 = uu____0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, (uint64_t)38U, c2, res_i1);
    uint64_t a_i1 = uu____0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, (uint64_t)38U, c2, res_i2);
    uint64_t a_i2 = uu____0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, (uint64_t)38U, c2, res_i);
  }
  for (uint32_t i = (uint32_t)4U; i < (uint32_t)4U; i++)
  {
    uint64_t a_i = uu____0[i];
    uint64_t *res_i = res_j + i;
    c2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, (uint64_t)38U, c2, res_i);
  }
  uint64_t r = c2;
  uint64_t c00 = r;
  uint64_t *uu____2 = tmp;
  uint64_t
  c01 =
    Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U,
      uu____2[0U],
      c00 * (uint64_t)38U,
      out);
  uint64_t c3;
  if ((uint32_t)1U < (uint32_t)4U)
  {
    uint32_t rLen = (uint32_t)3U;
    uint64_t *a1 = uu____2 + (uint32_t)1U;
    uint64_t *res1 = out + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    c3 = c10;
  }
  else
  {
    c3 = c01;
  }
  out[0U] = out[0U] + c3 * (uint64_t)38U;
}

static inline void fsqr2_(uint64_t *out, uint64_t *f, uint64_t *tmp)
{
  uint64_t *out1 = out;
  uint64_t *out2 = out + (uint32_t)4U;
  uint64_t *f1 = f;
  uint64_t *f2 = f + (uint32_t)4U;
  fmul_(out1, f1, f1, tmp);
  fmul_(out2, f2, f2, tmp);
}

static inline void cswap2_(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  uint64_t mask = (uint64_t)0U - bit;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t dummy = mask & (p1[i] ^ p2[i]);
    p1[i] = p1[i] ^ dummy;
    p2[i] = p2[i] ^ dummy;
  }
}

static const uint8_t g25519[32U] = { (uint8_t)9U };

static void point_add_and_double(uint64_t *q, uint64_t *p01_tmp1, uint64_t *tmp2)
{
  uint64_t *nq = p01_tmp1;
  uint64_t *nq_p1 = p01_tmp1 + (uint32_t)8U;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  uint64_t *x1 = q;
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *z3 = nq_p1 + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  fadd_(a, x2, z2);
  fsub_(b, x2, z2);
  uint64_t *x3 = nq_p1;
  uint64_t *z31 = nq_p1 + (uint32_t)4U;
  uint64_t *d0 = dc;
  uint64_t *c0 = dc + (uint32_t)4U;
  fadd_(c0, x3, z31);
  fsub_(d0, x3, z31);
  fmul2_(dc, dc, ab, tmp2);
  fadd_(x3, d0, c0);
  fsub_(z31, d0, c0);
  uint64_t *a1 = tmp1;
  uint64_t *b1 = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab1 = tmp1;
  uint64_t *dc1 = tmp1 + (uint32_t)8U;
  fsqr2_(dc1, ab1, tmp2);
  fsqr2_(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  fsub_(c, d, c);
  fmul1_(b1, c, (uint64_t)121665U);
  fadd_(b1, b1, d);
  fmul2_(nq, dc1, ab1, tmp2);
  fmul_(z3, z3, x1, tmp2);
}

static void point_double(uint64_t *nq, uint64_t *tmp1, uint64_t *tmp2)
{
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  fadd_(a, x2, z2);
  fsub_(b, x2, z2);
  fsqr2_(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  fsub_(c, d, c);
  fmul1_(b, c, (uint64_t)121665U);
  fadd_(b, b, d);
  fmul2_(nq, dc, ab, tmp2);
}

static void montgomery_ladder(uint64_t *out, uint8_t *key, uint64_t *init)
{
  uint64_t tmp2[16U] = { 0U };
  uint64_t p01_tmp1_swap[33U] = { 0U };
  uint64_t *p0 = p01_tmp1_swap;
  uint64_t *p01 = p01_tmp1_swap;
  uint64_t *p03 = p01;
  uint64_t *p11 = p01 + (uint32_t)8U;
  memcpy(p11, init, (uint32_t)8U * sizeof (uint64_t));
  uint64_t *x0 = p03;
  uint64_t *z0 = p03 + (uint32_t)4U;
  x0[0U] = (uint64_t)1U;
  x0[1U] = (uint64_t)0U;
  x0[2U] = (uint64_t)0U;
  x0[3U] = (uint64_t)0U;
  z0[0U] = (uint64_t)0U;
  z0[1U] = (uint64_t)0U;
  z0[2U] = (uint64_t)0U;
  z0[3U] = (uint64_t)0U;
  uint64_t *p01_tmp1 = p01_tmp1_swap;
  uint64_t *p01_tmp11 = p01_tmp1_swap;
  uint64_t *nq1 = p01_tmp1_swap;
  uint64_t *nq_p11 = p01_tmp1_swap + (uint32_t)8U;
  uint64_t *swap = p01_tmp1_swap + (uint32_t)32U;
  cswap2_((uint64_t)1U, nq1, nq_p11);
  point_add_and_double(init, p01_tmp11, tmp2);
  swap[0U] = (uint64_t)1U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)251U; i++)
  {
    uint64_t *p01_tmp12 = p01_tmp1_swap;
    uint64_t *swap1 = p01_tmp1_swap + (uint32_t)32U;
    uint64_t *nq2 = p01_tmp12;
    uint64_t *nq_p12 = p01_tmp12 + (uint32_t)8U;
    uint64_t
    bit =
      (uint64_t)(key[((uint32_t)253U - i)
      / (uint32_t)8U]
      >> ((uint32_t)253U - i) % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t sw = swap1[0U] ^ bit;
    cswap2_(sw, nq2, nq_p12);
    point_add_and_double(init, p01_tmp12, tmp2);
    swap1[0U] = bit;
  }
  uint64_t sw = swap[0U];
  cswap2_(sw, nq1, nq_p11);
  uint64_t *nq10 = p01_tmp1;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  point_double(nq10, tmp1, tmp2);
  point_double(nq10, tmp1, tmp2);
  point_double(nq10, tmp1, tmp2);
  memcpy(out, p0, (uint32_t)8U * sizeof (uint64_t));
}

static void fsquare_times(uint64_t *o, uint64_t *inp, uint64_t *tmp, uint32_t n)
{
  fsqr_(o, inp, tmp);
  for (uint32_t i = (uint32_t)0U; i < n - (uint32_t)1U; i++)
  {
    fsqr_(o, o, tmp);
  }
}

static void finv(uint64_t *o, uint64_t *i, uint64_t *tmp)
{
  uint64_t t1[16U] = { 0U };
  uint64_t *a1 = t1;
  uint64_t *b1 = t1 + (uint32_t)4U;
  uint64_t *t010 = t1 + (uint32_t)12U;
  uint64_t *tmp10 = tmp;
  fsquare_times(a1, i, tmp10, (uint32_t)1U);
  fsquare_times(t010, a1, tmp10, (uint32_t)2U);
  fmul_(b1, t010, i, tmp);
  fmul_(a1, b1, a1, tmp);
  fsquare_times(t010, a1, tmp10, (uint32_t)1U);
  fmul_(b1, t010, b1, tmp);
  fsquare_times(t010, b1, tmp10, (uint32_t)5U);
  fmul_(b1, t010, b1, tmp);
  uint64_t *b10 = t1 + (uint32_t)4U;
  uint64_t *c10 = t1 + (uint32_t)8U;
  uint64_t *t011 = t1 + (uint32_t)12U;
  uint64_t *tmp11 = tmp;
  fsquare_times(t011, b10, tmp11, (uint32_t)10U);
  fmul_(c10, t011, b10, tmp);
  fsquare_times(t011, c10, tmp11, (uint32_t)20U);
  fmul_(t011, t011, c10, tmp);
  fsquare_times(t011, t011, tmp11, (uint32_t)10U);
  fmul_(b10, t011, b10, tmp);
  fsquare_times(t011, b10, tmp11, (uint32_t)50U);
  fmul_(c10, t011, b10, tmp);
  uint64_t *b11 = t1 + (uint32_t)4U;
  uint64_t *c1 = t1 + (uint32_t)8U;
  uint64_t *t01 = t1 + (uint32_t)12U;
  uint64_t *tmp1 = tmp;
  fsquare_times(t01, c1, tmp1, (uint32_t)100U);
  fmul_(t01, t01, c1, tmp);
  fsquare_times(t01, t01, tmp1, (uint32_t)50U);
  fmul_(t01, t01, b11, tmp);
  fsquare_times(t01, t01, tmp1, (uint32_t)5U);
  uint64_t *a = t1;
  uint64_t *t0 = t1 + (uint32_t)12U;
  fmul_(o, t0, a, tmp);
}

static void store_felem(uint64_t *b, uint64_t *f)
{
  uint64_t f30 = f[3U];
  uint64_t top_bit0 = f30 >> (uint32_t)63U;
  f[3U] = f30 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry = add1_(f, f, (uint64_t)19U * top_bit0);
  uint64_t f31 = f[3U];
  uint64_t top_bit = f31 >> (uint32_t)63U;
  f[3U] = f31 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry0 = add1_(f, f, (uint64_t)19U * top_bit);
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t m0 = FStar_UInt64_gte_mask(f0, (uint64_t)0xffffffffffffffedU);
  uint64_t m1 = FStar_UInt64_eq_mask(f1, (uint64_t)0xffffffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(f2, (uint64_t)0xffffffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(f3, (uint64_t)0x7fffffffffffffffU);
  uint64_t mask = ((m0 & m1) & m2) & m3;
  uint64_t f0_ = f0 - (mask & (uint64_t)0xffffffffffffffedU);
  uint64_t f1_ = f1 - (mask & (uint64_t)0xffffffffffffffffU);
  uint64_t f2_ = f2 - (mask & (uint64_t)0xffffffffffffffffU);
  uint64_t f3_ = f3 - (mask & (uint64_t)0x7fffffffffffffffU);
  uint64_t o0 = f0_;
  uint64_t o1 = f1_;
  uint64_t o2 = f2_;
  uint64_t o3 = f3_;
  b[0U] = o0;
  b[1U] = o1;
  b[2U] = o2;
  b[3U] = o3;
}

static void encode_point(uint8_t *o, uint64_t *i)
{
  uint64_t *x = i;
  uint64_t *z = i + (uint32_t)4U;
  uint64_t tmp[4U] = { 0U };
  uint64_t u64s[4U] = { 0U };
  uint64_t tmp_w[16U] = { 0U };
  finv(tmp, z, tmp_w);
  fmul_(tmp, tmp, x, tmp_w);
  store_felem(u64s, tmp);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    store64_le(o + i0 * (uint32_t)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_64_Slow_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint64_t init[8U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = tmp;
    uint8_t *bj = pub + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (uint64_t)0x7fffffffffffffffU;
  uint64_t *x = init;
  uint64_t *z = init + (uint32_t)4U;
  z[0U] = (uint64_t)1U;
  z[1U] = (uint64_t)0U;
  z[2U] = (uint64_t)0U;
  z[3U] = (uint64_t)0U;
  x[0U] = tmp[0U];
  x[1U] = tmp[1U];
  x[2U] = tmp[2U];
  x[3U] = tmp[3U];
  montgomery_ladder(init, priv, init);
  encode_point(out, init);
}

void Hacl_Curve25519_64_Slow_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  uint8_t basepoint[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t *os = basepoint;
    uint8_t x = g25519[i];
    os[i] = x;
  }
  Hacl_Curve25519_64_Slow_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_64_Slow_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint8_t zeros[32U] = { 0U };
  Hacl_Curve25519_64_Slow_scalarmult(out, priv, pub);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(out[i], zeros[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  return !r;
}

