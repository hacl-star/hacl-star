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


#include "Hacl_FFDHE4096.h"

static void add_mod_n(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a[(uint32_t)4U * i];
    uint64_t t20 = b[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res + (uint32_t)4U * i);
    uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
  }
  uint64_t c00 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c = (uint64_t)0U;
  uint32_t k = (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, tmp + (uint32_t)4U * i);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, tmp + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, tmp + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, tmp + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static void mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)128U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = res + i0;
    uint64_t c = (uint64_t)0U;
    uint32_t k = (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t uu____1 = a[(uint32_t)4U * i];
      uint64_t uu____2 = c;
      uint64_t *uu____3 = res_ + (uint32_t)4U * i;
      FStar_UInt128_uint128 uu____4 = FStar_UInt128_uint64_to_uint128(uu____3[0U]);
      FStar_UInt128_uint128
      res1 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____1, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____2)),
          uu____4);
      uu____3[0U] = FStar_UInt128_uint128_to_uint64(res1);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
      uint64_t uu____5 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t uu____6 = c;
      uint64_t *uu____7 = res_ + (uint32_t)4U * i + (uint32_t)1U;
      FStar_UInt128_uint128 uu____8 = FStar_UInt128_uint64_to_uint128(uu____7[0U]);
      FStar_UInt128_uint128
      res10 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____5, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____6)),
          uu____8);
      uu____7[0U] = FStar_UInt128_uint128_to_uint64(res10);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res10, (uint32_t)64U));
      uint64_t uu____9 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t uu____10 = c;
      uint64_t *uu____11 = res_ + (uint32_t)4U * i + (uint32_t)2U;
      FStar_UInt128_uint128 uu____12 = FStar_UInt128_uint64_to_uint128(uu____11[0U]);
      FStar_UInt128_uint128
      res11 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____9, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____10)),
          uu____12);
      uu____11[0U] = FStar_UInt128_uint128_to_uint64(res11);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res11, (uint32_t)64U));
      uint64_t uu____13 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t uu____14 = c;
      uint64_t *uu____15 = res_ + (uint32_t)4U * i + (uint32_t)3U;
      FStar_UInt128_uint128 uu____16 = FStar_UInt128_uint64_to_uint128(uu____15[0U]);
      FStar_UInt128_uint128
      res12 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____13, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____14)),
          uu____16);
      uu____15[0U] = FStar_UInt128_uint128_to_uint64(res12);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res12, (uint32_t)64U));
    }
    for (uint32_t i = k; i < (uint32_t)64U; i++)
    {
      uint64_t uu____17 = a[i];
      uint64_t uu____18 = c;
      uint64_t *uu____19 = res_ + i;
      FStar_UInt128_uint128 uu____20 = FStar_UInt128_uint64_to_uint128(uu____19[0U]);
      FStar_UInt128_uint128
      res1 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____17, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____18)),
          uu____20);
      uu____19[0U] = FStar_UInt128_uint128_to_uint64(res1);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    }
    uint64_t r = c;
    res[(uint32_t)64U + i0] = r;
  }
}

static void sqr(uint64_t *a, uint64_t *res)
{
  uint32_t resLen = (uint32_t)128U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t uu____0 = a[i0];
    uint64_t *res_ = res + i0;
    uint64_t c = (uint64_t)0U;
    uint32_t k = (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t uu____1 = a[(uint32_t)4U * i];
      uint64_t uu____2 = c;
      uint64_t *uu____3 = res_ + (uint32_t)4U * i;
      FStar_UInt128_uint128 uu____4 = FStar_UInt128_uint64_to_uint128(uu____3[0U]);
      FStar_UInt128_uint128
      res1 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____1, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____2)),
          uu____4);
      uu____3[0U] = FStar_UInt128_uint128_to_uint64(res1);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
      uint64_t uu____5 = a[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t uu____6 = c;
      uint64_t *uu____7 = res_ + (uint32_t)4U * i + (uint32_t)1U;
      FStar_UInt128_uint128 uu____8 = FStar_UInt128_uint64_to_uint128(uu____7[0U]);
      FStar_UInt128_uint128
      res10 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____5, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____6)),
          uu____8);
      uu____7[0U] = FStar_UInt128_uint128_to_uint64(res10);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res10, (uint32_t)64U));
      uint64_t uu____9 = a[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t uu____10 = c;
      uint64_t *uu____11 = res_ + (uint32_t)4U * i + (uint32_t)2U;
      FStar_UInt128_uint128 uu____12 = FStar_UInt128_uint64_to_uint128(uu____11[0U]);
      FStar_UInt128_uint128
      res11 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____9, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____10)),
          uu____12);
      uu____11[0U] = FStar_UInt128_uint128_to_uint64(res11);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res11, (uint32_t)64U));
      uint64_t uu____13 = a[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t uu____14 = c;
      uint64_t *uu____15 = res_ + (uint32_t)4U * i + (uint32_t)3U;
      FStar_UInt128_uint128 uu____16 = FStar_UInt128_uint64_to_uint128(uu____15[0U]);
      FStar_UInt128_uint128
      res12 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____13, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____14)),
          uu____16);
      uu____15[0U] = FStar_UInt128_uint128_to_uint64(res12);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res12, (uint32_t)64U));
    }
    for (uint32_t i = k; i < (uint32_t)64U; i++)
    {
      uint64_t uu____17 = a[i];
      uint64_t uu____18 = c;
      uint64_t *uu____19 = res_ + i;
      FStar_UInt128_uint128 uu____20 = FStar_UInt128_uint64_to_uint128(uu____19[0U]);
      FStar_UInt128_uint128
      res1 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____17, uu____0),
            FStar_UInt128_uint64_to_uint128(uu____18)),
          uu____20);
      uu____19[0U] = FStar_UInt128_uint128_to_uint64(res1);
      c = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    }
    uint64_t r = c;
    res[(uint32_t)64U + i0] = r;
  }
}

static void precomp(uint32_t nBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, (uint32_t)64U * sizeof (uint64_t));
  uint32_t i = nBits / (uint32_t)64U;
  uint32_t j = nBits % (uint32_t)64U;
  res[i] = res[i] | (uint64_t)1U << j;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)8192U - nBits; i0++)
  {
    add_mod_n(n, res, res, res);
  }
}

static void reduction(uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = (uint32_t)64U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t uu____0 = n[(uint32_t)4U * i];
      uint64_t uu____1 = c1;
      uint64_t *uu____2 = res_ + (uint32_t)4U * i;
      FStar_UInt128_uint128 uu____3 = FStar_UInt128_uint64_to_uint128(uu____2[0U]);
      FStar_UInt128_uint128
      res1 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____0, qj),
            FStar_UInt128_uint64_to_uint128(uu____1)),
          uu____3);
      uu____2[0U] = FStar_UInt128_uint128_to_uint64(res1);
      c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
      uint64_t uu____4 = n[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t uu____5 = c1;
      uint64_t *uu____6 = res_ + (uint32_t)4U * i + (uint32_t)1U;
      FStar_UInt128_uint128 uu____7 = FStar_UInt128_uint64_to_uint128(uu____6[0U]);
      FStar_UInt128_uint128
      res10 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____4, qj),
            FStar_UInt128_uint64_to_uint128(uu____5)),
          uu____7);
      uu____6[0U] = FStar_UInt128_uint128_to_uint64(res10);
      c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res10, (uint32_t)64U));
      uint64_t uu____8 = n[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t uu____9 = c1;
      uint64_t *uu____10 = res_ + (uint32_t)4U * i + (uint32_t)2U;
      FStar_UInt128_uint128 uu____11 = FStar_UInt128_uint64_to_uint128(uu____10[0U]);
      FStar_UInt128_uint128
      res11 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____8, qj),
            FStar_UInt128_uint64_to_uint128(uu____9)),
          uu____11);
      uu____10[0U] = FStar_UInt128_uint128_to_uint64(res11);
      c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res11, (uint32_t)64U));
      uint64_t uu____12 = n[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t uu____13 = c1;
      uint64_t *uu____14 = res_ + (uint32_t)4U * i + (uint32_t)3U;
      FStar_UInt128_uint128 uu____15 = FStar_UInt128_uint64_to_uint128(uu____14[0U]);
      FStar_UInt128_uint128
      res12 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____12, qj),
            FStar_UInt128_uint64_to_uint128(uu____13)),
          uu____15);
      uu____14[0U] = FStar_UInt128_uint128_to_uint64(res12);
      c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res12, (uint32_t)64U));
    }
    for (uint32_t i = k; i < (uint32_t)64U; i++)
    {
      uint64_t uu____16 = n[i];
      uint64_t uu____17 = c1;
      uint64_t *uu____18 = res_ + i;
      FStar_UInt128_uint128 uu____19 = FStar_UInt128_uint64_to_uint128(uu____18[0U]);
      FStar_UInt128_uint128
      res1 =
        FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(uu____16, qj),
            FStar_UInt128_uint64_to_uint128(uu____17)),
          uu____19);
      uu____18[0U] = FStar_UInt128_uint128_to_uint64(res1);
      c1 = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    c0 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c0,
        c10,
        c[(uint32_t)64U + i0],
        c + (uint32_t)64U + i0);
  }
  memcpy(res, c + (uint32_t)64U, (uint32_t)64U * sizeof (uint64_t));
  uint64_t uu____20 = c0;
  uint64_t tmp[64U] = { 0U };
  uint64_t c1 = (uint64_t)0U;
  uint32_t k = (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
  {
    uint64_t t1 = res[(uint32_t)4U * i];
    uint64_t t20 = n[(uint32_t)4U * i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, tmp + (uint32_t)4U * i);
    uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = n[(uint32_t)4U * i + (uint32_t)1U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t10,
        t21,
        tmp + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = n[(uint32_t)4U * i + (uint32_t)2U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t11,
        t22,
        tmp + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = n[(uint32_t)4U * i + (uint32_t)3U];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, tmp + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tmp + i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = uu____20 - c10;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static void
mod_exp_mont_ladder_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
)
{
  uint64_t one[64U] = { 0U };
  memset(one, 0U, (uint32_t)64U * sizeof (uint64_t));
  one[0U] = (uint64_t)1U;
  uint64_t nInv = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  uint64_t rM0[64U] = { 0U };
  uint64_t rM1[64U] = { 0U };
  uint64_t sw = (uint64_t)0U;
  uint64_t c[128U] = { 0U };
  mul(one, r2, c);
  reduction(n, nInv, c, rM0);
  uint64_t c0[128U] = { 0U };
  mul(a, r2, c0);
  reduction(n, nInv, c0, rM1);
  for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
  {
    uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
    uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
    uint64_t tmp = b[i1];
    uint64_t bit = tmp >> j & (uint64_t)1U;
    uint64_t sw1 = bit ^ sw;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw1) & (rM0[i] ^ rM1[i]);
      rM0[i] = rM0[i] ^ dummy;
      rM1[i] = rM1[i] ^ dummy;
    }
    uint64_t c1[128U] = { 0U };
    mul(rM1, rM0, c1);
    reduction(n, nInv, c1, rM1);
    uint64_t c2[128U] = { 0U };
    sqr(rM0, c2);
    reduction(n, nInv, c2, rM0);
    sw = bit;
  }
  uint64_t uu____0 = sw;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t dummy = ((uint64_t)0U - uu____0) & (rM0[i] ^ rM1[i]);
    rM0[i] = rM0[i] ^ dummy;
    rM1[i] = rM1[i] ^ dummy;
  }
  uint64_t tmp[128U] = { 0U };
  memcpy(tmp, rM0, (uint32_t)64U * sizeof (uint64_t));
  reduction(n, nInv, tmp, res);
}

static inline void ffdhe_precomp_p(uint64_t *p_r2_n)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint64_t *p_n = p_r2_n;
  uint64_t *r2_n = p_r2_n + nLen;
  uint8_t p_s[512U] = { 0U };
  const uint8_t *p = Hacl_Impl_FFDHE_Constants_ffdhe_p4096;
  uint32_t len1 = Hacl_Impl_FFDHE_ffdhe_len(Spec_FFDHE_FFDHE4096);
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    uint8_t *os = p_s;
    uint8_t x = p[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, p_s, p_n);
  precomp((uint32_t)4095U, p_n, r2_n);
}

static inline uint64_t ffdhe_check_pk(uint64_t *pk_n, uint64_t *p_n)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t p_n1[nLen];
  memset(p_n1, 0U, nLen * sizeof (uint64_t));
  uint64_t
  c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, p_n[0U], (uint64_t)1U, p_n1);
  uint64_t uu____0;
  if ((uint32_t)1U < nLen)
  {
    uint32_t rLen = nLen - (uint32_t)1U;
    uint64_t *a1 = p_n + (uint32_t)1U;
    uint64_t *res1 = p_n1 + (uint32_t)1U;
    uint64_t c = c0;
    uint32_t k = rLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = a1[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res1 + (uint32_t)4U * i);
      uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t10,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t11,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_sub_borrow_u64(c,
          t12,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < rLen; i++)
    {
      uint64_t t1 = a1[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, (uint64_t)0U, res1 + i);
    }
    uint64_t c1 = c;
    uu____0 = c1;
  }
  else
  {
    uu____0 = c0;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t b2[nLen];
  memset(b2, 0U, nLen * sizeof (uint64_t));
  uint32_t i0 = (uint32_t)0U;
  uint32_t j = (uint32_t)0U;
  b2[i0] = b2[i0] | (uint64_t)1U << j;
  uint64_t acc0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(b2[i], pk_n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(b2[i], pk_n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t res = acc0;
  uint64_t m0 = res;
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < nLen; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(pk_n[i], p_n1[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(pk_n[i], p_n1[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t m1 = acc;
  return m0 & m1;
}

static inline void
ffdhe_compute_exp(uint64_t *p_r2_n, uint64_t *sk_n, uint64_t *b_n, uint8_t *res)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint64_t *p_n = p_r2_n;
  uint64_t *r2_n = p_r2_n + nLen;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t res_n[nLen];
  memset(res_n, 0U, nLen * sizeof (uint64_t));
  mod_exp_mont_ladder_precompr2(p_n, b_n, (uint32_t)64U * nLen, sk_n, r2_n, res_n);
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64((uint32_t)512U, res_n, res);
}

uint64_t *Hacl_FFDHE4096_new_ffdhe_precomp_p()
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t *res = KRML_HOST_CALLOC(nLen + nLen, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  ffdhe_precomp_p(res2);
  return res2;
}

void Hacl_FFDHE4096_ffdhe_secret_to_public_precomp(uint64_t *p_r2_n, uint8_t *sk, uint8_t *pk)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t g_n[nLen];
  memset(g_n, 0U, nLen * sizeof (uint64_t));
  uint8_t g = (uint8_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
  {
    uint8_t *os = &g;
    uint8_t x = Hacl_Impl_FFDHE_Constants_ffdhe_g2[i];
    os[i] = x;
  }
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)1U, &g, g_n);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t sk_n[nLen];
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, sk, sk_n);
  ffdhe_compute_exp(p_r2_n, sk_n, g_n, pk);
}

void Hacl_FFDHE4096_ffdhe_secret_to_public(uint8_t *sk, uint8_t *pk)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t p_r2_n[nLen + nLen];
  memset(p_r2_n, 0U, (nLen + nLen) * sizeof (uint64_t));
  ffdhe_precomp_p(p_r2_n);
  Hacl_FFDHE4096_ffdhe_secret_to_public_precomp(p_r2_n, sk, pk);
}

uint64_t
Hacl_FFDHE4096_ffdhe_shared_secret_precomp(
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk,
  uint8_t *ss
)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint64_t *p_n = p_r2_n;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t sk_n[nLen];
  memset(sk_n, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t pk_n[nLen];
  memset(pk_n, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, sk, sk_n);
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)512U, pk, pk_n);
  uint64_t m = ffdhe_check_pk(pk_n, p_n);
  if (m == (uint64_t)0xFFFFFFFFFFFFFFFFU)
  {
    ffdhe_compute_exp(p_r2_n, sk_n, pk_n, ss);
  }
  return m;
}

uint64_t Hacl_FFDHE4096_ffdhe_shared_secret(uint8_t *sk, uint8_t *pk, uint8_t *ss)
{
  uint32_t nLen = ((uint32_t)512U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen + nLen);
  uint64_t p_n[nLen + nLen];
  memset(p_n, 0U, (nLen + nLen) * sizeof (uint64_t));
  ffdhe_precomp_p(p_n);
  uint64_t m = Hacl_FFDHE4096_ffdhe_shared_secret_precomp(p_n, sk, pk, ss);
  return m;
}

