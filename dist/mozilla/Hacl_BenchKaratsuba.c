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


#include "Hacl_BenchKaratsuba.h"

#include "internal/Hacl_Bignum256_32_Hacl_Bignum4096_32_Hacl_Bignum256_Hacl_Bignum4096_Hacl_Bignum32_Hacl_Bignum64_Hacl_GenericField32_Hacl_GenericField64_Hacl_Bignum_Hacl_Bignum.h"

void
Hacl_BenchKaratsuba_bn_karatsuba_mul_uint32(
  uint32_t threshold,
  uint32_t aLen,
  uint32_t *a,
  uint32_t *b,
  uint32_t *tmp,
  uint32_t *res
)
{
  if (aLen < threshold || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    Hacl_Bignum_Multiplication_bn_mul_u32(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint32_t *a0 = a;
  uint32_t *a1 = a + len2;
  uint32_t *b0 = b;
  uint32_t *b1 = b + len2;
  uint32_t *t0 = tmp;
  uint32_t *t1 = tmp + len2;
  uint32_t *tmp_ = tmp + aLen;
  uint32_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
  uint32_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint32_t *os = t0;
    uint32_t x = (((uint32_t)0U - c0) & t0[i]) | (~((uint32_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint32_t c00 = c0;
  uint32_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b0, b1, tmp_);
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b1, b0, t1);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint32_t *os = t1;
    uint32_t x = (((uint32_t)0U - c010) & t1[i]) | (~((uint32_t)0U - c010) & tmp_[i]);
    os[i] = x;
  }
  uint32_t c11 = c010;
  uint32_t *t23 = tmp + aLen;
  uint32_t *tmp1 = tmp + aLen + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_mul_uint32(threshold, len2, t0, t1, tmp1, t23);
  uint32_t *r01 = res;
  uint32_t *r23 = res + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_mul_uint32(threshold, len2, a0, b0, tmp1, r01);
  Hacl_BenchKaratsuba_bn_karatsuba_mul_uint32(threshold, len2, a1, b1, tmp1, r23);
  uint32_t *r011 = res;
  uint32_t *r231 = res + aLen;
  uint32_t *t01 = tmp;
  uint32_t *t231 = tmp + aLen;
  uint32_t *t45 = tmp + (uint32_t)2U * aLen;
  uint32_t *t67 = tmp + (uint32_t)3U * aLen;
  uint32_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
  uint32_t c_sign = c00 ^ c11;
  uint32_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t67);
  uint32_t c31 = c2 - c3;
  uint32_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, t01, t231, t45);
  uint32_t c41 = c2 + c4;
  uint32_t mask = (uint32_t)0U - c_sign;
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint32_t *os = t45;
    uint32_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint32_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint32_t *r0 = res + aLen2;
  uint32_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r0, t45, r0);
  uint32_t c6 = r10;
  uint32_t c60 = c6;
  uint32_t c7 = c5 + c60;
  uint32_t *r = res + aLen + aLen2;
  uint32_t c01 = Lib_IntTypes_Intrinsics_add_carry_u32((uint32_t)0U, r[0U], c7, r);
  uint32_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint32_t *a11 = r + (uint32_t)1U;
    uint32_t *res1 = r + (uint32_t)1U;
    uint32_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint32_t t11 = a11[(uint32_t)4U * i];
      uint32_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, (uint32_t)0U, res_i0);
      uint32_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t110, (uint32_t)0U, res_i1);
      uint32_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t111, (uint32_t)0U, res_i2);
      uint32_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t112, (uint32_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint32_t t11 = a11[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, (uint32_t)0U, res_i);
    }
    uint32_t c110 = c;
    r1 = c110;
  }
  else
  {
    r1 = c01;
  }
  uint32_t c8 = r1;
  uint32_t c = c8;
  uint32_t c9 = c;
}

void
Hacl_BenchKaratsuba_bn_karatsuba_mul_uint64(
  uint32_t threshold,
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < threshold || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    Hacl_Bignum_Multiplication_bn_mul_u64(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *b0 = b;
  uint64_t *b1 = b + len2;
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + len2;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c00 = c0;
  uint64_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b0, b1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b1, b0, t1);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t1;
    uint64_t x = (((uint64_t)0U - c010) & t1[i]) | (~((uint64_t)0U - c010) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c11 = c010;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_mul_uint64(threshold, len2, t0, t1, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_mul_uint64(threshold, len2, a0, b0, tmp1, r01);
  Hacl_BenchKaratsuba_bn_karatsuba_mul_uint64(threshold, len2, a1, b1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t *t67 = tmp + (uint32_t)3U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c_sign = c00 ^ c11;
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t67);
  uint64_t c31 = c2 - c3;
  uint64_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c41 = c2 + c4;
  uint64_t mask = (uint64_t)0U - c_sign;
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint64_t *os = t45;
    uint64_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint64_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c6 = r10;
  uint64_t c60 = c6;
  uint64_t c7 = c5 + c60;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t11 = a11[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i0);
      uint64_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t110, (uint64_t)0U, res_i1);
      uint64_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t111, (uint64_t)0U, res_i2);
      uint64_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t112, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t11 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i);
    }
    uint64_t c110 = c;
    r1 = c110;
  }
  else
  {
    r1 = c01;
  }
  uint64_t c8 = r1;
  uint64_t c = c8;
  uint64_t c9 = c;
}

void
Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint32(
  uint32_t threshold,
  uint32_t aLen,
  uint32_t *a,
  uint32_t *tmp,
  uint32_t *res
)
{
  if (aLen < threshold || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    Hacl_Bignum_Multiplication_bn_sqr_u32(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint32_t *a0 = a;
  uint32_t *a1 = a + len2;
  uint32_t *t0 = tmp;
  uint32_t *tmp_ = tmp + aLen;
  uint32_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint32_t *os = t0;
    uint32_t x = (((uint32_t)0U - c0) & t0[i]) | (~((uint32_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint32_t c00 = c0;
  uint32_t *t23 = tmp + aLen;
  uint32_t *tmp1 = tmp + aLen + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint32(threshold, len2, t0, tmp1, t23);
  uint32_t *r01 = res;
  uint32_t *r23 = res + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint32(threshold, len2, a0, tmp1, r01);
  Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint32(threshold, len2, a1, tmp1, r23);
  uint32_t *r011 = res;
  uint32_t *r231 = res + aLen;
  uint32_t *t01 = tmp;
  uint32_t *t231 = tmp + aLen;
  uint32_t *t45 = tmp + (uint32_t)2U * aLen;
  uint32_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
  uint32_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t45);
  uint32_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint32_t *r0 = res + aLen2;
  uint32_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r0, t45, r0);
  uint32_t c4 = r10;
  uint32_t c6 = c4;
  uint32_t c7 = c5 + c6;
  uint32_t *r = res + aLen + aLen2;
  uint32_t c01 = Lib_IntTypes_Intrinsics_add_carry_u32((uint32_t)0U, r[0U], c7, r);
  uint32_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint32_t *a11 = r + (uint32_t)1U;
    uint32_t *res1 = r + (uint32_t)1U;
    uint32_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint32_t t1 = a11[(uint32_t)4U * i];
      uint32_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, (uint32_t)0U, res_i0);
      uint32_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint32_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, (uint32_t)0U, res_i1);
      uint32_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint32_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, (uint32_t)0U, res_i2);
      uint32_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint32_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, (uint32_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint32_t t1 = a11[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, (uint32_t)0U, res_i);
    }
    uint32_t c10 = c;
    r1 = c10;
  }
  else
  {
    r1 = c01;
  }
  uint32_t c8 = r1;
  uint32_t c = c8;
  uint32_t c9 = c;
}

void
Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint64(
  uint32_t threshold,
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < threshold || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    Hacl_Bignum_Multiplication_bn_sqr_u64(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *t0 = tmp;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c00 = c0;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint64(threshold, len2, t0, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint64(threshold, len2, a0, tmp1, r01);
  Hacl_BenchKaratsuba_bn_karatsuba_sqr_uint64(threshold, len2, a1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c4 = r10;
  uint64_t c6 = c4;
  uint64_t c7 = c5 + c6;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c01;
    for (uint32_t i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a11[(uint32_t)4U * i];
      uint64_t *res_i0 = res1 + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
      uint64_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
      uint64_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
      uint64_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
    }
    for (uint32_t i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
    {
      uint64_t t1 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
    }
    uint64_t c10 = c;
    r1 = c10;
  }
  else
  {
    r1 = c01;
  }
  uint64_t c8 = r1;
  uint64_t c = c8;
  uint64_t c9 = c;
}

