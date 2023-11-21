/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#include "internal/Hacl_Bignum.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
  uint32_t aLen,
  uint32_t *a,
  uint32_t *b,
  uint32_t *tmp,
  uint32_t *res
)
{
  if (aLen < 32U || aLen % 2U == 1U)
  {
    Hacl_Bignum_Multiplication_bn_mul_u32(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / 2U;
  uint32_t *a0 = a;
  uint32_t *a1 = a + len2;
  uint32_t *b0 = b;
  uint32_t *b1 = b + len2;
  uint32_t *t0 = tmp;
  uint32_t *t1 = tmp + len2;
  uint32_t *tmp_ = tmp + aLen;
  uint32_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
  uint32_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
  for (uint32_t i = 0U; i < len2; i++)
  {
    uint32_t *os = t0;
    uint32_t x = ((0U - c0) & t0[i]) | (~(0U - c0) & tmp_[i]);
    os[i] = x;
  }
  KRML_MAYBE_UNUSED_VAR(c10);
  uint32_t c00 = c0;
  uint32_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b0, b1, tmp_);
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b1, b0, t1);
  for (uint32_t i = 0U; i < len2; i++)
  {
    uint32_t *os = t1;
    uint32_t x = ((0U - c010) & t1[i]) | (~(0U - c010) & tmp_[i]);
    os[i] = x;
  }
  KRML_MAYBE_UNUSED_VAR(c1);
  uint32_t c11 = c010;
  uint32_t *t23 = tmp + aLen;
  uint32_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, t0, t1, tmp1, t23);
  uint32_t *r01 = res;
  uint32_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, a0, b0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, a1, b1, tmp1, r23);
  uint32_t *r011 = res;
  uint32_t *r231 = res + aLen;
  uint32_t *t01 = tmp;
  uint32_t *t231 = tmp + aLen;
  uint32_t *t45 = tmp + 2U * aLen;
  uint32_t *t67 = tmp + 3U * aLen;
  uint32_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
  uint32_t c_sign = c00 ^ c11;
  uint32_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t67);
  uint32_t c31 = c2 - c3;
  uint32_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, t01, t231, t45);
  uint32_t c41 = c2 + c4;
  uint32_t mask = 0U - c_sign;
  for (uint32_t i = 0U; i < aLen; i++)
  {
    uint32_t *os = t45;
    uint32_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint32_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / 2U;
  uint32_t *r0 = res + aLen2;
  uint32_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r0, t45, r0);
  uint32_t c6 = r10;
  uint32_t c60 = c6;
  uint32_t c7 = c5 + c60;
  uint32_t *r = res + aLen + aLen2;
  uint32_t c01 = Lib_IntTypes_Intrinsics_add_carry_u32(0U, r[0U], c7, r);
  uint32_t r1;
  if (1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t *a11 = r + 1U;
    uint32_t *res1 = r + 1U;
    uint32_t c = c01;
    for (uint32_t i = 0U; i < (aLen + aLen - (aLen + aLen2) - 1U) / 4U; i++)
    {
      uint32_t t11 = a11[4U * i];
      uint32_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, 0U, res_i0);
      uint32_t t110 = a11[4U * i + 1U];
      uint32_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t110, 0U, res_i1);
      uint32_t t111 = a11[4U * i + 2U];
      uint32_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t111, 0U, res_i2);
      uint32_t t112 = a11[4U * i + 3U];
      uint32_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t112, 0U, res_i);
    }
    for
    (uint32_t
      i = (aLen + aLen - (aLen + aLen2) - 1U) / 4U * 4U;
      i
      < aLen + aLen - (aLen + aLen2) - 1U;
      i++)
    {
      uint32_t t11 = a11[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, 0U, res_i);
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
  KRML_MAYBE_UNUSED_VAR(c9);
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < 32U || aLen % 2U == 1U)
  {
    Hacl_Bignum_Multiplication_bn_mul_u64(aLen, a, aLen, b, res);
    return;
  }
  uint32_t len2 = aLen / 2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *b0 = b;
  uint64_t *b1 = b + len2;
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + len2;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c10 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = 0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = ((0ULL - c0) & t0[i]) | (~(0ULL - c0) & tmp_[i]);
    os[i] = x;
  }
  KRML_MAYBE_UNUSED_VAR(c10);
  uint64_t c00 = c0;
  uint64_t c010 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b0, b1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b1, b0, t1);
  for (uint32_t i = 0U; i < len2; i++)
  {
    uint64_t *os = t1;
    uint64_t x = ((0ULL - c010) & t1[i]) | (~(0ULL - c010) & tmp_[i]);
    os[i] = x;
  }
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t c11 = c010;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, t0, t1, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a0, b0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a1, b1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + 2U * aLen;
  uint64_t *t67 = tmp + 3U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c_sign = c00 ^ c11;
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t67);
  uint64_t c31 = c2 - c3;
  uint64_t c4 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c41 = c2 + c4;
  uint64_t mask = 0ULL - c_sign;
  for (uint32_t i = 0U; i < aLen; i++)
  {
    uint64_t *os = t45;
    uint64_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint64_t c5 = (mask & c41) | (~mask & c31);
  uint32_t aLen2 = aLen / 2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c6 = r10;
  uint64_t c60 = c6;
  uint64_t c7 = c5 + c60;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64(0ULL, r[0U], c7, r);
  uint64_t r1;
  if (1U < aLen + aLen - (aLen + aLen2))
  {
    uint64_t *a11 = r + 1U;
    uint64_t *res1 = r + 1U;
    uint64_t c = c01;
    for (uint32_t i = 0U; i < (aLen + aLen - (aLen + aLen2) - 1U) / 4U; i++)
    {
      uint64_t t11 = a11[4U * i];
      uint64_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, 0ULL, res_i0);
      uint64_t t110 = a11[4U * i + 1U];
      uint64_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t110, 0ULL, res_i1);
      uint64_t t111 = a11[4U * i + 2U];
      uint64_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t111, 0ULL, res_i2);
      uint64_t t112 = a11[4U * i + 3U];
      uint64_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t112, 0ULL, res_i);
    }
    for
    (uint32_t
      i = (aLen + aLen - (aLen + aLen2) - 1U) / 4U * 4U;
      i
      < aLen + aLen - (aLen + aLen2) - 1U;
      i++)
    {
      uint64_t t11 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, 0ULL, res_i);
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
  KRML_MAYBE_UNUSED_VAR(c9);
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(
  uint32_t aLen,
  uint32_t *a,
  uint32_t *tmp,
  uint32_t *res
)
{
  if (aLen < 32U || aLen % 2U == 1U)
  {
    Hacl_Bignum_Multiplication_bn_sqr_u32(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / 2U;
  uint32_t *a0 = a;
  uint32_t *a1 = a + len2;
  uint32_t *t0 = tmp;
  uint32_t *tmp_ = tmp + aLen;
  uint32_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
  for (uint32_t i = 0U; i < len2; i++)
  {
    uint32_t *os = t0;
    uint32_t x = ((0U - c0) & t0[i]) | (~(0U - c0) & tmp_[i]);
    os[i] = x;
  }
  KRML_MAYBE_UNUSED_VAR(c1);
  uint32_t c00 = c0;
  KRML_MAYBE_UNUSED_VAR(c00);
  uint32_t *t23 = tmp + aLen;
  uint32_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, t0, tmp1, t23);
  uint32_t *r01 = res;
  uint32_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, a0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, a1, tmp1, r23);
  uint32_t *r011 = res;
  uint32_t *r231 = res + aLen;
  uint32_t *t01 = tmp;
  uint32_t *t231 = tmp + aLen;
  uint32_t *t45 = tmp + 2U * aLen;
  uint32_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
  uint32_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t45);
  uint32_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / 2U;
  uint32_t *r0 = res + aLen2;
  uint32_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r0, t45, r0);
  uint32_t c4 = r10;
  uint32_t c6 = c4;
  uint32_t c7 = c5 + c6;
  uint32_t *r = res + aLen + aLen2;
  uint32_t c01 = Lib_IntTypes_Intrinsics_add_carry_u32(0U, r[0U], c7, r);
  uint32_t r1;
  if (1U < aLen + aLen - (aLen + aLen2))
  {
    uint32_t *a11 = r + 1U;
    uint32_t *res1 = r + 1U;
    uint32_t c = c01;
    for (uint32_t i = 0U; i < (aLen + aLen - (aLen + aLen2) - 1U) / 4U; i++)
    {
      uint32_t t1 = a11[4U * i];
      uint32_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, 0U, res_i0);
      uint32_t t10 = a11[4U * i + 1U];
      uint32_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, 0U, res_i1);
      uint32_t t11 = a11[4U * i + 2U];
      uint32_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, 0U, res_i2);
      uint32_t t12 = a11[4U * i + 3U];
      uint32_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, 0U, res_i);
    }
    for
    (uint32_t
      i = (aLen + aLen - (aLen + aLen2) - 1U) / 4U * 4U;
      i
      < aLen + aLen - (aLen + aLen2) - 1U;
      i++)
    {
      uint32_t t1 = a11[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, 0U, res_i);
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
  KRML_MAYBE_UNUSED_VAR(c9);
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < 32U || aLen % 2U == 1U)
  {
    Hacl_Bignum_Multiplication_bn_sqr_u64(aLen, a, res);
    return;
  }
  uint32_t len2 = aLen / 2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + len2;
  uint64_t *t0 = tmp;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
  for (uint32_t i = 0U; i < len2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = ((0ULL - c0) & t0[i]) | (~(0ULL - c0) & tmp_[i]);
    os[i] = x;
  }
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t c00 = c0;
  KRML_MAYBE_UNUSED_VAR(c00);
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, t0, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + 2U * aLen;
  uint64_t c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
  uint64_t c3 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t45);
  uint64_t c5 = c2 - c3;
  uint32_t aLen2 = aLen / 2U;
  uint64_t *r0 = res + aLen2;
  uint64_t r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
  uint64_t c4 = r10;
  uint64_t c6 = c4;
  uint64_t c7 = c5 + c6;
  uint64_t *r = res + aLen + aLen2;
  uint64_t c01 = Lib_IntTypes_Intrinsics_add_carry_u64(0ULL, r[0U], c7, r);
  uint64_t r1;
  if (1U < aLen + aLen - (aLen + aLen2))
  {
    uint64_t *a11 = r + 1U;
    uint64_t *res1 = r + 1U;
    uint64_t c = c01;
    for (uint32_t i = 0U; i < (aLen + aLen - (aLen + aLen2) - 1U) / 4U; i++)
    {
      uint64_t t1 = a11[4U * i];
      uint64_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, 0ULL, res_i0);
      uint64_t t10 = a11[4U * i + 1U];
      uint64_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, 0ULL, res_i1);
      uint64_t t11 = a11[4U * i + 2U];
      uint64_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, 0ULL, res_i2);
      uint64_t t12 = a11[4U * i + 3U];
      uint64_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, 0ULL, res_i);
    }
    for
    (uint32_t
      i = (aLen + aLen - (aLen + aLen2) - 1U) / 4U * 4U;
      i
      < aLen + aLen - (aLen + aLen2) - 1U;
      i++)
    {
      uint64_t t1 = a11[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, 0ULL, res_i);
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
  KRML_MAYBE_UNUSED_VAR(c9);
}

void
Hacl_Bignum_bn_add_mod_n_u32(
  uint32_t len1,
  uint32_t *n,
  uint32_t *a,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t c0 = 0U;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint32_t t1 = a[4U * i];
    uint32_t t20 = b[4U * i];
    uint32_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[4U * i + 1U];
    uint32_t t21 = b[4U * i + 1U];
    uint32_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[4U * i + 2U];
    uint32_t t22 = b[4U * i + 2U];
    uint32_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[4U * i + 3U];
    uint32_t t2 = b[4U * i + 3U];
    uint32_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint32_t t1 = a[i];
    uint32_t t2 = b[i];
    uint32_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, t1, t2, res_i);
  }
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len1);
  uint32_t tmp[len1];
  memset(tmp, 0U, len1 * sizeof (uint32_t));
  uint32_t c = 0U;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint32_t t1 = res[4U * i];
    uint32_t t20 = n[4U * i];
    uint32_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[4U * i + 1U];
    uint32_t t21 = n[4U * i + 1U];
    uint32_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[4U * i + 2U];
    uint32_t t22 = n[4U * i + 2U];
    uint32_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[4U * i + 3U];
    uint32_t t2 = n[4U * i + 3U];
    uint32_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint32_t t1 = res[i];
    uint32_t t2 = n[i];
    uint32_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t2, res_i);
  }
  uint32_t c1 = c;
  uint32_t c2 = c00 - c1;
  for (uint32_t i = 0U; i < len1; i++)
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_bn_add_mod_n_u64(
  uint32_t len1,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t c0 = 0ULL;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint64_t t1 = a[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t tmp[len1];
  memset(tmp, 0U, len1 * sizeof (uint64_t));
  uint64_t c = 0ULL;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint64_t t1 = res[4U * i];
    uint64_t t20 = n[4U * i];
    uint64_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * i + 1U];
    uint64_t t21 = n[4U * i + 1U];
    uint64_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * i + 2U];
    uint64_t t22 = n[4U * i + 2U];
    uint64_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * i + 3U];
    uint64_t t2 = n[4U * i + 3U];
    uint64_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = 0U; i < len1; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_bn_sub_mod_n_u32(
  uint32_t len1,
  uint32_t *n,
  uint32_t *a,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t c0 = 0U;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint32_t t1 = a[4U * i];
    uint32_t t20 = b[4U * i];
    uint32_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
    uint32_t t10 = a[4U * i + 1U];
    uint32_t t21 = b[4U * i + 1U];
    uint32_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
    uint32_t t11 = a[4U * i + 2U];
    uint32_t t22 = b[4U * i + 2U];
    uint32_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
    uint32_t t12 = a[4U * i + 3U];
    uint32_t t2 = b[4U * i + 3U];
    uint32_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint32_t t1 = a[i];
    uint32_t t2 = b[i];
    uint32_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t2, res_i);
  }
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len1);
  uint32_t tmp[len1];
  memset(tmp, 0U, len1 * sizeof (uint32_t));
  uint32_t c = 0U;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint32_t t1 = res[4U * i];
    uint32_t t20 = n[4U * i];
    uint32_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    uint32_t t10 = res[4U * i + 1U];
    uint32_t t21 = n[4U * i + 1U];
    uint32_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    uint32_t t11 = res[4U * i + 2U];
    uint32_t t22 = n[4U * i + 2U];
    uint32_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    uint32_t t12 = res[4U * i + 3U];
    uint32_t t2 = n[4U * i + 3U];
    uint32_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint32_t t1 = res[i];
    uint32_t t2 = n[i];
    uint32_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u32(c, t1, t2, res_i);
  }
  uint32_t c1 = c;
  KRML_MAYBE_UNUSED_VAR(c1);
  uint32_t c2 = 0U - c00;
  for (uint32_t i = 0U; i < len1; i++)
  {
    uint32_t *os = res;
    uint32_t x = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_bn_sub_mod_n_u64(
  uint32_t len1,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t c0 = 0ULL;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint64_t t1 = a[4U * i];
    uint64_t t20 = b[4U * i];
    uint64_t *res_i0 = res + 4U * i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, res_i0);
    uint64_t t10 = a[4U * i + 1U];
    uint64_t t21 = b[4U * i + 1U];
    uint64_t *res_i1 = res + 4U * i + 1U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t10, t21, res_i1);
    uint64_t t11 = a[4U * i + 2U];
    uint64_t t22 = b[4U * i + 2U];
    uint64_t *res_i2 = res + 4U * i + 2U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t22, res_i2);
    uint64_t t12 = a[4U * i + 3U];
    uint64_t t2 = b[4U * i + 3U];
    uint64_t *res_i = res + 4U * i + 3U;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    uint64_t *res_i = res + i;
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, res_i);
  }
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t tmp[len1];
  memset(tmp, 0U, len1 * sizeof (uint64_t));
  uint64_t c = 0ULL;
  for (uint32_t i = 0U; i < len1 / 4U; i++)
  {
    uint64_t t1 = res[4U * i];
    uint64_t t20 = n[4U * i];
    uint64_t *res_i0 = tmp + 4U * i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    uint64_t t10 = res[4U * i + 1U];
    uint64_t t21 = n[4U * i + 1U];
    uint64_t *res_i1 = tmp + 4U * i + 1U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
    uint64_t t11 = res[4U * i + 2U];
    uint64_t t22 = n[4U * i + 2U];
    uint64_t *res_i2 = tmp + 4U * i + 2U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
    uint64_t t12 = res[4U * i + 3U];
    uint64_t t2 = n[4U * i + 3U];
    uint64_t *res_i = tmp + 4U * i + 3U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
  }
  for (uint32_t i = len1 / 4U * 4U; i < len1; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
  }
  uint64_t c1 = c;
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t c2 = 0ULL - c00;
  for (uint32_t i = 0U; i < len1; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & tmp[i]) | (~c2 & res[i]);
    os[i] = x;
  }
}

uint32_t Hacl_Bignum_ModInvLimb_mod_inv_uint32(uint32_t n0)
{
  uint32_t alpha = 2147483648U;
  uint32_t beta = n0;
  uint32_t ub = 0U;
  uint32_t vb = 0U;
  ub = 1U;
  vb = 0U;
  for (uint32_t i = 0U; i < 32U; i++)
  {
    uint32_t us = ub;
    uint32_t vs = vb;
    uint32_t u_is_odd = 0U - (us & 1U);
    uint32_t beta_if_u_is_odd = beta & u_is_odd;
    ub = ((us ^ beta_if_u_is_odd) >> 1U) + (us & beta_if_u_is_odd);
    uint32_t alpha_if_u_is_odd = alpha & u_is_odd;
    vb = (vs >> 1U) + alpha_if_u_is_odd;
  }
  return vb;
}

uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0)
{
  uint64_t alpha = 9223372036854775808ULL;
  uint64_t beta = n0;
  uint64_t ub = 0ULL;
  uint64_t vb = 0ULL;
  ub = 1ULL;
  vb = 0ULL;
  for (uint32_t i = 0U; i < 64U; i++)
  {
    uint64_t us = ub;
    uint64_t vs = vb;
    uint64_t u_is_odd = 0ULL - (us & 1ULL);
    uint64_t beta_if_u_is_odd = beta & u_is_odd;
    ub = ((us ^ beta_if_u_is_odd) >> 1U) + (us & beta_if_u_is_odd);
    uint64_t alpha_if_u_is_odd = alpha & u_is_odd;
    vb = (vs >> 1U) + alpha_if_u_is_odd;
  }
  return vb;
}

uint32_t Hacl_Bignum_Montgomery_bn_check_modulus_u32(uint32_t len, uint32_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t one[len];
  memset(one, 0U, len * sizeof (uint32_t));
  memset(one, 0U, len * sizeof (uint32_t));
  one[0U] = 1U;
  uint32_t bit0 = n[0U] & 1U;
  uint32_t m0 = 0U - bit0;
  uint32_t acc = 0U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U)));
  }
  uint32_t m1 = acc;
  return m0 & m1;
}

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *res
)
{
  memset(res, 0U, len * sizeof (uint32_t));
  uint32_t i = nBits / 32U;
  uint32_t j = nBits % 32U;
  res[i] = res[i] | 1U << j;
  for (uint32_t i0 = 0U; i0 < 64U * len - nBits; i0++)
  {
    Hacl_Bignum_bn_add_mod_n_u32(len, n, res, res, res);
  }
}

static void
bn_mont_reduction_u32(uint32_t len, uint32_t *n, uint32_t nInv, uint32_t *c, uint32_t *res)
{
  uint32_t c0 = 0U;
  for (uint32_t i0 = 0U; i0 < len; i0++)
  {
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = 0U;
    for (uint32_t i = 0U; i < len / 4U; i++)
    {
      uint32_t a_i = n[4U * i];
      uint32_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[4U * i + 1U];
      uint32_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[4U * i + 2U];
      uint32_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[4U * i + 3U];
      uint32_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = len / 4U * 4U; i < len; i++)
    {
      uint32_t a_i = n[i];
      uint32_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + len + i0;
    uint32_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint32_t));
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint32_t));
  uint32_t c1 = 0U;
  for (uint32_t i = 0U; i < len / 4U; i++)
  {
    uint32_t t1 = res[4U * i];
    uint32_t t20 = n[4U * i];
    uint32_t *res_i0 = tmp + 4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t20, res_i0);
    uint32_t t10 = res[4U * i + 1U];
    uint32_t t21 = n[4U * i + 1U];
    uint32_t *res_i1 = tmp + 4U * i + 1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t10, t21, res_i1);
    uint32_t t11 = res[4U * i + 2U];
    uint32_t t22 = n[4U * i + 2U];
    uint32_t *res_i2 = tmp + 4U * i + 2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t11, t22, res_i2);
    uint32_t t12 = res[4U * i + 3U];
    uint32_t t2 = n[4U * i + 3U];
    uint32_t *res_i = tmp + 4U * i + 3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t12, t2, res_i);
  }
  for (uint32_t i = len / 4U * 4U; i < len; i++)
  {
    uint32_t t1 = res[i];
    uint32_t t2 = n[i];
    uint32_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u32(c1, t1, t2, res_i);
  }
  uint32_t c10 = c1;
  uint32_t c2 = c00 - c10;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t *os = res;
    uint32_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_Montgomery_bn_to_mont_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *r2,
  uint32_t *a,
  uint32_t *aM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, r2, tmp, c);
  bn_mont_reduction_u32(len, n, nInv, c, aM);
}

void
Hacl_Bignum_Montgomery_bn_from_mont_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *a
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t tmp[len + len];
  memset(tmp, 0U, (len + len) * sizeof (uint32_t));
  memcpy(tmp, aM, len * sizeof (uint32_t));
  bn_mont_reduction_u32(len, n, nInv_u64, tmp, a);
}

void
Hacl_Bignum_Montgomery_bn_mont_mul_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, aM, bM, tmp, c);
  bn_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

void
Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len, aM, tmp, c);
  bn_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

uint64_t Hacl_Bignum_Montgomery_bn_check_modulus_u64(uint32_t len, uint64_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t one[len];
  memset(one, 0U, len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  one[0U] = 1ULL;
  uint64_t bit0 = n[0U] & 1ULL;
  uint64_t m0 = 0ULL - bit0;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m1 = acc;
  return m0 & m1;
}

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *res
)
{
  memset(res, 0U, len * sizeof (uint64_t));
  uint32_t i = nBits / 64U;
  uint32_t j = nBits % 64U;
  res[i] = res[i] | 1ULL << j;
  for (uint32_t i0 = 0U; i0 < 128U * len - nBits; i0++)
  {
    Hacl_Bignum_bn_add_mod_n_u64(len, n, res, res, res);
  }
}

static void
bn_mont_reduction_u64(uint32_t len, uint64_t *n, uint64_t nInv, uint64_t *c, uint64_t *res)
{
  uint64_t c0 = 0ULL;
  for (uint32_t i0 = 0U; i0 < len; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = 0ULL;
    for (uint32_t i = 0U; i < len / 4U; i++)
    {
      uint64_t a_i = n[4U * i];
      uint64_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[4U * i + 1U];
      uint64_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[4U * i + 2U];
      uint64_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[4U * i + 3U];
      uint64_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = len / 4U * 4U; i < len; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + len + i0;
    uint64_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = 0ULL;
  for (uint32_t i = 0U; i < len / 4U; i++)
  {
    uint64_t t1 = res[4U * i];
    uint64_t t20 = n[4U * i];
    uint64_t *res_i0 = tmp + 4U * i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, res_i0);
    uint64_t t10 = res[4U * i + 1U];
    uint64_t t21 = n[4U * i + 1U];
    uint64_t *res_i1 = tmp + 4U * i + 1U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, res_i1);
    uint64_t t11 = res[4U * i + 2U];
    uint64_t t22 = n[4U * i + 2U];
    uint64_t *res_i2 = tmp + 4U * i + 2U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, res_i2);
    uint64_t t12 = res[4U * i + 3U];
    uint64_t t2 = n[4U * i + 3U];
    uint64_t *res_i = tmp + 4U * i + 3U;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, res_i);
  }
  for (uint32_t i = len / 4U * 4U; i < len; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    uint64_t *res_i = tmp + i;
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, res_i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = c00 - c10;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

void
Hacl_Bignum_Montgomery_bn_to_mont_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *r2,
  uint64_t *a,
  uint64_t *aM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, r2, tmp, c);
  bn_mont_reduction_u64(len, n, nInv, c, aM);
}

void
Hacl_Bignum_Montgomery_bn_from_mont_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *a
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t tmp[len + len];
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, aM, len * sizeof (uint64_t));
  bn_mont_reduction_u64(len, n, nInv_u64, tmp, a);
}

void
Hacl_Bignum_Montgomery_bn_mont_mul_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, aM, bM, tmp, c);
  bn_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

void
Hacl_Bignum_Montgomery_bn_mont_sqr_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, aM, tmp, c);
  bn_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

void
Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *c,
  uint32_t *res
)
{
  uint32_t c0 = 0U;
  for (uint32_t i0 = 0U; i0 < len; i0++)
  {
    uint32_t qj = nInv * c[i0];
    uint32_t *res_j0 = c + i0;
    uint32_t c1 = 0U;
    for (uint32_t i = 0U; i < len / 4U; i++)
    {
      uint32_t a_i = n[4U * i];
      uint32_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
      uint32_t a_i0 = n[4U * i + 1U];
      uint32_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
      uint32_t a_i1 = n[4U * i + 2U];
      uint32_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
      uint32_t a_i2 = n[4U * i + 3U];
      uint32_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = len / 4U * 4U; i < len; i++)
    {
      uint32_t a_i = n[i];
      uint32_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i);
    }
    uint32_t r = c1;
    uint32_t c10 = r;
    uint32_t *resb = c + len + i0;
    uint32_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint32_t));
  uint32_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint32_t));
  uint32_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len, res, n, tmp);
  KRML_MAYBE_UNUSED_VAR(c1);
  uint32_t m = 0U - c00;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t *os = res;
    uint32_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;
  }
}

static void
bn_almost_mont_mul_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, aM, bM, tmp, c);
  Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

static void
bn_almost_mont_sqr_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len, aM, tmp, c);
  Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(len, n, nInv_u64, c, resM);
}

void
Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *c,
  uint64_t *res
)
{
  uint64_t c0 = 0ULL;
  for (uint32_t i0 = 0U; i0 < len; i0++)
  {
    uint64_t qj = nInv * c[i0];
    uint64_t *res_j0 = c + i0;
    uint64_t c1 = 0ULL;
    for (uint32_t i = 0U; i < len / 4U; i++)
    {
      uint64_t a_i = n[4U * i];
      uint64_t *res_i0 = res_j0 + 4U * i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
      uint64_t a_i0 = n[4U * i + 1U];
      uint64_t *res_i1 = res_j0 + 4U * i + 1U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
      uint64_t a_i1 = n[4U * i + 2U];
      uint64_t *res_i2 = res_j0 + 4U * i + 2U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
      uint64_t a_i2 = n[4U * i + 3U];
      uint64_t *res_i = res_j0 + 4U * i + 3U;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    }
    for (uint32_t i = len / 4U * 4U; i < len; i++)
    {
      uint64_t a_i = n[i];
      uint64_t *res_i = res_j0 + i;
      c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    uint64_t *resb = c + len + i0;
    uint64_t res_j = c[len + i0];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, res_j, resb);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t c00 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len, res, n, tmp);
  KRML_MAYBE_UNUSED_VAR(c1);
  uint64_t m = 0ULL - c00;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (m & tmp[i]) | (~m & res[i]);
    os[i] = x;
  }
}

static void
bn_almost_mont_mul_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, aM, bM, tmp, c);
  Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

static void
bn_almost_mont_sqr_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *resM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, aM, tmp, c);
  Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(len, n, nInv_u64, c, resM);
}

uint32_t
Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t one[len];
  memset(one, 0U, len * sizeof (uint32_t));
  memset(one, 0U, len * sizeof (uint32_t));
  one[0U] = 1U;
  uint32_t bit0 = n[0U] & 1U;
  uint32_t m0 = 0U - bit0;
  uint32_t acc0 = 0U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(one[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U)));
  }
  uint32_t m10 = acc0;
  uint32_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 32U + 1U;
  }
  uint32_t m1;
  if (bBits < 32U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), bLen);
    uint32_t b2[bLen];
    memset(b2, 0U, bLen * sizeof (uint32_t));
    uint32_t i0 = bBits / 32U;
    uint32_t j = bBits % 32U;
    b2[i0] = b2[i0] | 1U << j;
    uint32_t acc = 0U;
    for (uint32_t i = 0U; i < bLen; i++)
    {
      uint32_t beq = FStar_UInt32_eq_mask(b[i], b2[i]);
      uint32_t blt = ~FStar_UInt32_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U)));
    }
    uint32_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = 0xFFFFFFFFU;
  }
  uint32_t acc = 0U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFU) | (~blt & 0U)));
  }
  uint32_t m2 = acc;
  uint32_t m = m1 & m2;
  return m00 & m;
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < 200U)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t aM[len];
    memset(aM, 0U, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM);
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t resM[len];
    memset(resM, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t ctx[len + len];
    memset(ctx, 0U, (len + len) * sizeof (uint32_t));
    memcpy(ctx, n, len * sizeof (uint32_t));
    memcpy(ctx + len, r2, len * sizeof (uint32_t));
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n, mu, ctx_r2, resM);
    for (uint32_t i = 0U; i < bBits; i++)
    {
      uint32_t i1 = i / 32U;
      uint32_t j = i % 32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & 1U;
      if (!(bit == 0U))
      {
        uint32_t *ctx_n0 = ctx;
        bn_almost_mont_mul_u32(len, ctx_n0, mu, resM, aM, resM);
      }
      uint32_t *ctx_n0 = ctx;
      bn_almost_mont_sqr_u32(len, ctx_n0, mu, aM, aM);
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t aM[len];
  memset(aM, 0U, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM);
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t resM[len];
  memset(resM, 0U, len * sizeof (uint32_t));
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 32U + 1U;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t ctx[len + len];
  memset(ctx, 0U, (len + len) * sizeof (uint32_t));
  memcpy(ctx, n, len * sizeof (uint32_t));
  memcpy(ctx + len, r2, len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 16U * len);
  uint32_t table[16U * len];
  memset(table, 0U, 16U * len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint32_t));
  uint32_t *t0 = table;
  uint32_t *t1 = table + len;
  uint32_t *ctx_n0 = ctx;
  uint32_t *ctx_r20 = ctx + len;
  Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, len * sizeof (uint32_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint32_t *t11 = table + (i + 1U) * len;
    uint32_t *ctx_n1 = ctx;
    bn_almost_mont_sqr_u32(len, ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * len, tmp, len * sizeof (uint32_t));
    uint32_t *t2 = table + (2U * i + 2U) * len;
    uint32_t *ctx_n = ctx;
    bn_almost_mont_mul_u32(len, ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * len, tmp, len * sizeof (uint32_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i = bBits / 4U * 4U;
    uint32_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, i, 4U);
    uint32_t bits_l32 = bits_c;
    const uint32_t *a_bits_l = table + bits_l32 * len;
    memcpy(resM, (uint32_t *)a_bits_l, len * sizeof (uint32_t));
  }
  else
  {
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n, mu, ctx_r2, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t tmp0[len];
  memset(tmp0, 0U, len * sizeof (uint32_t));
  for (uint32_t i = 0U; i < bBits / 4U; i++)
  {
    KRML_MAYBE_FOR4(i0,
      0U,
      4U,
      1U,
      uint32_t *ctx_n = ctx;
      bn_almost_mont_sqr_u32(len, ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i - 4U;
    uint32_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, k, 4U);
    uint32_t bits_l32 = bits_l;
    const uint32_t *a_bits_l = table + bits_l32 * len;
    memcpy(tmp0, (uint32_t *)a_bits_l, len * sizeof (uint32_t));
    uint32_t *ctx_n = ctx;
    bn_almost_mont_mul_u32(len, ctx_n, mu, resM, tmp0, resM);
  }
  Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  if (bBits < 200U)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t aM[len];
    memset(aM, 0U, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM);
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t resM[len];
    memset(resM, 0U, len * sizeof (uint32_t));
    KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
    uint32_t ctx[len + len];
    memset(ctx, 0U, (len + len) * sizeof (uint32_t));
    memcpy(ctx, n, len * sizeof (uint32_t));
    memcpy(ctx + len, r2, len * sizeof (uint32_t));
    uint32_t sw = 0U;
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n, mu, ctx_r2, resM);
    for (uint32_t i0 = 0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - 1U) / 32U;
      uint32_t j = (bBits - i0 - 1U) % 32U;
      uint32_t tmp = b[i1];
      uint32_t bit = tmp >> j & 1U;
      uint32_t sw1 = bit ^ sw;
      for (uint32_t i = 0U; i < len; i++)
      {
        uint32_t dummy = (0U - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;
      }
      uint32_t *ctx_n0 = ctx;
      bn_almost_mont_mul_u32(len, ctx_n0, mu, aM, resM, aM);
      uint32_t *ctx_n1 = ctx;
      bn_almost_mont_sqr_u32(len, ctx_n1, mu, resM, resM);
      sw = bit;
    }
    uint32_t sw0 = sw;
    for (uint32_t i = 0U; i < len; i++)
    {
      uint32_t dummy = (0U - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t aM[len];
  memset(aM, 0U, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM);
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t resM[len];
  memset(resM, 0U, len * sizeof (uint32_t));
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 32U + 1U;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t ctx[len + len];
  memset(ctx, 0U, (len + len) * sizeof (uint32_t));
  memcpy(ctx, n, len * sizeof (uint32_t));
  memcpy(ctx + len, r2, len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), 16U * len);
  uint32_t table[16U * len];
  memset(table, 0U, 16U * len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint32_t));
  uint32_t *t0 = table;
  uint32_t *t1 = table + len;
  uint32_t *ctx_n0 = ctx;
  uint32_t *ctx_r20 = ctx + len;
  Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, len * sizeof (uint32_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint32_t *t11 = table + (i + 1U) * len;
    uint32_t *ctx_n1 = ctx;
    bn_almost_mont_sqr_u32(len, ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * len, tmp, len * sizeof (uint32_t));
    uint32_t *t2 = table + (2U * i + 2U) * len;
    uint32_t *ctx_n = ctx;
    bn_almost_mont_mul_u32(len, ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * len, tmp, len * sizeof (uint32_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i0 = bBits / 4U * 4U;
    uint32_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, i0, 4U);
    memcpy(resM, (uint32_t *)(table + 0U * len), len * sizeof (uint32_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint32_t c = FStar_UInt32_eq_mask(bits_c, i1 + 1U);
      const uint32_t *res_j = table + (i1 + 1U) * len;
      for (uint32_t i = 0U; i < len; i++)
      {
        uint32_t *os = resM;
        uint32_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;
      });
  }
  else
  {
    uint32_t *ctx_n = ctx;
    uint32_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n, mu, ctx_r2, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t tmp0[len];
  memset(tmp0, 0U, len * sizeof (uint32_t));
  for (uint32_t i0 = 0U; i0 < bBits / 4U; i0++)
  {
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint32_t *ctx_n = ctx;
      bn_almost_mont_sqr_u32(len, ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i0 - 4U;
    uint32_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u32(bLen, b, k, 4U);
    memcpy(tmp0, (uint32_t *)(table + 0U * len), len * sizeof (uint32_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint32_t c = FStar_UInt32_eq_mask(bits_l, i1 + 1U);
      const uint32_t *res_j = table + (i1 + 1U) * len;
      for (uint32_t i = 0U; i < len; i++)
      {
        uint32_t *os = tmp0;
        uint32_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;
      });
    uint32_t *ctx_n = ctx;
    bn_almost_mont_mul_u32(len, ctx_n, mu, resM, tmp0, resM);
  }
  Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t r2[len];
  memset(r2, 0U, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(len, n, mu, r2, a, bBits, b, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t r2[len];
  memset(r2, 0U, len * sizeof (uint32_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(len, n, mu, r2, a, bBits, b, res);
}

uint64_t
Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t one[len];
  memset(one, 0U, len * sizeof (uint64_t));
  memset(one, 0U, len * sizeof (uint64_t));
  one[0U] = 1ULL;
  uint64_t bit0 = n[0U] & 1ULL;
  uint64_t m0 = 0ULL - bit0;
  uint64_t acc0 = 0ULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(one[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(one[i], n[i]);
    acc0 = (beq & acc0) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m10 = acc0;
  uint64_t m00 = m0 & m10;
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 64U + 1U;
  }
  uint64_t m1;
  if (bBits < 64U * bLen)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), bLen);
    uint64_t b2[bLen];
    memset(b2, 0U, bLen * sizeof (uint64_t));
    uint32_t i0 = bBits / 64U;
    uint32_t j = bBits % 64U;
    b2[i0] = b2[i0] | 1ULL << j;
    uint64_t acc = 0ULL;
    for (uint32_t i = 0U; i < bLen; i++)
    {
      uint64_t beq = FStar_UInt64_eq_mask(b[i], b2[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(b[i], b2[i]);
      acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
    }
    uint64_t res = acc;
    m1 = res;
  }
  else
  {
    m1 = 0xFFFFFFFFFFFFFFFFULL;
  }
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m2 = acc;
  uint64_t m = m1 & m2;
  return m00 & m;
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  if (bBits < 200U)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t aM[len];
    memset(aM, 0U, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM);
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t resM[len];
    memset(resM, 0U, len * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t ctx[len + len];
    memset(ctx, 0U, (len + len) * sizeof (uint64_t));
    memcpy(ctx, n, len * sizeof (uint64_t));
    memcpy(ctx + len, r2, len * sizeof (uint64_t));
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n, mu, ctx_r2, resM);
    for (uint32_t i = 0U; i < bBits; i++)
    {
      uint32_t i1 = i / 64U;
      uint32_t j = i % 64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & 1ULL;
      if (!(bit == 0ULL))
      {
        uint64_t *ctx_n0 = ctx;
        bn_almost_mont_mul_u64(len, ctx_n0, mu, resM, aM, resM);
      }
      uint64_t *ctx_n0 = ctx;
      bn_almost_mont_sqr_u64(len, ctx_n0, mu, aM, aM);
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t aM[len];
  memset(aM, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t resM[len];
  memset(resM, 0U, len * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 64U + 1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t ctx[len + len];
  memset(ctx, 0U, (len + len) * sizeof (uint64_t));
  memcpy(ctx, n, len * sizeof (uint64_t));
  memcpy(ctx + len, r2, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 16U * len);
  uint64_t table[16U * len];
  memset(table, 0U, 16U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t *t0 = table;
  uint64_t *t1 = table + len;
  uint64_t *ctx_n0 = ctx;
  uint64_t *ctx_r20 = ctx + len;
  Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, len * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint64_t *t11 = table + (i + 1U) * len;
    uint64_t *ctx_n1 = ctx;
    bn_almost_mont_sqr_u64(len, ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * len, tmp, len * sizeof (uint64_t));
    uint64_t *t2 = table + (2U * i + 2U) * len;
    uint64_t *ctx_n = ctx;
    bn_almost_mont_mul_u64(len, ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * len, tmp, len * sizeof (uint64_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i = bBits / 4U * 4U;
    uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, i, 4U);
    uint32_t bits_l32 = (uint32_t)bits_c;
    const uint64_t *a_bits_l = table + bits_l32 * len;
    memcpy(resM, (uint64_t *)a_bits_l, len * sizeof (uint64_t));
  }
  else
  {
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n, mu, ctx_r2, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp0[len];
  memset(tmp0, 0U, len * sizeof (uint64_t));
  for (uint32_t i = 0U; i < bBits / 4U; i++)
  {
    KRML_MAYBE_FOR4(i0,
      0U,
      4U,
      1U,
      uint64_t *ctx_n = ctx;
      bn_almost_mont_sqr_u64(len, ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, k, 4U);
    uint32_t bits_l32 = (uint32_t)bits_l;
    const uint64_t *a_bits_l = table + bits_l32 * len;
    memcpy(tmp0, (uint64_t *)a_bits_l, len * sizeof (uint64_t));
    uint64_t *ctx_n = ctx;
    bn_almost_mont_mul_u64(len, ctx_n, mu, resM, tmp0, resM);
  }
  Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  if (bBits < 200U)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t aM[len];
    memset(aM, 0U, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM);
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t resM[len];
    memset(resM, 0U, len * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
    uint64_t ctx[len + len];
    memset(ctx, 0U, (len + len) * sizeof (uint64_t));
    memcpy(ctx, n, len * sizeof (uint64_t));
    memcpy(ctx + len, r2, len * sizeof (uint64_t));
    uint64_t sw = 0ULL;
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n, mu, ctx_r2, resM);
    for (uint32_t i0 = 0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - 1U) / 64U;
      uint32_t j = (bBits - i0 - 1U) % 64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & 1ULL;
      uint64_t sw1 = bit ^ sw;
      for (uint32_t i = 0U; i < len; i++)
      {
        uint64_t dummy = (0ULL - sw1) & (resM[i] ^ aM[i]);
        resM[i] = resM[i] ^ dummy;
        aM[i] = aM[i] ^ dummy;
      }
      uint64_t *ctx_n0 = ctx;
      bn_almost_mont_mul_u64(len, ctx_n0, mu, aM, resM, aM);
      uint64_t *ctx_n1 = ctx;
      bn_almost_mont_sqr_u64(len, ctx_n1, mu, resM, resM);
      sw = bit;
    }
    uint64_t sw0 = sw;
    for (uint32_t i = 0U; i < len; i++)
    {
      uint64_t dummy = (0ULL - sw0) & (resM[i] ^ aM[i]);
      resM[i] = resM[i] ^ dummy;
      aM[i] = aM[i] ^ dummy;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM, res);
    return;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t aM[len];
  memset(aM, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM);
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t resM[len];
  memset(resM, 0U, len * sizeof (uint64_t));
  uint32_t bLen;
  if (bBits == 0U)
  {
    bLen = 1U;
  }
  else
  {
    bLen = (bBits - 1U) / 64U + 1U;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t ctx[len + len];
  memset(ctx, 0U, (len + len) * sizeof (uint64_t));
  memcpy(ctx, n, len * sizeof (uint64_t));
  memcpy(ctx + len, r2, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), 16U * len);
  uint64_t table[16U * len];
  memset(table, 0U, 16U * len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t *t0 = table;
  uint64_t *t1 = table + len;
  uint64_t *ctx_n0 = ctx;
  uint64_t *ctx_r20 = ctx + len;
  Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n0, mu, ctx_r20, t0);
  memcpy(t1, aM, len * sizeof (uint64_t));
  KRML_MAYBE_FOR7(i,
    0U,
    7U,
    1U,
    uint64_t *t11 = table + (i + 1U) * len;
    uint64_t *ctx_n1 = ctx;
    bn_almost_mont_sqr_u64(len, ctx_n1, mu, t11, tmp);
    memcpy(table + (2U * i + 2U) * len, tmp, len * sizeof (uint64_t));
    uint64_t *t2 = table + (2U * i + 2U) * len;
    uint64_t *ctx_n = ctx;
    bn_almost_mont_mul_u64(len, ctx_n, mu, aM, t2, tmp);
    memcpy(table + (2U * i + 3U) * len, tmp, len * sizeof (uint64_t)););
  if (bBits % 4U != 0U)
  {
    uint32_t i0 = bBits / 4U * 4U;
    uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, i0, 4U);
    memcpy(resM, (uint64_t *)(table + 0U * len), len * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_c, (uint64_t)(i1 + 1U));
      const uint64_t *res_j = table + (i1 + 1U) * len;
      for (uint32_t i = 0U; i < len; i++)
      {
        uint64_t *os = resM;
        uint64_t x = (c & res_j[i]) | (~c & resM[i]);
        os[i] = x;
      });
  }
  else
  {
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + len;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n, mu, ctx_r2, resM);
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp0[len];
  memset(tmp0, 0U, len * sizeof (uint64_t));
  for (uint32_t i0 = 0U; i0 < bBits / 4U; i0++)
  {
    KRML_MAYBE_FOR4(i,
      0U,
      4U,
      1U,
      uint64_t *ctx_n = ctx;
      bn_almost_mont_sqr_u64(len, ctx_n, mu, resM, resM););
    uint32_t k = bBits - bBits % 4U - 4U * i0 - 4U;
    uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, k, 4U);
    memcpy(tmp0, (uint64_t *)(table + 0U * len), len * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i1,
      0U,
      15U,
      1U,
      uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i1 + 1U));
      const uint64_t *res_j = table + (i1 + 1U) * len;
      for (uint32_t i = 0U; i < len; i++)
      {
        uint64_t *os = tmp0;
        uint64_t x = (c & res_j[i]) | (~c & tmp0[i]);
        os[i] = x;
      });
    uint64_t *ctx_n = ctx;
    bn_almost_mont_mul_u64(len, ctx_n, mu, resM, tmp0, resM);
  }
  Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t r2[len];
  memset(r2, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(len, n, mu, r2, a, bBits, b, res);
}

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t r2[len];
  memset(r2, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(len, n, mu, r2, a, bBits, b, res);
}

