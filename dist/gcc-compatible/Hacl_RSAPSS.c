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


#include "Hacl_RSAPSS.h"

inline void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    uint32_t resLen = aLen + aLen;
    memset(res, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i0 = (uint32_t)0U; i0 < aLen; i0++)
    {
      uint64_t uu____0 = b[i0];
      uint64_t *res_ = res + i0;
      uint64_t c = (uint64_t)0U;
      uint32_t k = aLen / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            a[(uint32_t)4U * i],
            uu____0,
            res_ + (uint32_t)4U * i);
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            a[(uint32_t)4U * i + (uint32_t)1U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            a[(uint32_t)4U * i + (uint32_t)2U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            a[(uint32_t)4U * i + (uint32_t)3U],
            uu____0,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < aLen; i++)
      {
        c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i], uu____0, res_ + i);
      }
      uint64_t r = c;
      res[aLen + i0] = r;
    }
    return;
  }
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + aLen2;
  uint64_t *b0 = b;
  uint64_t *b1 = b + aLen2;
  uint64_t *t0 = tmp;
  uint64_t *t1 = tmp + aLen2;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = aLen2 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t11 = a0[(uint32_t)4U * i];
    uint64_t t20 = a1[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t20, tmp_ + (uint32_t)4U * i);
    uint64_t t110 = a0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = a1[(uint32_t)4U * i + (uint32_t)1U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t110,
        t21,
        tmp_ + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = a0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = a1[(uint32_t)4U * i + (uint32_t)2U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t111,
        t22,
        tmp_ + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = a0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = a1[(uint32_t)4U * i + (uint32_t)3U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t112,
        t2,
        tmp_ + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < aLen2; i++)
  {
    uint64_t t11 = a0[i];
    uint64_t t2 = a1[i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t11, t2, tmp_ + i);
  }
  uint64_t c00 = c0;
  uint64_t c1 = (uint64_t)0U;
  uint32_t k1 = aLen2 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
  {
    uint64_t t11 = a1[(uint32_t)4U * i];
    uint64_t t20 = a0[(uint32_t)4U * i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t20, t0 + (uint32_t)4U * i);
    uint64_t t110 = a1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = a0[(uint32_t)4U * i + (uint32_t)1U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t110,
        t21,
        t0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = a1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = a0[(uint32_t)4U * i + (uint32_t)2U];
    c1 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c1,
        t111,
        t22,
        t0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = a1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = a0[(uint32_t)4U * i + (uint32_t)3U];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t112, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k1; i < aLen2; i++)
  {
    uint64_t t11 = a1[i];
    uint64_t t2 = a0[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t2, t0 + i);
  }
  uint64_t c10 = c1;
  for (uint32_t i = (uint32_t)0U; i < aLen2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c00) & t0[i]) | (~((uint64_t)0U - c00) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c01 = c00;
  uint64_t c2 = (uint64_t)0U;
  uint32_t k2 = aLen2 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
  {
    uint64_t t11 = b0[(uint32_t)4U * i];
    uint64_t t20 = b1[(uint32_t)4U * i];
    c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t11, t20, tmp_ + (uint32_t)4U * i);
    uint64_t t110 = b0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b1[(uint32_t)4U * i + (uint32_t)1U];
    c2 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c2,
        t110,
        t21,
        tmp_ + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = b0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b1[(uint32_t)4U * i + (uint32_t)2U];
    c2 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c2,
        t111,
        t22,
        tmp_ + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = b0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b1[(uint32_t)4U * i + (uint32_t)3U];
    c2 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c2,
        t112,
        t2,
        tmp_ + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k2; i < aLen2; i++)
  {
    uint64_t t11 = b0[i];
    uint64_t t2 = b1[i];
    c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t11, t2, tmp_ + i);
  }
  uint64_t c010 = c2;
  uint64_t c3 = (uint64_t)0U;
  uint32_t k3 = aLen2 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k3 / (uint32_t)4U; i++)
  {
    uint64_t t11 = b1[(uint32_t)4U * i];
    uint64_t t20 = b0[(uint32_t)4U * i];
    c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t11, t20, t1 + (uint32_t)4U * i);
    uint64_t t110 = b1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = b0[(uint32_t)4U * i + (uint32_t)1U];
    c3 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
        t110,
        t21,
        t1 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = b1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = b0[(uint32_t)4U * i + (uint32_t)2U];
    c3 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
        t111,
        t22,
        t1 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = b1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = b0[(uint32_t)4U * i + (uint32_t)3U];
    c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t112, t2, t1 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k3; i < aLen2; i++)
  {
    uint64_t t11 = b1[i];
    uint64_t t2 = b0[i];
    c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t11, t2, t1 + i);
  }
  uint64_t c11 = c3;
  for (uint32_t i = (uint32_t)0U; i < aLen2; i++)
  {
    uint64_t *os = t1;
    uint64_t x = (((uint64_t)0U - c010) & t1[i]) | (~((uint64_t)0U - c010) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c12 = c010;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(aLen2, t0, t1, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(aLen2, a0, b0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(aLen2, a1, b1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t *t67 = tmp + (uint32_t)3U * aLen;
  uint64_t c4 = (uint64_t)0U;
  uint32_t k4 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k4 / (uint32_t)4U; i++)
  {
    uint64_t t11 = r011[(uint32_t)4U * i];
    uint64_t t20 = r231[(uint32_t)4U * i];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t11, t20, t01 + (uint32_t)4U * i);
    uint64_t t110 = r011[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = r231[(uint32_t)4U * i + (uint32_t)1U];
    c4 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c4,
        t110,
        t21,
        t01 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = r011[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = r231[(uint32_t)4U * i + (uint32_t)2U];
    c4 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c4,
        t111,
        t22,
        t01 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = r011[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = r231[(uint32_t)4U * i + (uint32_t)3U];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t112, t2, t01 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k4; i < aLen; i++)
  {
    uint64_t t11 = r011[i];
    uint64_t t2 = r231[i];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t11, t2, t01 + i);
  }
  uint64_t c20 = c4;
  uint64_t c_sign = c01 ^ c12;
  uint64_t c5 = (uint64_t)0U;
  uint32_t k5 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k5 / (uint32_t)4U; i++)
  {
    uint64_t t11 = t01[(uint32_t)4U * i];
    uint64_t t20 = t231[(uint32_t)4U * i];
    c5 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c5, t11, t20, t67 + (uint32_t)4U * i);
    uint64_t t110 = t01[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t231[(uint32_t)4U * i + (uint32_t)1U];
    c5 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c5,
        t110,
        t21,
        t67 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = t01[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t231[(uint32_t)4U * i + (uint32_t)2U];
    c5 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c5,
        t111,
        t22,
        t67 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = t01[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t231[(uint32_t)4U * i + (uint32_t)3U];
    c5 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c5,
        t112,
        t2,
        t67 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k5; i < aLen; i++)
  {
    uint64_t t11 = t01[i];
    uint64_t t2 = t231[i];
    c5 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c5, t11, t2, t67 + i);
  }
  uint64_t c30 = c5;
  uint64_t c31 = c20 - c30;
  uint64_t c6 = (uint64_t)0U;
  uint32_t k6 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k6 / (uint32_t)4U; i++)
  {
    uint64_t t11 = t01[(uint32_t)4U * i];
    uint64_t t20 = t231[(uint32_t)4U * i];
    c6 = Lib_IntTypes_Intrinsics_add_carry_u64(c6, t11, t20, t45 + (uint32_t)4U * i);
    uint64_t t110 = t01[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t231[(uint32_t)4U * i + (uint32_t)1U];
    c6 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c6,
        t110,
        t21,
        t45 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = t01[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t231[(uint32_t)4U * i + (uint32_t)2U];
    c6 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c6,
        t111,
        t22,
        t45 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = t01[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t231[(uint32_t)4U * i + (uint32_t)3U];
    c6 = Lib_IntTypes_Intrinsics_add_carry_u64(c6, t112, t2, t45 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k6; i < aLen; i++)
  {
    uint64_t t11 = t01[i];
    uint64_t t2 = t231[i];
    c6 = Lib_IntTypes_Intrinsics_add_carry_u64(c6, t11, t2, t45 + i);
  }
  uint64_t c40 = c6;
  uint64_t c41 = c20 + c40;
  uint64_t mask = (uint64_t)0U - c_sign;
  for (uint32_t i = (uint32_t)0U; i < aLen; i++)
  {
    uint64_t *os = t45;
    uint64_t x = (mask & t45[i]) | (~mask & t67[i]);
    os[i] = x;
  }
  uint64_t c50 = (mask & c41) | (~mask & c31);
  uint32_t aLen21 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen21;
  uint64_t c7 = (uint64_t)0U;
  uint32_t k7 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k7 / (uint32_t)4U; i++)
  {
    uint64_t t11 = r0[(uint32_t)4U * i];
    uint64_t t20 = t45[(uint32_t)4U * i];
    c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t11, t20, r0 + (uint32_t)4U * i);
    uint64_t t110 = r0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t45[(uint32_t)4U * i + (uint32_t)1U];
    c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t110, t21, r0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = r0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t45[(uint32_t)4U * i + (uint32_t)2U];
    c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t111, t22, r0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = r0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t45[(uint32_t)4U * i + (uint32_t)3U];
    c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t112, t2, r0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k7; i < aLen; i++)
  {
    uint64_t t11 = r0[i];
    uint64_t t2 = t45[i];
    c7 = Lib_IntTypes_Intrinsics_add_carry_u64(c7, t11, t2, r0 + i);
  }
  uint64_t r10 = c7;
  uint64_t c60 = r10;
  uint64_t c70 = c50 + c60;
  uint64_t c71 = c70;
  uint64_t *r = res + aLen + aLen21;
  uint64_t *a01 = r;
  uint64_t *res0 = r;
  uint64_t c8 = (uint64_t)0U;
  uint32_t k8 = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < k8 / (uint32_t)4U; i++)
  {
    uint64_t t11 = a01[(uint32_t)4U * i];
    uint64_t t20 = (&c71)[(uint32_t)4U * i];
    c8 = Lib_IntTypes_Intrinsics_add_carry_u64(c8, t11, t20, res0 + (uint32_t)4U * i);
    uint64_t t110 = a01[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = (&c71)[(uint32_t)4U * i + (uint32_t)1U];
    c8 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c8,
        t110,
        t21,
        res0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t111 = a01[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = (&c71)[(uint32_t)4U * i + (uint32_t)2U];
    c8 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c8,
        t111,
        t22,
        res0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t112 = a01[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = (&c71)[(uint32_t)4U * i + (uint32_t)3U];
    c8 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c8,
        t112,
        t2,
        res0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k8; i < (uint32_t)1U; i++)
  {
    uint64_t t11 = a01[i];
    uint64_t t2 = (&c71)[i];
    c8 = Lib_IntTypes_Intrinsics_add_carry_u64(c8, t11, t2, res0 + i);
  }
  uint64_t c011 = c8;
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen21))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen21) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c011;
    uint32_t k = rLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t11 = a11[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res1 + (uint32_t)4U * i);
      uint64_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_add_carry_u64(c,
          t110,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_add_carry_u64(c,
          t111,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_add_carry_u64(c,
          t112,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < rLen; i++)
    {
      uint64_t t11 = a11[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res1 + i);
    }
    uint64_t c110 = c;
    r1 = c110;
  }
  else
  {
    r1 = c011;
  }
  uint64_t c80 = r1;
  uint64_t c = c80;
  uint64_t c9 = c;
}

inline void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    uint32_t resLen = aLen + aLen;
    memset(res, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i0 = (uint32_t)0U; i0 < aLen; i0++)
    {
      uint64_t *uu____0 = a;
      uint64_t uu____1 = a[i0];
      uint64_t *res_ = res + i0;
      uint64_t c = (uint64_t)0U;
      uint32_t k = i0 / (uint32_t)4U * (uint32_t)4U;
      for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
      {
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i],
            uu____1,
            res_ + (uint32_t)4U * i);
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i + (uint32_t)1U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)1U);
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i + (uint32_t)2U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)2U);
        c =
          Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c,
            uu____0[(uint32_t)4U * i + (uint32_t)3U],
            uu____1,
            res_ + (uint32_t)4U * i + (uint32_t)3U);
      }
      for (uint32_t i = k; i < i0; i++)
      {
        c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, uu____0[i], uu____1, res_ + i);
      }
      uint64_t r = c;
      res[i0 + i0] = r;
    }
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = res[(uint32_t)4U * i];
      uint64_t t20 = res[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res + (uint32_t)4U * i);
      uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = res[(uint32_t)4U * i + (uint32_t)1U];
      c0 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c0,
          t10,
          t21,
          res + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = res[(uint32_t)4U * i + (uint32_t)2U];
      c0 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c0,
          t11,
          t22,
          res + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = res[(uint32_t)4U * i + (uint32_t)3U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < resLen; i++)
    {
      uint64_t t1 = res[i];
      uint64_t t2 = res[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
    }
    uint64_t uu____2 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
    uint64_t tmp1[resLen];
    memset(tmp1, 0U, resLen * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < aLen; i++)
    {
      FStar_UInt128_uint128 a2 = FStar_UInt128_mul_wide(a[i], a[i]);
      tmp1[(uint32_t)2U * i] = FStar_UInt128_uint128_to_uint64(a2);
      tmp1[(uint32_t)2U * i + (uint32_t)1U] =
        FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(a2, (uint32_t)64U));
    }
    uint64_t c = (uint64_t)0U;
    uint32_t k = resLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = res[(uint32_t)4U * i];
      uint64_t t20 = tmp1[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res + (uint32_t)4U * i);
      uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = tmp1[(uint32_t)4U * i + (uint32_t)1U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = tmp1[(uint32_t)4U * i + (uint32_t)2U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = tmp1[(uint32_t)4U * i + (uint32_t)3U];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < resLen; i++)
    {
      uint64_t t1 = res[i];
      uint64_t t2 = tmp1[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res + i);
    }
    uint64_t uu____3 = c;
    return;
  }
  uint32_t aLen2 = aLen / (uint32_t)2U;
  uint64_t *a0 = a;
  uint64_t *a1 = a + aLen2;
  uint64_t *t0 = tmp;
  uint64_t *tmp_ = tmp + aLen;
  uint64_t c0 = (uint64_t)0U;
  uint32_t k0 = aLen2 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a0[(uint32_t)4U * i];
    uint64_t t20 = a1[(uint32_t)4U * i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t20, tmp_ + (uint32_t)4U * i);
    uint64_t t10 = a0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = a1[(uint32_t)4U * i + (uint32_t)1U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t10,
        t21,
        tmp_ + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = a1[(uint32_t)4U * i + (uint32_t)2U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t11,
        t22,
        tmp_ + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = a1[(uint32_t)4U * i + (uint32_t)3U];
    c0 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c0,
        t12,
        t2,
        tmp_ + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k0; i < aLen2; i++)
  {
    uint64_t t1 = a0[i];
    uint64_t t2 = a1[i];
    c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c0, t1, t2, tmp_ + i);
  }
  uint64_t c00 = c0;
  uint64_t c1 = (uint64_t)0U;
  uint32_t k1 = aLen2 / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k1 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a1[(uint32_t)4U * i];
    uint64_t t20 = a0[(uint32_t)4U * i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t20, t0 + (uint32_t)4U * i);
    uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = a0[(uint32_t)4U * i + (uint32_t)1U];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t10, t21, t0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = a0[(uint32_t)4U * i + (uint32_t)2U];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t11, t22, t0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = a0[(uint32_t)4U * i + (uint32_t)3U];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t12, t2, t0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k1; i < aLen2; i++)
  {
    uint64_t t1 = a1[i];
    uint64_t t2 = a0[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, t0 + i);
  }
  uint64_t c10 = c1;
  for (uint32_t i = (uint32_t)0U; i < aLen2; i++)
  {
    uint64_t *os = t0;
    uint64_t x = (((uint64_t)0U - c00) & t0[i]) | (~((uint64_t)0U - c00) & tmp_[i]);
    os[i] = x;
  }
  uint64_t c01 = c00;
  uint64_t *t23 = tmp + aLen;
  uint64_t *tmp1 = tmp + aLen + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_(aLen2, t0, tmp1, t23);
  uint64_t *r01 = res;
  uint64_t *r23 = res + aLen;
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_(aLen2, a0, tmp1, r01);
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_(aLen2, a1, tmp1, r23);
  uint64_t *r011 = res;
  uint64_t *r231 = res + aLen;
  uint64_t *t01 = tmp;
  uint64_t *t231 = tmp + aLen;
  uint64_t *t45 = tmp + (uint32_t)2U * aLen;
  uint64_t c2 = (uint64_t)0U;
  uint32_t k2 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k2 / (uint32_t)4U; i++)
  {
    uint64_t t1 = r011[(uint32_t)4U * i];
    uint64_t t20 = r231[(uint32_t)4U * i];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t20, t01 + (uint32_t)4U * i);
    uint64_t t10 = r011[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = r231[(uint32_t)4U * i + (uint32_t)1U];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t10, t21, t01 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = r011[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = r231[(uint32_t)4U * i + (uint32_t)2U];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t11, t22, t01 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = r011[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = r231[(uint32_t)4U * i + (uint32_t)3U];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t12, t2, t01 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k2; i < aLen; i++)
  {
    uint64_t t1 = r011[i];
    uint64_t t2 = r231[i];
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t2, t01 + i);
  }
  uint64_t c20 = c2;
  uint64_t c3 = (uint64_t)0U;
  uint32_t k3 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k3 / (uint32_t)4U; i++)
  {
    uint64_t t1 = t01[(uint32_t)4U * i];
    uint64_t t20 = t231[(uint32_t)4U * i];
    c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t20, t45 + (uint32_t)4U * i);
    uint64_t t10 = t01[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t231[(uint32_t)4U * i + (uint32_t)1U];
    c3 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
        t10,
        t21,
        t45 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = t01[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t231[(uint32_t)4U * i + (uint32_t)2U];
    c3 =
      Lib_IntTypes_Intrinsics_sub_borrow_u64(c3,
        t11,
        t22,
        t45 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = t01[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t231[(uint32_t)4U * i + (uint32_t)3U];
    c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t12, t2, t45 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k3; i < aLen; i++)
  {
    uint64_t t1 = t01[i];
    uint64_t t2 = t231[i];
    c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t2, t45 + i);
  }
  uint64_t c30 = c3;
  uint64_t c5 = c20 - c30;
  uint32_t aLen21 = aLen / (uint32_t)2U;
  uint64_t *r0 = res + aLen21;
  uint64_t c4 = (uint64_t)0U;
  uint32_t k4 = aLen / (uint32_t)4U * (uint32_t)4U;
  for (uint32_t i = (uint32_t)0U; i < k4 / (uint32_t)4U; i++)
  {
    uint64_t t1 = r0[(uint32_t)4U * i];
    uint64_t t20 = t45[(uint32_t)4U * i];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t1, t20, r0 + (uint32_t)4U * i);
    uint64_t t10 = r0[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = t45[(uint32_t)4U * i + (uint32_t)1U];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t10, t21, r0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = r0[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = t45[(uint32_t)4U * i + (uint32_t)2U];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t11, t22, r0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = r0[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = t45[(uint32_t)4U * i + (uint32_t)3U];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t12, t2, r0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k4; i < aLen; i++)
  {
    uint64_t t1 = r0[i];
    uint64_t t2 = t45[i];
    c4 = Lib_IntTypes_Intrinsics_add_carry_u64(c4, t1, t2, r0 + i);
  }
  uint64_t r10 = c4;
  uint64_t c6 = r10;
  uint64_t c7 = c5 + c6;
  uint64_t c71 = c7;
  uint64_t *r = res + aLen + aLen21;
  uint64_t *a01 = r;
  uint64_t *res0 = r;
  uint64_t c8 = (uint64_t)0U;
  uint32_t k5 = (uint32_t)0U;
  for (uint32_t i = (uint32_t)0U; i < k5 / (uint32_t)4U; i++)
  {
    uint64_t t1 = a01[(uint32_t)4U * i];
    uint64_t t20 = (&c71)[(uint32_t)4U * i];
    c8 = Lib_IntTypes_Intrinsics_add_carry_u64(c8, t1, t20, res0 + (uint32_t)4U * i);
    uint64_t t10 = a01[(uint32_t)4U * i + (uint32_t)1U];
    uint64_t t21 = (&c71)[(uint32_t)4U * i + (uint32_t)1U];
    c8 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c8,
        t10,
        t21,
        res0 + (uint32_t)4U * i + (uint32_t)1U);
    uint64_t t11 = a01[(uint32_t)4U * i + (uint32_t)2U];
    uint64_t t22 = (&c71)[(uint32_t)4U * i + (uint32_t)2U];
    c8 =
      Lib_IntTypes_Intrinsics_add_carry_u64(c8,
        t11,
        t22,
        res0 + (uint32_t)4U * i + (uint32_t)2U);
    uint64_t t12 = a01[(uint32_t)4U * i + (uint32_t)3U];
    uint64_t t2 = (&c71)[(uint32_t)4U * i + (uint32_t)3U];
    c8 = Lib_IntTypes_Intrinsics_add_carry_u64(c8, t12, t2, res0 + (uint32_t)4U * i + (uint32_t)3U);
  }
  for (uint32_t i = k5; i < (uint32_t)1U; i++)
  {
    uint64_t t1 = a01[i];
    uint64_t t2 = (&c71)[i];
    c8 = Lib_IntTypes_Intrinsics_add_carry_u64(c8, t1, t2, res0 + i);
  }
  uint64_t c010 = c8;
  uint64_t r1;
  if ((uint32_t)1U < aLen + aLen - (aLen + aLen21))
  {
    uint32_t rLen = aLen + aLen - (aLen + aLen21) - (uint32_t)1U;
    uint64_t *a11 = r + (uint32_t)1U;
    uint64_t *res1 = r + (uint32_t)1U;
    uint64_t c = c010;
    uint32_t k = rLen / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      uint64_t t1 = a11[(uint32_t)4U * i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res1 + (uint32_t)4U * i);
      uint64_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
      c =
        Lib_IntTypes_Intrinsics_add_carry_u64(c,
          t10,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
      c =
        Lib_IntTypes_Intrinsics_add_carry_u64(c,
          t11,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
      c =
        Lib_IntTypes_Intrinsics_add_carry_u64(c,
          t12,
          (uint64_t)0U,
          res1 + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < rLen; i++)
    {
      uint64_t t1 = a11[i];
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res1 + i);
    }
    uint64_t c11 = c;
    r1 = c11;
  }
  else
  {
    r1 = c010;
  }
  uint64_t c80 = r1;
  uint64_t c = c80;
  uint64_t c9 = c;
}

static void precomp_runtime(uint32_t len, uint32_t modBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, len * sizeof (uint64_t));
  Hacl_Bignum_bn_bit_set(len, res, modBits - (uint32_t)1U);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)128U * len + (uint32_t)1U - modBits; i0++)
  {
    uint64_t c0 = (uint64_t)0U;
    uint32_t k0 = len / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k0 / (uint32_t)4U; i++)
    {
      uint64_t t1 = res[(uint32_t)4U * i];
      uint64_t t20 = res[(uint32_t)4U * i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t20, res + (uint32_t)4U * i);
      uint64_t t10 = res[(uint32_t)4U * i + (uint32_t)1U];
      uint64_t t21 = res[(uint32_t)4U * i + (uint32_t)1U];
      c0 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c0,
          t10,
          t21,
          res + (uint32_t)4U * i + (uint32_t)1U);
      uint64_t t11 = res[(uint32_t)4U * i + (uint32_t)2U];
      uint64_t t22 = res[(uint32_t)4U * i + (uint32_t)2U];
      c0 =
        Lib_IntTypes_Intrinsics_add_carry_u64(c0,
          t11,
          t22,
          res + (uint32_t)4U * i + (uint32_t)2U);
      uint64_t t12 = res[(uint32_t)4U * i + (uint32_t)3U];
      uint64_t t2 = res[(uint32_t)4U * i + (uint32_t)3U];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t12, t2, res + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k0; i < len; i++)
    {
      uint64_t t1 = res[i];
      uint64_t t2 = res[i];
      c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
    }
    uint64_t c00 = c0;
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t tmp[len];
    memset(tmp, 0U, len * sizeof (uint64_t));
    uint64_t c = (uint64_t)0U;
    uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
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
    for (uint32_t i = k; i < len; i++)
    {
      uint64_t t1 = res[i];
      uint64_t t2 = n[i];
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
    }
    uint64_t c1 = c;
    uint64_t c2 = c00 - c1;
    for (uint32_t i = (uint32_t)0U; i < len; i++)
    {
      uint64_t *os = res;
      uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
      os[i] = x;
    }
  }
}

static void
mont_reduction_runtime(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *c,
  uint64_t *res
)
{
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i0 = (uint32_t)0U; i0 < len; i0++)
  {
    uint64_t qj = nInv_u64 * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
    for (uint32_t i = (uint32_t)0U; i < k / (uint32_t)4U; i++)
    {
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i],
          qj,
          res_ + (uint32_t)4U * i);
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i + (uint32_t)1U],
          qj,
          res_ + (uint32_t)4U * i + (uint32_t)1U);
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i + (uint32_t)2U],
          qj,
          res_ + (uint32_t)4U * i + (uint32_t)2U);
      c1 =
        Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1,
          n[(uint32_t)4U * i + (uint32_t)3U],
          qj,
          res_ + (uint32_t)4U * i + (uint32_t)3U);
    }
    for (uint32_t i = k; i < len; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n[i], qj, res_ + i);
    }
    uint64_t r = c1;
    uint64_t c10 = r;
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, c10, c[len + i0], c + len + i0);
  }
  memcpy(res, c + len, (len + len - len) * sizeof (uint64_t));
  uint64_t uu____0 = c0;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t tmp[len];
  memset(tmp, 0U, len * sizeof (uint64_t));
  uint64_t c1 = (uint64_t)0U;
  uint32_t k = len / (uint32_t)4U * (uint32_t)4U;
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
  for (uint32_t i = k; i < len; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c1 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c1, t1, t2, tmp + i);
  }
  uint64_t c10 = c1;
  uint64_t c2 = uu____0 - c10;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static void
to_runtime(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *r2,
  uint64_t *a,
  uint64_t *aM
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(len, a, r2, tmp, c);
  mont_reduction_runtime(len, n, nInv_u64, c, aM);
}

static void
from_runtime(uint32_t len, uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *a)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t tmp[len + len];
  memset(tmp, 0U, (len + len) * sizeof (uint64_t));
  memcpy(tmp, aM, len * sizeof (uint64_t));
  mont_reduction_runtime(len, n, nInv_u64, tmp, a);
}

static void
mul_runtime(
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
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_(len, aM, bM, tmp, c);
  mont_reduction_runtime(len, n, nInv_u64, c, resM);
}

static void
sqr_runtime(uint32_t len, uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *resM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t c[len + len];
  memset(c, 0U, (len + len) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U * len);
  uint64_t tmp[(uint32_t)4U * len];
  memset(tmp, 0U, (uint32_t)4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_(len, aM, tmp, c);
  mont_reduction_runtime(len, n, nInv_u64, c, resM);
}

static inline uint32_t hash_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return (uint32_t)16U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return (uint32_t)20U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return (uint32_t)28U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (uint32_t)32U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (uint32_t)48U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (uint32_t)64U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void
hash(Spec_Hash_Definitions_hash_alg a, uint8_t *mHash, uint32_t msgLen, uint8_t *msg)
{
  switch (a)
  {
    case Spec_Hash_Definitions_SHA2_256:
      {
        Hacl_Hash_SHA2_hash_256(msg, msgLen, mHash);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(msg, msgLen, mHash);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(msg, msgLen, mHash);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static inline void
mgf_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t len,
  uint8_t *mgfseed,
  uint32_t maskLen,
  uint8_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), len + (uint32_t)4U);
  uint8_t mgfseed_counter[len + (uint32_t)4U];
  memset(mgfseed_counter, 0U, (len + (uint32_t)4U) * sizeof (uint8_t));
  memcpy(mgfseed_counter, mgfseed, len * sizeof (uint8_t));
  uint32_t hLen = hash_len(a);
  uint32_t n = (maskLen - (uint32_t)1U) / hLen + (uint32_t)1U;
  uint32_t accLen = n * hLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), accLen);
  uint8_t acc[accLen];
  memset(acc, 0U, accLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < n; i++)
  {
    uint8_t *uu____0 = acc + i * hLen;
    uint8_t *uu____1 = mgfseed_counter + len;
    uu____1[0U] = (uint8_t)(i >> (uint32_t)24U);
    uu____1[1U] = (uint8_t)(i >> (uint32_t)16U);
    uu____1[2U] = (uint8_t)(i >> (uint32_t)8U);
    uu____1[3U] = (uint8_t)i;
    hash(a, uu____0, len + (uint32_t)4U, mgfseed_counter);
  }
  memcpy(res, acc, maskLen * sizeof (uint8_t));
}

static void
bn_mod_exp_loop_runtime(
  uint32_t nLen,
  uint64_t *n,
  uint64_t nInv_u64,
  uint32_t bBits,
  uint32_t bLen,
  uint64_t *b,
  uint64_t *aM,
  uint64_t *accM
)
{
  for (uint32_t i = (uint32_t)0U; i < bBits; i++)
  {
    if (Hacl_Bignum_bn_is_bit_set(bLen, b, i))
    {
      mul_runtime(nLen, n, nInv_u64, aM, accM, accM);
    }
    sqr_runtime(nLen, n, nInv_u64, aM, aM);
  }
}

static inline void
bn_mod_exp(
  uint32_t modBits,
  uint32_t nLen,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t acc[nLen];
  memset(acc, 0U, nLen * sizeof (uint64_t));
  memset(acc, 0U, nLen * sizeof (uint64_t));
  acc[0U] = (uint64_t)1U;
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t r2[nLen];
  memset(r2, 0U, nLen * sizeof (uint64_t));
  precomp_runtime(nLen, modBits, n, r2);
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t aM[nLen];
  memset(aM, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t accM[nLen];
  memset(accM, 0U, nLen * sizeof (uint64_t));
  to_runtime(nLen, n, nInv_u64, r2, a, aM);
  to_runtime(nLen, n, nInv_u64, r2, acc, accM);
  bn_mod_exp_loop_runtime(nLen, n, nInv_u64, bBits, bLen, b, aM, accM);
  from_runtime(nLen, n, nInv_u64, accM, res);
}

static inline void xor_bytes(uint32_t len, uint8_t *b1, uint8_t *b2)
{
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint8_t *os = b1;
    uint8_t x = b1[i] ^ b2[i];
    os[i] = x;
  }
}

static inline void
pss_encode(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint32_t hLen = hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  uint8_t m1Hash[hLen];
  memset(m1Hash, 0U, hLen * sizeof (uint8_t));
  uint32_t m1Len = (uint32_t)8U + hLen + sLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t m1[m1Len];
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + (uint32_t)8U, msgLen, msg);
  memcpy(m1 + (uint32_t)8U + hLen, salt, sLen * sizeof (uint8_t));
  hash(a, m1Hash, m1Len, m1);
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t dbLen = emLen - hLen - (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t db[dbLen];
  memset(db, 0U, dbLen * sizeof (uint8_t));
  uint32_t last_before_salt = dbLen - sLen - (uint32_t)1U;
  db[last_before_salt] = (uint8_t)1U;
  memcpy(db + last_before_salt + (uint32_t)1U, salt, sLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t dbMask[dbLen];
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
  xor_bytes(dbLen, db, dbMask);
  uint32_t msBits = emBits % (uint32_t)8U;
  if (msBits > (uint32_t)0U)
  {
    db[0U] = db[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits);
  }
  memcpy(em, db, dbLen * sizeof (uint8_t));
  memcpy(em + dbLen, m1Hash, hLen * sizeof (uint8_t));
  em[emLen - (uint32_t)1U] = (uint8_t)0xbcU;
}

static inline bool
pss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t sLen,
  uint32_t msgLen,
  uint8_t *msg,
  uint32_t emBits,
  uint8_t *em
)
{
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t msBits = emBits % (uint32_t)8U;
  uint8_t em_0;
  if (msBits > (uint32_t)0U)
  {
    em_0 = em[0U] & (uint8_t)0xffU << msBits;
  }
  else
  {
    em_0 = (uint8_t)0U;
  }
  uint8_t em_last = em[emLen - (uint32_t)1U];
  if (emLen < sLen + hash_len(a) + (uint32_t)2U)
  {
    return false;
  }
  if (!(em_last == (uint8_t)0xbcU && em_0 == (uint8_t)0U))
  {
    return false;
  }
  uint32_t emLen1 = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t hLen = hash_len(a);
  KRML_CHECK_SIZE(sizeof (uint8_t), hLen);
  uint8_t m1Hash0[hLen];
  memset(m1Hash0, 0U, hLen * sizeof (uint8_t));
  uint32_t dbLen = emLen1 - hLen - (uint32_t)1U;
  uint8_t *maskedDB = em;
  uint8_t *m1Hash = em + dbLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), dbLen);
  uint8_t dbMask[dbLen];
  memset(dbMask, 0U, dbLen * sizeof (uint8_t));
  mgf_hash(a, hLen, m1Hash, dbLen, dbMask);
  xor_bytes(dbLen, dbMask, maskedDB);
  uint32_t msBits1 = emBits % (uint32_t)8U;
  if (msBits1 > (uint32_t)0U)
  {
    dbMask[0U] = dbMask[0U] & (uint8_t)0xffU >> ((uint32_t)8U - msBits1);
  }
  uint32_t padLen = emLen1 - sLen - hLen - (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), padLen);
  uint8_t pad2[padLen];
  memset(pad2, 0U, padLen * sizeof (uint8_t));
  pad2[padLen - (uint32_t)1U] = (uint8_t)0x01U;
  uint8_t *pad = dbMask;
  uint8_t *salt = dbMask + padLen;
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < padLen; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(pad[i], pad2[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  if (!(z == (uint8_t)255U))
  {
    return false;
  }
  uint32_t m1Len = (uint32_t)8U + hLen + sLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), m1Len);
  uint8_t m1[m1Len];
  memset(m1, 0U, m1Len * sizeof (uint8_t));
  hash(a, m1 + (uint32_t)8U, msgLen, msg);
  memcpy(m1 + (uint32_t)8U + hLen, salt, sLen * sizeof (uint8_t));
  hash(a, m1Hash0, m1Len, m1);
  uint8_t res0 = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < hLen; i++)
  {
    uint8_t uu____1 = FStar_UInt8_eq_mask(m1Hash0[i], m1Hash[i]);
    res0 = uu____1 & res0;
  }
  uint8_t z0 = res0;
  return z0 == (uint8_t)255U;
}

void
Hacl_RSAPSS_rsapss_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t sLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint32_t eLen = (eBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = skey;
  uint64_t *d = skey + nLen + eLen;
  uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t emBits = modBits - (uint32_t)1U;
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
  uint8_t em[emLen];
  memset(em, 0U, emLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t m[nLen];
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t s[nLen];
  memset(s, 0U, nLen * sizeof (uint64_t));
  pss_encode(a, sLen, salt, msgLen, msg, emBits, em);
  Hacl_Bignum_Convert_bn_from_bytes_be(emLen, em, m);
  bn_mod_exp(modBits, nLen, n, m, dBits, d, s);
  Hacl_Bignum_Convert_bn_to_bytes_be(k, s, sgnt);
}

bool
Hacl_RSAPSS_rsapss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t sLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
)
{
  uint32_t nLen = (modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t *n = pkey;
  uint64_t *e = pkey + nLen;
  uint32_t k = (modBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t emBits = modBits - (uint32_t)1U;
  uint32_t emLen = (emBits - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), emLen);
  uint8_t em[emLen];
  memset(em, 0U, emLen * sizeof (uint8_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t m[nLen];
  memset(m, 0U, nLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), nLen);
  uint64_t s[nLen];
  memset(s, 0U, nLen * sizeof (uint64_t));
  Hacl_Bignum_Convert_bn_from_bytes_be(k, sgnt, s);
  if (Hacl_Bignum_bn_is_less(nLen, s, n))
  {
    bn_mod_exp(modBits, nLen, n, s, eBits, e, m);
    bool ite;
    if (!((modBits - (uint32_t)1U) % (uint32_t)8U == (uint32_t)0U))
    {
      ite = true;
    }
    else
    {
      ite =
        !Hacl_Bignum_bn_is_bit_set((modBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U,
          m,
          modBits - (uint32_t)1U);
    }
    if (ite)
    {
      uint64_t *m1 = m;
      Hacl_Bignum_Convert_bn_to_bytes_be(emLen, m1, em);
      return pss_verify(a, sLen, msgLen, msg, emBits, em);
    }
    return false;
  }
  return false;
}

inline void Hacl_Bignum_Convert_bn_from_bytes_be(uint32_t len, uint8_t *b, uint64_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
}

inline void Hacl_Bignum_Convert_bn_from_bytes_le(uint32_t len, uint8_t *b, uint64_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U; i++)
  {
    uint64_t *os = res;
    uint8_t *bj = tmp + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
}

inline void Hacl_Bignum_Convert_bn_to_bytes_be(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * (uint32_t)8U, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
}

inline void Hacl_Bignum_Convert_bn_to_bytes_le(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_le(tmp + i * (uint32_t)8U, b[i]);
  }
  memcpy(res, tmp, len * sizeof (uint8_t));
}

