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

inline uint64_t
Hacl_Bignum_Base_mul_wide_add2_u64(uint64_t a, uint64_t b, uint64_t c_in, uint64_t *out)
{
  uint64_t out0 = out[0U];
  FStar_UInt128_uint128
  res =
    FStar_UInt128_add(FStar_UInt128_add(FStar_UInt128_mul_wide(a, b),
        FStar_UInt128_uint64_to_uint128(c_in)),
      FStar_UInt128_uint64_to_uint128(out0));
  out[0U] = FStar_UInt128_uint128_to_uint64(res);
  return FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res, (uint32_t)64U));
}

inline uint64_t Hacl_Bignum_Lib_bn_get_top_index_u64(uint32_t len, uint64_t *b)
{
  uint64_t priv = (uint64_t)0U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < len; i++)
    {
      uint64_t mask = FStar_UInt64_eq_mask(b[i], (uint64_t)0U);
      priv = (mask & priv) | (~mask & (uint64_t)i);
    }
  }
  return priv;
}

static inline uint64_t
bn_sub_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a[(uint32_t)4U * i];
      uint64_t t20 = b[(uint32_t)4U * i];
      uint64_t *res_i0 = res + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t20, res_i0);
      {
        uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, t21, res_i1);
        {
          uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
          c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, t22, res_i2);
          {
            uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
            c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, t2, res_i);
          }
        }
      }
    }
  }
  {
    uint32_t i;
    for (i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
    {
      uint64_t t1 = a[i];
      uint64_t t2 = b[i];
      uint64_t *res_i = res + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res_i);
    }
  }
  return c;
}

inline uint64_t
Hacl_Bignum_Addition_bn_add_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
    {
      uint64_t t1 = a[(uint32_t)4U * i];
      uint64_t t20 = b[(uint32_t)4U * i];
      uint64_t *res_i0 = res + (uint32_t)4U * i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
      {
        uint64_t t10 = a[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res + (uint32_t)4U * i + (uint32_t)1U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
        {
          uint64_t t11 = a[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res + (uint32_t)4U * i + (uint32_t)2U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
          {
            uint64_t t12 = a[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t *res_i = res + (uint32_t)4U * i + (uint32_t)3U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
          }
        }
      }
    }
  }
  {
    uint32_t i;
    for (i = aLen / (uint32_t)4U * (uint32_t)4U; i < aLen; i++)
    {
      uint64_t t1 = a[i];
      uint64_t t2 = b[i];
      uint64_t *res_i = res + i;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res_i);
    }
  }
  return c;
}

static inline void
bn_mul_u64(uint32_t aLen, uint64_t *a, uint32_t bLen, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = aLen + bLen;
  uint32_t i;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (i = (uint32_t)0U; i < bLen; i++)
  {
    uint64_t bj = b[i];
    uint64_t *res_j = res + i;
    uint64_t c = (uint64_t)0U;
    uint64_t r;
    {
      uint32_t i0;
      for (i0 = (uint32_t)0U; i0 < aLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i0++)
      {
        uint64_t a_i = a[(uint32_t)4U * i0];
        uint64_t *res_i0 = res_j + (uint32_t)4U * i0;
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
        {
          uint64_t a_i0 = a[(uint32_t)4U * i0 + (uint32_t)1U];
          uint64_t *res_i1 = res_j + (uint32_t)4U * i0 + (uint32_t)1U;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
          {
            uint64_t a_i1 = a[(uint32_t)4U * i0 + (uint32_t)2U];
            uint64_t *res_i2 = res_j + (uint32_t)4U * i0 + (uint32_t)2U;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
            {
              uint64_t a_i2 = a[(uint32_t)4U * i0 + (uint32_t)3U];
              uint64_t *res_i = res_j + (uint32_t)4U * i0 + (uint32_t)3U;
              c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
            }
          }
        }
      }
    }
    {
      uint32_t i0;
      for (i0 = aLen / (uint32_t)4U * (uint32_t)4U; i0 < aLen; i0++)
      {
        uint64_t a_i = a[i0];
        uint64_t *res_i = res_j + i0;
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
      }
    }
    r = c;
    res[aLen + i] = r;
  }
}

static inline void bn_sqr_u64(uint32_t aLen, uint64_t *a, uint64_t *res)
{
  uint32_t resLen = aLen + aLen;
  uint64_t c0;
  memset(res, 0U, resLen * sizeof (uint64_t));
  {
    uint32_t i0;
    for (i0 = (uint32_t)0U; i0 < aLen; i0++)
    {
      uint64_t *ab = a;
      uint64_t a_j = a[i0];
      uint64_t *res_j = res + i0;
      uint64_t c = (uint64_t)0U;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < i0 / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
        {
          uint64_t a_i = ab[(uint32_t)4U * i];
          uint64_t *res_i0 = res_j + (uint32_t)4U * i;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
          {
            uint64_t a_i0 = ab[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
            {
              uint64_t a_i1 = ab[(uint32_t)4U * i + (uint32_t)2U];
              uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
              c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
              {
                uint64_t a_i2 = ab[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
                c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
              }
            }
          }
        }
      }
      {
        uint32_t i;
        for (i = i0 / (uint32_t)4U * (uint32_t)4U; i < i0; i++)
        {
          uint64_t a_i = ab[i];
          uint64_t *res_i = res_j + i;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i);
        }
      }
      {
        uint64_t r = c;
        res[i0 + i0] = r;
      }
    }
  }
  c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, res, res);
  KRML_CHECK_SIZE(sizeof (uint64_t), resLen);
  {
    uint64_t *tmp = (uint64_t *)alloca(resLen * sizeof (uint64_t));
    memset(tmp, 0U, resLen * sizeof (uint64_t));
    {
      uint64_t c1;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < aLen; i++)
        {
          FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
          uint64_t
          hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
          uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
          tmp[(uint32_t)2U * i] = lo;
          tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;
        }
      }
      c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64(resLen, res, tmp, res);
    }
  }
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
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    bn_mul_u64(aLen, a, aLen, b, res);
    return;
  }
  {
    uint32_t len2 = aLen / (uint32_t)2U;
    uint64_t *a0 = a;
    uint64_t *a1 = a + len2;
    uint64_t *b0 = b;
    uint64_t *b1 = b + len2;
    uint64_t *t0 = tmp;
    uint64_t *t1 = tmp + len2;
    uint64_t *tmp_ = tmp + aLen;
    uint64_t c0 = bn_sub_eq_len_u64(len2, a0, a1, tmp_);
    uint64_t c10 = bn_sub_eq_len_u64(len2, a1, a0, t0);
    uint64_t c00;
    uint64_t c010;
    uint64_t c11;
    uint64_t c1;
    uint64_t *t23;
    uint64_t *tmp1;
    uint64_t *r01;
    uint64_t *r23;
    uint64_t *r011;
    uint64_t *r231;
    uint64_t *t01;
    uint64_t *t231;
    uint64_t *t45;
    uint64_t *t67;
    uint64_t c2;
    uint64_t c_sign;
    uint64_t c3;
    uint64_t c31;
    uint64_t c4;
    uint64_t c41;
    uint64_t mask;
    uint64_t c5;
    uint32_t aLen2;
    uint64_t *r0;
    uint64_t r10;
    uint64_t c9;
    uint64_t c6;
    uint64_t c7;
    uint64_t *r;
    uint64_t c01;
    uint64_t r1;
    uint64_t c8;
    uint64_t c12;
    uint64_t c13;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < len2; i++)
      {
        uint64_t *os = t0;
        uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
        os[i] = x;
      }
    }
    c00 = c0;
    c010 = bn_sub_eq_len_u64(len2, b0, b1, tmp_);
    c11 = bn_sub_eq_len_u64(len2, b1, b0, t1);
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < len2; i++)
      {
        uint64_t *os = t1;
        uint64_t x = (((uint64_t)0U - c010) & t1[i]) | (~((uint64_t)0U - c010) & tmp_[i]);
        os[i] = x;
      }
    }
    c1 = c010;
    t23 = tmp + aLen;
    tmp1 = tmp + aLen + aLen;
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, t0, t1, tmp1, t23);
    r01 = res;
    r23 = res + aLen;
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a0, b0, tmp1, r01);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a1, b1, tmp1, r23);
    r011 = res;
    r231 = res + aLen;
    t01 = tmp;
    t231 = tmp + aLen;
    t45 = tmp + (uint32_t)2U * aLen;
    t67 = tmp + (uint32_t)3U * aLen;
    c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
    c_sign = c00 ^ c1;
    c3 = bn_sub_eq_len_u64(aLen, t01, t231, t67);
    c31 = c2 - c3;
    c4 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, t01, t231, t45);
    c41 = c2 + c4;
    mask = (uint64_t)0U - c_sign;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < aLen; i++)
      {
        uint64_t *os = t45;
        uint64_t x = (mask & t45[i]) | (~mask & t67[i]);
        os[i] = x;
      }
    }
    c5 = (mask & c41) | (~mask & c31);
    aLen2 = aLen / (uint32_t)2U;
    r0 = res + aLen2;
    r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
    c9 = r10;
    c6 = c9;
    c7 = c5 + c6;
    r = res + aLen + aLen2;
    c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
    if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
    {
      uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
      uint64_t *a11 = r + (uint32_t)1U;
      uint64_t *res1 = r + (uint32_t)1U;
      uint64_t c = c01;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
        {
          uint64_t t11 = a11[(uint32_t)4U * i];
          uint64_t *res_i0 = res1 + (uint32_t)4U * i;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i0);
          {
            uint64_t t110 = a11[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t110, (uint64_t)0U, res_i1);
            {
              uint64_t t111 = a11[(uint32_t)4U * i + (uint32_t)2U];
              uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t111, (uint64_t)0U, res_i2);
              {
                uint64_t t112 = a11[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
                c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t112, (uint64_t)0U, res_i);
              }
            }
          }
        }
      }
      {
        uint32_t i;
        for (i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
        {
          uint64_t t11 = a11[i];
          uint64_t *res_i = res1 + i;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i);
        }
      }
      {
        uint64_t c110 = c;
        r1 = c110;
      }
    }
    else
    {
      r1 = c01;
    }
    c8 = r1;
    c12 = c8;
    c13 = c12;
  }
}

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
)
{
  if (aLen < (uint32_t)32U || aLen % (uint32_t)2U == (uint32_t)1U)
  {
    bn_sqr_u64(aLen, a, res);
    return;
  }
  {
    uint32_t len2 = aLen / (uint32_t)2U;
    uint64_t *a0 = a;
    uint64_t *a1 = a + len2;
    uint64_t *t0 = tmp;
    uint64_t *tmp_ = tmp + aLen;
    uint64_t c0 = bn_sub_eq_len_u64(len2, a0, a1, tmp_);
    uint64_t c1 = bn_sub_eq_len_u64(len2, a1, a0, t0);
    uint64_t c00;
    uint64_t *t23;
    uint64_t *tmp1;
    uint64_t *r01;
    uint64_t *r23;
    uint64_t *r011;
    uint64_t *r231;
    uint64_t *t01;
    uint64_t *t231;
    uint64_t *t45;
    uint64_t c2;
    uint64_t c3;
    uint64_t c5;
    uint32_t aLen2;
    uint64_t *r0;
    uint64_t r10;
    uint64_t c4;
    uint64_t c6;
    uint64_t c7;
    uint64_t *r;
    uint64_t c01;
    uint64_t r1;
    uint64_t c8;
    uint64_t c9;
    uint64_t c10;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < len2; i++)
      {
        uint64_t *os = t0;
        uint64_t x = (((uint64_t)0U - c0) & t0[i]) | (~((uint64_t)0U - c0) & tmp_[i]);
        os[i] = x;
      }
    }
    c00 = c0;
    t23 = tmp + aLen;
    tmp1 = tmp + aLen + aLen;
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, t0, tmp1, t23);
    r01 = res;
    r23 = res + aLen;
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a0, tmp1, r01);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a1, tmp1, r23);
    r011 = res;
    r231 = res + aLen;
    t01 = tmp;
    t231 = tmp + aLen;
    t45 = tmp + (uint32_t)2U * aLen;
    c2 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
    c3 = bn_sub_eq_len_u64(aLen, t01, t231, t45);
    c5 = c2 - c3;
    aLen2 = aLen / (uint32_t)2U;
    r0 = res + aLen2;
    r10 = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r0, t45, r0);
    c4 = r10;
    c6 = c4;
    c7 = c5 + c6;
    r = res + aLen + aLen2;
    c01 = Lib_IntTypes_Intrinsics_add_carry_u64((uint64_t)0U, r[0U], c7, r);
    if ((uint32_t)1U < aLen + aLen - (aLen + aLen2))
    {
      uint32_t rLen = aLen + aLen - (aLen + aLen2) - (uint32_t)1U;
      uint64_t *a11 = r + (uint32_t)1U;
      uint64_t *res1 = r + (uint32_t)1U;
      uint64_t c = c01;
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < rLen / (uint32_t)4U * (uint32_t)4U / (uint32_t)4U; i++)
        {
          uint64_t t1 = a11[(uint32_t)4U * i];
          uint64_t *res_i0 = res1 + (uint32_t)4U * i;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
          {
            uint64_t t10 = a11[(uint32_t)4U * i + (uint32_t)1U];
            uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
            {
              uint64_t t11 = a11[(uint32_t)4U * i + (uint32_t)2U];
              uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
              c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
              {
                uint64_t t12 = a11[(uint32_t)4U * i + (uint32_t)3U];
                uint64_t *res_i = res1 + (uint32_t)4U * i + (uint32_t)3U;
                c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, (uint64_t)0U, res_i);
              }
            }
          }
        }
      }
      {
        uint32_t i;
        for (i = rLen / (uint32_t)4U * (uint32_t)4U; i < rLen; i++)
        {
          uint64_t t1 = a11[i];
          uint64_t *res_i = res1 + i;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
        }
      }
      {
        uint64_t c11 = c;
        r1 = c11;
      }
    }
    else
    {
      r1 = c01;
    }
    c8 = r1;
    c9 = c8;
    c10 = c9;
  }
}

inline uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0)
{
  uint64_t alpha = (uint64_t)9223372036854775808U;
  uint64_t beta = n0;
  uint64_t ub = (uint64_t)0U;
  uint64_t vb = (uint64_t)0U;
  ub = (uint64_t)1U;
  vb = (uint64_t)0U;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      uint64_t us = ub;
      uint64_t vs = vb;
      uint64_t u_is_odd = (uint64_t)0U - (us & (uint64_t)1U);
      uint64_t beta_if_u_is_odd = beta & u_is_odd;
      ub = ((us ^ beta_if_u_is_odd) >> (uint32_t)1U) + (us & beta_if_u_is_odd);
      {
        uint64_t alpha_if_u_is_odd = alpha & u_is_odd;
        vb = (vs >> (uint32_t)1U) + alpha_if_u_is_odd;
      }
    }
  }
  return vb;
}

