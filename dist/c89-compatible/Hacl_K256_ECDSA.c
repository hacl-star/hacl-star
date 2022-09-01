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


#include "internal/Hacl_K256_ECDSA.h"

#include "internal/Hacl_Bignum.h"

static inline uint64_t
bn_add(uint32_t aLen, uint64_t *a, uint32_t bLen, uint64_t *b, uint64_t *res)
{
  uint64_t *a0 = a;
  uint64_t *res0 = res;
  uint64_t c1 = (uint64_t)0U;
  uint64_t c0;
  uint64_t ite;
  {
    uint32_t i;
    for (i = (uint32_t)0U; i < bLen / (uint32_t)4U; i++)
    {
      uint64_t t1 = a0[(uint32_t)4U * i];
      uint64_t t20 = b[(uint32_t)4U * i];
      uint64_t *res_i0 = res0 + (uint32_t)4U * i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t20, res_i0);
      {
        uint64_t t10 = a0[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t t21 = b[(uint32_t)4U * i + (uint32_t)1U];
        uint64_t *res_i1 = res0 + (uint32_t)4U * i + (uint32_t)1U;
        c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t10, t21, res_i1);
        {
          uint64_t t11 = a0[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t t22 = b[(uint32_t)4U * i + (uint32_t)2U];
          uint64_t *res_i2 = res0 + (uint32_t)4U * i + (uint32_t)2U;
          c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t11, t22, res_i2);
          {
            uint64_t t12 = a0[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t t2 = b[(uint32_t)4U * i + (uint32_t)3U];
            uint64_t *res_i = res0 + (uint32_t)4U * i + (uint32_t)3U;
            c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t12, t2, res_i);
          }
        }
      }
    }
  }
  {
    uint32_t i;
    for (i = bLen / (uint32_t)4U * (uint32_t)4U; i < bLen; i++)
    {
      uint64_t t1 = a0[i];
      uint64_t t2 = b[i];
      uint64_t *res_i = res0 + i;
      c1 = Lib_IntTypes_Intrinsics_add_carry_u64(c1, t1, t2, res_i);
    }
  }
  c0 = c1;
  if (bLen < aLen)
  {
    uint32_t rLen = aLen - bLen;
    uint64_t *a1 = a + bLen;
    uint64_t *res1 = res + bLen;
    uint64_t c = c0;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < rLen / (uint32_t)4U; i++)
      {
        uint64_t t1 = a1[(uint32_t)4U * i];
        uint64_t *res_i0 = res1 + (uint32_t)4U * i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i0);
        {
          uint64_t t10 = a1[(uint32_t)4U * i + (uint32_t)1U];
          uint64_t *res_i1 = res1 + (uint32_t)4U * i + (uint32_t)1U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, (uint64_t)0U, res_i1);
          {
            uint64_t t11 = a1[(uint32_t)4U * i + (uint32_t)2U];
            uint64_t *res_i2 = res1 + (uint32_t)4U * i + (uint32_t)2U;
            c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, (uint64_t)0U, res_i2);
            {
              uint64_t t12 = a1[(uint32_t)4U * i + (uint32_t)3U];
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
        uint64_t t1 = a1[i];
        uint64_t *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, (uint64_t)0U, res_i);
      }
    }
    {
      uint64_t c10 = c;
      ite = c10;
    }
  }
  else
  {
    ite = c0;
  }
  return ite;
}

static uint64_t add4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  {
    uint64_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t20, res_i0);
    {
      uint64_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t10, t21, res_i1);
      {
        uint64_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
        uint64_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
        uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
        c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t11, t22, res_i2);
        {
          uint64_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
          c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t12, t2, res_i);
        }
      }
    }
  }
  return c;
}

static void add_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c2 = (uint64_t)0U;
  uint64_t c0;
  {
    uint64_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t1, t20, res_i0);
    {
      uint64_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t10, t21, res_i1);
      {
        uint64_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
        uint64_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
        uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
        c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t11, t22, res_i2);
        {
          uint64_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
          c2 = Lib_IntTypes_Intrinsics_add_carry_u64(c2, t12, t2, res_i);
        }
      }
    }
  }
  c0 = c2;
  {
    uint64_t tmp[4U] = { 0U };
    uint64_t c3 = (uint64_t)0U;
    uint64_t c1;
    uint64_t c;
    {
      uint64_t t1 = res[(uint32_t)4U * (uint32_t)0U];
      uint64_t t20 = n[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
      c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t1, t20, res_i0);
      {
        uint64_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
        uint64_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
        uint64_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
        c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t10, t21, res_i1);
        {
          uint64_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
          c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t11, t22, res_i2);
          {
            uint64_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
            uint64_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
            uint64_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
            c3 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c3, t12, t2, res_i);
          }
        }
      }
    }
    c1 = c3;
    c = c0 - c1;
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      uint64_t *os = res;
      uint64_t x = (c & res[i]) | (~c & tmp[i]);
      os[i] = x;);
  }
}

static void sub_mod4(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c2 = (uint64_t)0U;
  uint64_t c0;
  {
    uint64_t t1 = a[(uint32_t)4U * (uint32_t)0U];
    uint64_t t20 = b[(uint32_t)4U * (uint32_t)0U];
    uint64_t *res_i0 = res + (uint32_t)4U * (uint32_t)0U;
    c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t1, t20, res_i0);
    {
      uint64_t t10 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t t21 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
      uint64_t *res_i1 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
      c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t10, t21, res_i1);
      {
        uint64_t t11 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
        uint64_t t22 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
        uint64_t *res_i2 = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
        c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t11, t22, res_i2);
        {
          uint64_t t12 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t t2 = b[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
          uint64_t *res_i = res + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
          c2 = Lib_IntTypes_Intrinsics_sub_borrow_u64(c2, t12, t2, res_i);
        }
      }
    }
  }
  c0 = c2;
  {
    uint64_t tmp[4U] = { 0U };
    uint64_t c3 = (uint64_t)0U;
    uint64_t c1;
    uint64_t c;
    {
      uint64_t t1 = res[(uint32_t)4U * (uint32_t)0U];
      uint64_t t20 = n[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = tmp + (uint32_t)4U * (uint32_t)0U;
      c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, t20, res_i0);
      {
        uint64_t t10 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
        uint64_t t21 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
        uint64_t *res_i1 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
        c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t10, t21, res_i1);
        {
          uint64_t t11 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t t22 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t *res_i2 = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
          c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t11, t22, res_i2);
          {
            uint64_t t12 = res[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
            uint64_t t2 = n[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
            uint64_t *res_i = tmp + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
            c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t12, t2, res_i);
          }
        }
      }
    }
    c1 = c3;
    c = (uint64_t)0U - c0;
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      uint64_t *os = res;
      uint64_t x = (c & tmp[i]) | (~c & res[i]);
      os[i] = x;);
  }
}

static void mul4(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t i;
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  for (i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t bj = b[i];
    uint64_t *res_j = res + i;
    uint64_t c = (uint64_t)0U;
    uint64_t r;
    {
      uint64_t a_i = a[(uint32_t)4U * (uint32_t)0U];
      uint64_t *res_i0 = res_j + (uint32_t)4U * (uint32_t)0U;
      c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
      {
        uint64_t a_i0 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)1U];
        uint64_t *res_i1 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)1U;
        c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
        {
          uint64_t a_i1 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)2U];
          uint64_t *res_i2 = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)2U;
          c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
          {
            uint64_t a_i2 = a[(uint32_t)4U * (uint32_t)0U + (uint32_t)3U];
            uint64_t *res_i = res_j + (uint32_t)4U * (uint32_t)0U + (uint32_t)3U;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
          }
        }
      }
    }
    r = c;
    res[(uint32_t)4U + i] = r;
  }
}

static void sqr4(uint64_t *a, uint64_t *res)
{
  uint64_t c0;
  memset(res, 0U, (uint32_t)8U * sizeof (uint64_t));
  KRML_MAYBE_FOR4(i0,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *ab = a;
    uint64_t a_j = a[i0];
    uint64_t *res_j = res + i0;
    uint64_t c = (uint64_t)0U;
    {
      uint32_t i;
      for (i = (uint32_t)0U; i < i0 / (uint32_t)4U; i++)
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
    uint64_t r = c;
    res[i0 + i0] = r;);
  c0 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, res, res);
  {
    uint64_t tmp[8U] = { 0U };
    uint64_t c1;
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      FStar_UInt128_uint128 res1 = FStar_UInt128_mul_wide(a[i], a[i]);
      uint64_t hi = FStar_UInt128_uint128_to_uint64(FStar_UInt128_shift_right(res1, (uint32_t)64U));
      uint64_t lo = FStar_UInt128_uint128_to_uint64(res1);
      tmp[(uint32_t)2U * i] = lo;
      tmp[(uint32_t)2U * i + (uint32_t)1U] = hi;);
    c1 = Hacl_Bignum_Addition_bn_add_eq_len_u64((uint32_t)8U, res, tmp, res);
  }
}

static inline uint64_t is_qelem_zero(uint64_t *f)
{
  uint64_t bn_zero[4U] = { 0U };
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t mask1;
  uint64_t res;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t uu____0 = FStar_UInt64_eq_mask(f[i], bn_zero[i]);
    mask = uu____0 & mask;);
  mask1 = mask;
  res = mask1;
  return res;
}

static inline bool is_qelem_zero_vartime(uint64_t *f)
{
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  return f0 == (uint64_t)0U && f1 == (uint64_t)0U && f2 == (uint64_t)0U && f3 == (uint64_t)0U;
}

static inline uint64_t load_qelem_check(uint64_t *f, uint8_t *b)
{
  uint64_t n[4U] = { 0U };
  uint64_t is_zero;
  n[0U] = (uint64_t)0xbfd25e8cd0364141U;
  n[1U] = (uint64_t)0xbaaedce6af48a03bU;
  n[2U] = (uint64_t)0xfffffffffffffffeU;
  n[3U] = (uint64_t)0xffffffffffffffffU;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)32U, b, f);
  is_zero = is_qelem_zero(f);
  {
    uint64_t acc = (uint64_t)0U;
    uint64_t is_lt_q;
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      uint64_t beq = FStar_UInt64_eq_mask(f[i], n[i]);
      uint64_t blt = ~FStar_UInt64_gte_mask(f[i], n[i]);
      acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U))););
    is_lt_q = acc;
    return ~is_zero & is_lt_q;
  }
}

static inline bool load_qelem_vartime(uint64_t *f, uint8_t *b)
{
  bool is_zero;
  uint64_t a0;
  uint64_t a1;
  uint64_t a2;
  uint64_t a3;
  bool is_lt_q_b;
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)32U, b, f);
  is_zero = is_qelem_zero_vartime(f);
  a0 = f[0U];
  a1 = f[1U];
  a2 = f[2U];
  a3 = f[3U];
  if (a3 < (uint64_t)0xffffffffffffffffU)
  {
    is_lt_q_b = true;
  }
  else if (a2 < (uint64_t)0xfffffffffffffffeU)
  {
    is_lt_q_b = true;
  }
  else if (a2 > (uint64_t)0xfffffffffffffffeU)
  {
    is_lt_q_b = false;
  }
  else if (a1 < (uint64_t)0xbaaedce6af48a03bU)
  {
    is_lt_q_b = true;
  }
  else if (a1 > (uint64_t)0xbaaedce6af48a03bU)
  {
    is_lt_q_b = false;
  }
  else
  {
    is_lt_q_b = a0 < (uint64_t)0xbfd25e8cd0364141U;
  }
  return !is_zero && is_lt_q_b;
}

static inline void modq_short(uint64_t *out, uint64_t *a)
{
  uint64_t tmp[4U] = { 0U };
  uint64_t c;
  uint64_t mask;
  tmp[0U] = (uint64_t)0x402da1732fc9bebfU;
  tmp[1U] = (uint64_t)0x4551231950b75fc4U;
  tmp[2U] = (uint64_t)0x1U;
  tmp[3U] = (uint64_t)0x0U;
  c = add4(a, tmp, out);
  mask = (uint64_t)0U - c;
  KRML_MAYBE_FOR4(i,
    (uint32_t)0U,
    (uint32_t)4U,
    (uint32_t)1U,
    uint64_t *os = out;
    uint64_t x = (mask & out[i]) | (~mask & a[i]);
    os[i] = x;);
}

static inline void load_qelem_modq(uint64_t *f, uint8_t *b)
{
  uint64_t tmp[4U] = { 0U };
  Hacl_Bignum_Convert_bn_from_bytes_be_uint64((uint32_t)32U, b, f);
  memcpy(tmp, f, (uint32_t)4U * sizeof (uint64_t));
  modq_short(f, tmp);
}

static inline void store_qelem(uint8_t *b, uint64_t *f)
{
  Hacl_Bignum_Convert_bn_to_bytes_be_uint64((uint32_t)32U, f, b);
}

static inline void qadd(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t n[4U] = { 0U };
  n[0U] = (uint64_t)0xbfd25e8cd0364141U;
  n[1U] = (uint64_t)0xbaaedce6af48a03bU;
  n[2U] = (uint64_t)0xfffffffffffffffeU;
  n[3U] = (uint64_t)0xffffffffffffffffU;
  add_mod4(n, f1, f2, out);
}

static inline uint64_t
mul_pow2_256_minus_q_add(
  uint32_t len,
  uint32_t resLen,
  uint64_t *t01,
  uint64_t *a,
  uint64_t *e,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len + (uint32_t)2U);
  {
    uint64_t tmp[len + (uint32_t)2U];
    memset(tmp, 0U, (len + (uint32_t)2U) * sizeof (uint64_t));
    {
      uint64_t uu____0;
      uint64_t c0;
      memset(tmp, 0U, (len + (uint32_t)2U) * sizeof (uint64_t));
      KRML_MAYBE_FOR2(i0,
        (uint32_t)0U,
        (uint32_t)2U,
        (uint32_t)1U,
        uint64_t bj = t01[i0];
        uint64_t *res_j = tmp + i0;
        uint64_t c = (uint64_t)0U;
        {
          uint32_t i;
          for (i = (uint32_t)0U; i < len / (uint32_t)4U; i++)
          {
            uint64_t a_i = a[(uint32_t)4U * i];
            uint64_t *res_i0 = res_j + (uint32_t)4U * i;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
            {
              uint64_t a_i0 = a[(uint32_t)4U * i + (uint32_t)1U];
              uint64_t *res_i1 = res_j + (uint32_t)4U * i + (uint32_t)1U;
              c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
              {
                uint64_t a_i1 = a[(uint32_t)4U * i + (uint32_t)2U];
                uint64_t *res_i2 = res_j + (uint32_t)4U * i + (uint32_t)2U;
                c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
                {
                  uint64_t a_i2 = a[(uint32_t)4U * i + (uint32_t)3U];
                  uint64_t *res_i = res_j + (uint32_t)4U * i + (uint32_t)3U;
                  c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
                }
              }
            }
          }
        }
        {
          uint32_t i;
          for (i = len / (uint32_t)4U * (uint32_t)4U; i < len; i++)
          {
            uint64_t a_i = a[i];
            uint64_t *res_i = res_j + i;
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i);
          }
        }
        uint64_t r = c;
        tmp[len + i0] = r;);
      memcpy(res + (uint32_t)2U, a, len * sizeof (uint64_t));
      uu____0 = bn_add(resLen, res, len + (uint32_t)2U, tmp, res);
      c0 = bn_add(resLen, res, (uint32_t)4U, e, res);
      return c0;
    }
  }
}

static inline void modq(uint64_t *out, uint64_t *a)
{
  uint64_t r[4U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  uint64_t *t01;
  tmp[0U] = (uint64_t)0x402da1732fc9bebfU;
  tmp[1U] = (uint64_t)0x4551231950b75fc4U;
  tmp[2U] = (uint64_t)0x1U;
  tmp[3U] = (uint64_t)0x0U;
  t01 = tmp;
  {
    uint64_t m[7U] = { 0U };
    uint64_t p[5U] = { 0U };
    uint64_t
    c0 = mul_pow2_256_minus_q_add((uint32_t)4U, (uint32_t)7U, t01, a + (uint32_t)4U, a, m);
    uint64_t
    c10 = mul_pow2_256_minus_q_add((uint32_t)3U, (uint32_t)5U, t01, m + (uint32_t)4U, m, p);
    uint64_t
    c2 = mul_pow2_256_minus_q_add((uint32_t)1U, (uint32_t)4U, t01, p + (uint32_t)4U, p, r);
    uint64_t c00 = c2;
    uint64_t c1 = add4(r, tmp, out);
    uint64_t mask = (uint64_t)0U - (c00 + c1);
    KRML_MAYBE_FOR4(i,
      (uint32_t)0U,
      (uint32_t)4U,
      (uint32_t)1U,
      uint64_t *os = out;
      uint64_t x = (mask & out[i]) | (~mask & r[i]);
      os[i] = x;);
  }
}

static inline void qmul(uint64_t *out, uint64_t *f1, uint64_t *f2)
{
  uint64_t tmp[8U] = { 0U };
  mul4(f1, f2, tmp);
  modq(out, tmp);
}

static inline void qsqr(uint64_t *out, uint64_t *f)
{
  uint64_t tmp[8U] = { 0U };
  sqr4(f, tmp);
  modq(out, tmp);
}

static inline void qnegate_conditional_vartime(uint64_t *f, bool is_negate)
{
  uint64_t n[4U] = { 0U };
  n[0U] = (uint64_t)0xbfd25e8cd0364141U;
  n[1U] = (uint64_t)0xbaaedce6af48a03bU;
  n[2U] = (uint64_t)0xfffffffffffffffeU;
  n[3U] = (uint64_t)0xffffffffffffffffU;
  {
    uint64_t zero[4U] = { 0U };
    if (is_negate)
    {
      sub_mod4(n, zero, f, f);
    }
  }
}

static inline bool is_qelem_le_q_halved_vartime(uint64_t *f)
{
  uint64_t a0 = f[0U];
  uint64_t a1 = f[1U];
  uint64_t a2 = f[2U];
  uint64_t a3 = f[3U];
  if (a3 < (uint64_t)0x7fffffffffffffffU)
  {
    return true;
  }
  if (a3 > (uint64_t)0x7fffffffffffffffU)
  {
    return false;
  }
  if (a2 < (uint64_t)0xffffffffffffffffU)
  {
    return true;
  }
  if (a2 > (uint64_t)0xffffffffffffffffU)
  {
    return false;
  }
  if (a1 < (uint64_t)0x5d576e7357a4501dU)
  {
    return true;
  }
  if (a1 > (uint64_t)0x5d576e7357a4501dU)
  {
    return false;
  }
  return a0 <= (uint64_t)0xdfe92f46681b20a0U;
}

static inline void qsquare_times_in_place(uint64_t *out, uint32_t b)
{
  uint32_t i;
  for (i = (uint32_t)0U; i < b; i++)
  {
    qsqr(out, out);
  }
}

static inline void qsquare_times(uint64_t *out, uint64_t *a, uint32_t b)
{
  uint32_t i;
  memcpy(out, a, (uint32_t)4U * sizeof (uint64_t));
  for (i = (uint32_t)0U; i < b; i++)
  {
    qsqr(out, out);
  }
}

static inline void qinv(uint64_t *out, uint64_t *f)
{
  uint64_t x_10[4U] = { 0U };
  uint64_t x_11[4U] = { 0U };
  uint64_t x_101[4U] = { 0U };
  uint64_t x_111[4U] = { 0U };
  uint64_t x_1001[4U] = { 0U };
  uint64_t x_1011[4U] = { 0U };
  uint64_t x_1101[4U] = { 0U };
  qsquare_times(x_10, f, (uint32_t)1U);
  qmul(x_11, x_10, f);
  qmul(x_101, x_10, x_11);
  qmul(x_111, x_10, x_101);
  qmul(x_1001, x_10, x_111);
  qmul(x_1011, x_10, x_1001);
  qmul(x_1101, x_10, x_1011);
  {
    uint64_t x6[4U] = { 0U };
    uint64_t x8[4U] = { 0U };
    uint64_t x14[4U] = { 0U };
    qsquare_times(x6, x_1101, (uint32_t)2U);
    qmul(x6, x6, x_1011);
    qsquare_times(x8, x6, (uint32_t)2U);
    qmul(x8, x8, x_11);
    qsquare_times(x14, x8, (uint32_t)6U);
    qmul(x14, x14, x6);
    {
      uint64_t x56[4U] = { 0U };
      qsquare_times(out, x14, (uint32_t)14U);
      qmul(out, out, x14);
      qsquare_times(x56, out, (uint32_t)28U);
      qmul(x56, x56, out);
      qsquare_times(out, x56, (uint32_t)56U);
      qmul(out, out, x56);
      qsquare_times_in_place(out, (uint32_t)14U);
      qmul(out, out, x14);
      qsquare_times_in_place(out, (uint32_t)3U);
      qmul(out, out, x_101);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_111);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_101);
      qsquare_times_in_place(out, (uint32_t)5U);
      qmul(out, out, x_1011);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_1011);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_111);
      qsquare_times_in_place(out, (uint32_t)5U);
      qmul(out, out, x_111);
      qsquare_times_in_place(out, (uint32_t)6U);
      qmul(out, out, x_1101);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_101);
      qsquare_times_in_place(out, (uint32_t)3U);
      qmul(out, out, x_111);
      qsquare_times_in_place(out, (uint32_t)5U);
      qmul(out, out, x_1001);
      qsquare_times_in_place(out, (uint32_t)6U);
      qmul(out, out, x_101);
      qsquare_times_in_place(out, (uint32_t)10U);
      qmul(out, out, x_111);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_111);
      qsquare_times_in_place(out, (uint32_t)9U);
      qmul(out, out, x8);
      qsquare_times_in_place(out, (uint32_t)5U);
      qmul(out, out, x_1001);
      qsquare_times_in_place(out, (uint32_t)6U);
      qmul(out, out, x_1011);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_1101);
      qsquare_times_in_place(out, (uint32_t)5U);
      qmul(out, out, x_11);
      qsquare_times_in_place(out, (uint32_t)6U);
      qmul(out, out, x_1101);
      qsquare_times_in_place(out, (uint32_t)10U);
      qmul(out, out, x_1101);
      qsquare_times_in_place(out, (uint32_t)4U);
      qmul(out, out, x_1001);
      qsquare_times_in_place(out, (uint32_t)6U);
      qmul(out, out, f);
      qsquare_times_in_place(out, (uint32_t)8U);
      qmul(out, out, x6);
    }
  }
}

bool Hacl_Impl_K256_Point_aff_point_decompress_vartime(uint64_t *x, uint64_t *y, uint8_t *s)
{
  uint8_t s0 = s[0U];
  if (!(s0 == (uint8_t)0x02U || s0 == (uint8_t)0x03U))
  {
    return false;
  }
  {
    uint8_t *xb = s + (uint32_t)1U;
    bool is_x_valid = Hacl_K256_Field_load_felem_vartime(x, xb);
    bool is_y_odd = s0 == (uint8_t)0x03U;
    if (!is_x_valid)
    {
      return false;
    }
    {
      uint64_t y2[5U] = { 0U };
      uint64_t b[5U] = { 0U };
      b[0U] = (uint64_t)0x7U;
      b[1U] = (uint64_t)0U;
      b[2U] = (uint64_t)0U;
      b[3U] = (uint64_t)0U;
      b[4U] = (uint64_t)0U;
      Hacl_K256_Field_fsqr(y2, x);
      Hacl_K256_Field_fmul(y2, y2, x);
      Hacl_K256_Field_fadd(y2, y2, b);
      Hacl_K256_Field_fnormalize(y2, y2);
      Hacl_Impl_K256_Finv_fsqrt(y, y2);
      Hacl_K256_Field_fnormalize(y, y);
      {
        uint64_t y2_comp[5U] = { 0U };
        Hacl_K256_Field_fsqr(y2_comp, y);
        Hacl_K256_Field_fnormalize(y2_comp, y2_comp);
        {
          bool res = Hacl_K256_Field_is_felem_eq_vartime(y2, y2_comp);
          bool is_y_valid = res;
          if (!is_y_valid)
          {
            return false;
          }
          {
            uint64_t x0 = y[0U];
            bool is_y_odd1 = (x0 & (uint64_t)1U) == (uint64_t)1U;
            Hacl_K256_Field_fnegate_conditional_vartime(y, is_y_odd1 != is_y_odd);
            return true;
          }
        }
      }
    }
  }
}

void Hacl_Impl_K256_Point_aff_point_compress_vartime(uint8_t *s, uint64_t *x, uint64_t *y)
{
  uint64_t x0;
  bool is_y_odd;
  uint8_t ite;
  Hacl_K256_Field_fnormalize(y, y);
  Hacl_K256_Field_fnormalize(x, x);
  x0 = y[0U];
  is_y_odd = (x0 & (uint64_t)1U) == (uint64_t)1U;
  if (is_y_odd)
  {
    ite = (uint8_t)0x03U;
  }
  else
  {
    ite = (uint8_t)0x02U;
  }
  s[0U] = ite;
  Hacl_K256_Field_store_felem(s + (uint32_t)1U, x);
}

void Hacl_Impl_K256_Point_point_negate(uint64_t *out, uint64_t *p)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  uint64_t *ox = out;
  uint64_t *oy = out + (uint32_t)5U;
  uint64_t *oz = out + (uint32_t)10U;
  uint64_t a0;
  uint64_t a1;
  uint64_t a2;
  uint64_t a3;
  uint64_t a4;
  uint64_t r0;
  uint64_t r1;
  uint64_t r2;
  uint64_t r3;
  uint64_t r4;
  uint64_t f0;
  uint64_t f1;
  uint64_t f2;
  uint64_t f3;
  uint64_t f4;
  ox[0U] = px[0U];
  ox[1U] = px[1U];
  ox[2U] = px[2U];
  ox[3U] = px[3U];
  ox[4U] = px[4U];
  oz[0U] = pz[0U];
  oz[1U] = pz[1U];
  oz[2U] = pz[2U];
  oz[3U] = pz[3U];
  oz[4U] = pz[4U];
  a0 = py[0U];
  a1 = py[1U];
  a2 = py[2U];
  a3 = py[3U];
  a4 = py[4U];
  r0 = (uint64_t)0xffffefffffc2fU * (uint64_t)2U * (uint64_t)2U - a0;
  r1 = (uint64_t)0xfffffffffffffU * (uint64_t)2U * (uint64_t)2U - a1;
  r2 = (uint64_t)0xfffffffffffffU * (uint64_t)2U * (uint64_t)2U - a2;
  r3 = (uint64_t)0xfffffffffffffU * (uint64_t)2U * (uint64_t)2U - a3;
  r4 = (uint64_t)0xffffffffffffU * (uint64_t)2U * (uint64_t)2U - a4;
  f0 = r0;
  f1 = r1;
  f2 = r2;
  f3 = r3;
  f4 = r4;
  oy[0U] = f0;
  oy[1U] = f1;
  oy[2U] = f2;
  oy[3U] = f3;
  oy[4U] = f4;
  Hacl_K256_Field_fnormalize_weak(oy, oy);
}

static inline bool fmul_fmul_eq_vartime(uint64_t *a, uint64_t *bz, uint64_t *c, uint64_t *dz)
{
  uint64_t a_bz[5U] = { 0U };
  uint64_t c_dz[5U] = { 0U };
  bool z;
  Hacl_K256_Field_fmul(a_bz, a, bz);
  Hacl_K256_Field_fmul(c_dz, c, dz);
  Hacl_K256_Field_fnormalize(a_bz, a_bz);
  Hacl_K256_Field_fnormalize(c_dz, c_dz);
  z = Hacl_K256_Field_is_felem_eq_vartime(a_bz, c_dz);
  return z;
}

bool Hacl_Impl_K256_Point_point_eq(uint64_t *p, uint64_t *q)
{
  uint64_t *px = p;
  uint64_t *py = p + (uint32_t)5U;
  uint64_t *pz = p + (uint32_t)10U;
  uint64_t *qx = q;
  uint64_t *qy = q + (uint32_t)5U;
  uint64_t *qz = q + (uint32_t)10U;
  bool z0 = fmul_fmul_eq_vartime(px, qz, qx, pz);
  if (!z0)
  {
    return false;
  }
  return fmul_fmul_eq_vartime(py, qz, qy, pz);
}

void Hacl_Impl_K256_PointDouble_point_double(uint64_t *out, uint64_t *p)
{
  uint64_t tmp[25U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *yy = tmp;
  uint64_t *zz = tmp + (uint32_t)5U;
  uint64_t *bzz3 = tmp + (uint32_t)10U;
  uint64_t *bzz9 = tmp + (uint32_t)15U;
  uint64_t *tmp1 = tmp + (uint32_t)20U;
  Hacl_K256_Field_fsqr(yy, y1);
  Hacl_K256_Field_fsqr(zz, z1);
  Hacl_K256_Field_fmul_small_num(x3, x1, (uint64_t)2U);
  Hacl_K256_Field_fmul(x3, x3, y1);
  Hacl_K256_Field_fmul(tmp1, yy, y1);
  Hacl_K256_Field_fmul(z3, tmp1, z1);
  Hacl_K256_Field_fmul_small_num(z3, z3, (uint64_t)8U);
  Hacl_K256_Field_fnormalize_weak(z3, z3);
  Hacl_K256_Field_fmul_small_num(bzz3, zz, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(bzz3, bzz3);
  Hacl_K256_Field_fmul_small_num(bzz9, bzz3, (uint64_t)3U);
  Hacl_K256_Field_fsub(bzz9, yy, bzz9, (uint64_t)6U);
  Hacl_K256_Field_fadd(tmp1, yy, bzz3);
  Hacl_K256_Field_fmul(tmp1, bzz9, tmp1);
  Hacl_K256_Field_fmul(y3, yy, zz);
  Hacl_K256_Field_fmul(x3, x3, bzz9);
  Hacl_K256_Field_fmul_small_num(y3, y3, (uint64_t)168U);
  Hacl_K256_Field_fadd(y3, tmp1, y3);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
}

void Hacl_Impl_K256_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q)
{
  uint64_t tmp[45U] = { 0U };
  uint64_t *x1 = p;
  uint64_t *y1 = p + (uint32_t)5U;
  uint64_t *z1 = p + (uint32_t)10U;
  uint64_t *x2 = q;
  uint64_t *y2 = q + (uint32_t)5U;
  uint64_t *z2 = q + (uint32_t)10U;
  uint64_t *x3 = out;
  uint64_t *y3 = out + (uint32_t)5U;
  uint64_t *z3 = out + (uint32_t)10U;
  uint64_t *xx = tmp;
  uint64_t *yy = tmp + (uint32_t)5U;
  uint64_t *zz = tmp + (uint32_t)10U;
  uint64_t *xy_pairs = tmp + (uint32_t)15U;
  uint64_t *yz_pairs = tmp + (uint32_t)20U;
  uint64_t *xz_pairs = tmp + (uint32_t)25U;
  uint64_t *yy_m_bzz3 = tmp + (uint32_t)30U;
  uint64_t *yy_p_bzz3 = tmp + (uint32_t)35U;
  uint64_t *tmp1 = tmp + (uint32_t)40U;
  Hacl_K256_Field_fmul(xx, x1, x2);
  Hacl_K256_Field_fmul(yy, y1, y2);
  Hacl_K256_Field_fmul(zz, z1, z2);
  Hacl_K256_Field_fadd(xy_pairs, x1, y1);
  Hacl_K256_Field_fadd(tmp1, x2, y2);
  Hacl_K256_Field_fmul(xy_pairs, xy_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, xx, yy);
  Hacl_K256_Field_fsub(xy_pairs, xy_pairs, tmp1, (uint64_t)4U);
  Hacl_K256_Field_fadd(yz_pairs, y1, z1);
  Hacl_K256_Field_fadd(tmp1, y2, z2);
  Hacl_K256_Field_fmul(yz_pairs, yz_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, yy, zz);
  Hacl_K256_Field_fsub(yz_pairs, yz_pairs, tmp1, (uint64_t)4U);
  Hacl_K256_Field_fadd(xz_pairs, x1, z1);
  Hacl_K256_Field_fadd(tmp1, x2, z2);
  Hacl_K256_Field_fmul(xz_pairs, xz_pairs, tmp1);
  Hacl_K256_Field_fadd(tmp1, xx, zz);
  Hacl_K256_Field_fsub(xz_pairs, xz_pairs, tmp1, (uint64_t)4U);
  Hacl_K256_Field_fmul_small_num(tmp1, zz, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(tmp1, tmp1);
  Hacl_K256_Field_fsub(yy_m_bzz3, yy, tmp1, (uint64_t)2U);
  Hacl_K256_Field_fadd(yy_p_bzz3, yy, tmp1);
  Hacl_K256_Field_fmul_small_num(x3, yz_pairs, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(x3, x3);
  Hacl_K256_Field_fmul_small_num(z3, xx, (uint64_t)3U);
  Hacl_K256_Field_fmul_small_num(y3, z3, (uint64_t)21U);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
  Hacl_K256_Field_fmul(tmp1, xy_pairs, yy_m_bzz3);
  Hacl_K256_Field_fmul(x3, x3, xz_pairs);
  Hacl_K256_Field_fsub(x3, tmp1, x3, (uint64_t)2U);
  Hacl_K256_Field_fnormalize_weak(x3, x3);
  Hacl_K256_Field_fmul(tmp1, yy_p_bzz3, yy_m_bzz3);
  Hacl_K256_Field_fmul(y3, y3, xz_pairs);
  Hacl_K256_Field_fadd(y3, tmp1, y3);
  Hacl_K256_Field_fnormalize_weak(y3, y3);
  Hacl_K256_Field_fmul(tmp1, yz_pairs, yy_p_bzz3);
  Hacl_K256_Field_fmul(z3, z3, xy_pairs);
  Hacl_K256_Field_fadd(z3, tmp1, z3);
  Hacl_K256_Field_fnormalize_weak(z3, z3);
}

void Hacl_Impl_K256_PointMul_point_mul(uint64_t *out, uint64_t *scalar, uint64_t *q)
{
  uint64_t *px = out;
  uint64_t *py = out + (uint32_t)5U;
  uint64_t *pz = out + (uint32_t)10U;
  memset(px, 0U, (uint32_t)5U * sizeof (uint64_t));
  memset(py, 0U, (uint32_t)5U * sizeof (uint64_t));
  py[0U] = (uint64_t)1U;
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
  {
    uint64_t table[240U] = { 0U };
    uint64_t *t1;
    memcpy(table, out, (uint32_t)15U * sizeof (uint64_t));
    t1 = table + (uint32_t)15U;
    memcpy(t1, q, (uint32_t)15U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i,
      (uint32_t)0U,
      (uint32_t)15U,
      (uint32_t)1U,
      uint64_t *t11 = table + i * (uint32_t)15U;
      uint64_t *t2 = table + i * (uint32_t)15U + (uint32_t)15U;
      Hacl_Impl_K256_PointAdd_point_add(t2, q, t11););
    {
      uint32_t i0;
      for (i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
      {
        KRML_MAYBE_FOR4(i,
          (uint32_t)0U,
          (uint32_t)4U,
          (uint32_t)1U,
          Hacl_Impl_K256_PointDouble_point_double(out, out););
        {
          uint32_t bk = (uint32_t)256U;
          uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
          uint32_t i1 = (bk - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)64U;
          uint32_t j = (bk - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)64U;
          uint64_t p1 = scalar[i1] >> j;
          uint64_t ite;
          if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
          {
            ite = p1 | scalar[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
          }
          else
          {
            ite = p1;
          }
          {
            uint64_t bits_l = ite & mask_l;
            uint64_t a_bits_l[15U] = { 0U };
            memcpy(a_bits_l, table, (uint32_t)15U * sizeof (uint64_t));
            KRML_MAYBE_FOR15(i2,
              (uint32_t)0U,
              (uint32_t)15U,
              (uint32_t)1U,
              uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
              uint64_t *res_j = table + (i2 + (uint32_t)1U) * (uint32_t)15U;
              KRML_MAYBE_FOR15(i,
                (uint32_t)0U,
                (uint32_t)15U,
                (uint32_t)1U,
                uint64_t *os = a_bits_l;
                uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
                os[i] = x;););
            Hacl_Impl_K256_PointAdd_point_add(out, out, a_bits_l);
          }
        }
      }
    }
  }
}

static inline void
point_mul_double_vartime(
  uint64_t *out,
  uint64_t *scalar1,
  uint64_t *q1,
  uint64_t *scalar2,
  uint64_t *q2
)
{
  uint64_t *px = out;
  uint64_t *py = out + (uint32_t)5U;
  uint64_t *pz = out + (uint32_t)10U;
  memset(px, 0U, (uint32_t)5U * sizeof (uint64_t));
  memset(py, 0U, (uint32_t)5U * sizeof (uint64_t));
  py[0U] = (uint64_t)1U;
  memset(pz, 0U, (uint32_t)5U * sizeof (uint64_t));
  {
    uint64_t table1[240U] = { 0U };
    uint64_t *t10;
    memcpy(table1, out, (uint32_t)15U * sizeof (uint64_t));
    t10 = table1 + (uint32_t)15U;
    memcpy(t10, q1, (uint32_t)15U * sizeof (uint64_t));
    KRML_MAYBE_FOR15(i,
      (uint32_t)0U,
      (uint32_t)15U,
      (uint32_t)1U,
      uint64_t *t11 = table1 + i * (uint32_t)15U;
      uint64_t *t2 = table1 + i * (uint32_t)15U + (uint32_t)15U;
      Hacl_Impl_K256_PointAdd_point_add(t2, q1, t11););
    {
      uint64_t table2[240U] = { 0U };
      uint64_t *t1;
      memcpy(table2, out, (uint32_t)15U * sizeof (uint64_t));
      t1 = table2 + (uint32_t)15U;
      memcpy(t1, q2, (uint32_t)15U * sizeof (uint64_t));
      KRML_MAYBE_FOR15(i,
        (uint32_t)0U,
        (uint32_t)15U,
        (uint32_t)1U,
        uint64_t *t11 = table2 + i * (uint32_t)15U;
        uint64_t *t2 = table2 + i * (uint32_t)15U + (uint32_t)15U;
        Hacl_Impl_K256_PointAdd_point_add(t2, q2, t11););
      {
        uint32_t i;
        for (i = (uint32_t)0U; i < (uint32_t)64U; i++)
        {
          KRML_MAYBE_FOR4(i0,
            (uint32_t)0U,
            (uint32_t)4U,
            (uint32_t)1U,
            Hacl_Impl_K256_PointDouble_point_double(out, out););
          {
            uint32_t bk = (uint32_t)256U;
            uint64_t mask_l0 = (uint64_t)16U - (uint64_t)1U;
            uint32_t i10 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
            uint32_t j0 = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
            uint64_t p10 = scalar1[i10] >> j0;
            uint64_t ite0;
            if (i10 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j0)
            {
              ite0 = p10 | scalar1[i10 + (uint32_t)1U] << ((uint32_t)64U - j0);
            }
            else
            {
              ite0 = p10;
            }
            {
              uint64_t bits_l = ite0 & mask_l0;
              uint64_t a_bits_l0[15U] = { 0U };
              uint32_t bits_l320 = (uint32_t)bits_l;
              uint64_t *a_bits_l1 = table1 + bits_l320 * (uint32_t)15U;
              memcpy(a_bits_l0, a_bits_l1, (uint32_t)15U * sizeof (uint64_t));
              Hacl_Impl_K256_PointAdd_point_add(out, out, a_bits_l0);
              {
                uint32_t bk0 = (uint32_t)256U;
                uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
                uint32_t i1 = (bk0 - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
                uint32_t j = (bk0 - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
                uint64_t p1 = scalar2[i1] >> j;
                uint64_t ite;
                if (i1 + (uint32_t)1U < (uint32_t)4U && (uint32_t)0U < j)
                {
                  ite = p1 | scalar2[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
                }
                else
                {
                  ite = p1;
                }
                {
                  uint64_t bits_l0 = ite & mask_l;
                  uint64_t a_bits_l[15U] = { 0U };
                  uint32_t bits_l32 = (uint32_t)bits_l0;
                  uint64_t *a_bits_l10 = table2 + bits_l32 * (uint32_t)15U;
                  memcpy(a_bits_l, a_bits_l10, (uint32_t)15U * sizeof (uint64_t));
                  Hacl_Impl_K256_PointAdd_point_add(out, out, a_bits_l);
                }
              }
            }
          }
        }
      }
    }
  }
}

static inline void point_mul_g(uint64_t *out, uint64_t *scalar)
{
  uint64_t g[15U] = { 0U };
  uint64_t *gx = g;
  uint64_t *gy = g + (uint32_t)5U;
  uint64_t *gz = g + (uint32_t)10U;
  gx[0U] = (uint64_t)0x2815b16f81798U;
  gx[1U] = (uint64_t)0xdb2dce28d959fU;
  gx[2U] = (uint64_t)0xe870b07029bfcU;
  gx[3U] = (uint64_t)0xbbac55a06295cU;
  gx[4U] = (uint64_t)0x79be667ef9dcU;
  gy[0U] = (uint64_t)0x7d08ffb10d4b8U;
  gy[1U] = (uint64_t)0x48a68554199c4U;
  gy[2U] = (uint64_t)0xe1108a8fd17b4U;
  gy[3U] = (uint64_t)0xc4655da4fbfc0U;
  gy[4U] = (uint64_t)0x483ada7726a3U;
  memset(gz, 0U, (uint32_t)5U * sizeof (uint64_t));
  gz[0U] = (uint64_t)1U;
  Hacl_Impl_K256_PointMul_point_mul(out, scalar, g);
}

static inline void
point_mul_g_double_vartime(uint64_t *out, uint64_t *scalar1, uint64_t *scalar2, uint64_t *q2)
{
  uint64_t g[15U] = { 0U };
  uint64_t *gx = g;
  uint64_t *gy = g + (uint32_t)5U;
  uint64_t *gz = g + (uint32_t)10U;
  gx[0U] = (uint64_t)0x2815b16f81798U;
  gx[1U] = (uint64_t)0xdb2dce28d959fU;
  gx[2U] = (uint64_t)0xe870b07029bfcU;
  gx[3U] = (uint64_t)0xbbac55a06295cU;
  gx[4U] = (uint64_t)0x79be667ef9dcU;
  gy[0U] = (uint64_t)0x7d08ffb10d4b8U;
  gy[1U] = (uint64_t)0x48a68554199c4U;
  gy[2U] = (uint64_t)0xe1108a8fd17b4U;
  gy[3U] = (uint64_t)0xc4655da4fbfc0U;
  gy[4U] = (uint64_t)0x483ada7726a3U;
  memset(gz, 0U, (uint32_t)5U * sizeof (uint64_t));
  gz[0U] = (uint64_t)1U;
  point_mul_double_vartime(out, scalar1, g, scalar2, q2);
}

static inline bool load_public_key(uint8_t *pk, uint64_t *fpk_x, uint64_t *fpk_y)
{
  uint8_t *pk_x = pk;
  uint8_t *pk_y = pk + (uint32_t)32U;
  bool is_x_valid = Hacl_K256_Field_load_felem_vartime(fpk_x, pk_x);
  bool is_y_valid = Hacl_K256_Field_load_felem_vartime(fpk_y, pk_y);
  if (is_x_valid && is_y_valid)
  {
    uint64_t y2_exp[5U] = { 0U };
    uint64_t b[5U] = { 0U };
    b[0U] = (uint64_t)0x7U;
    b[1U] = (uint64_t)0U;
    b[2U] = (uint64_t)0U;
    b[3U] = (uint64_t)0U;
    b[4U] = (uint64_t)0U;
    Hacl_K256_Field_fsqr(y2_exp, fpk_x);
    Hacl_K256_Field_fmul(y2_exp, y2_exp, fpk_x);
    Hacl_K256_Field_fadd(y2_exp, y2_exp, b);
    Hacl_K256_Field_fnormalize(y2_exp, y2_exp);
    {
      uint64_t y2_comp[5U] = { 0U };
      Hacl_K256_Field_fsqr(y2_comp, fpk_y);
      Hacl_K256_Field_fnormalize(y2_comp, y2_comp);
      {
        bool res = Hacl_K256_Field_is_felem_eq_vartime(y2_exp, y2_comp);
        bool res0 = res;
        return res0;
      }
    }
  }
  return false;
}

static inline bool fmul_eq_vartime(uint64_t *r, uint64_t *z, uint64_t *x)
{
  uint64_t tmp[5U] = { 0U };
  bool b;
  Hacl_K256_Field_fmul(tmp, r, z);
  Hacl_K256_Field_fnormalize(tmp, tmp);
  b = Hacl_K256_Field_is_felem_eq_vartime(tmp, x);
  return b;
}

/*******************************************************************************
  Verified C library for ECDSA signing and verification on the secp256k1 curve.

  For the comments on low-S normalization (or canonical lowest S value), see:
    • https://en.bitcoin.it/wiki/BIP_0062
    • https://yondon.blog/2019/01/01/how-not-to-use-ecdsa/
    • https://eklitzke.org/bitcoin-transaction-malleability

  For example, bitcoin-core/secp256k1 *always* performs low-S normalization.

*******************************************************************************/


/*
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` and `private_key` < the order of the curve
    • 0 < `nonce` and `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint64_t r_q[4U] = { 0U };
  uint64_t s_q[4U] = { 0U };
  uint64_t d_a[4U] = { 0U };
  uint64_t k_q[4U] = { 0U };
  uint64_t is_sk_valid = load_qelem_check(d_a, private_key);
  uint64_t is_nonce_valid = load_qelem_check(k_q, nonce);
  uint64_t are_sk_nonce_valid = is_sk_valid & is_nonce_valid;
  if (are_sk_nonce_valid == (uint64_t)0U)
  {
    return false;
  }
  {
    uint64_t tmp[5U] = { 0U };
    uint8_t x_bytes[32U] = { 0U };
    uint64_t p[15U] = { 0U };
    point_mul_g(p, k_q);
    {
      uint64_t *x = p;
      uint64_t *z = p + (uint32_t)10U;
      Hacl_Impl_K256_Finv_finv(tmp, z);
      Hacl_K256_Field_fmul(tmp, x, tmp);
      Hacl_K256_Field_fnormalize(tmp, tmp);
      Hacl_K256_Field_store_felem(x_bytes, tmp);
      load_qelem_modq(r_q, x_bytes);
      {
        uint64_t z0[4U] = { 0U };
        uint64_t kinv[4U] = { 0U };
        load_qelem_modq(z0, msgHash);
        qinv(kinv, k_q);
        qmul(s_q, r_q, d_a);
        qadd(s_q, z0, s_q);
        qmul(s_q, kinv, s_q);
        store_qelem(signature, r_q);
        store_qelem(signature + (uint32_t)32U, s_q);
        {
          uint64_t is_r_zero = is_qelem_zero(r_q);
          uint64_t is_s_zero = is_qelem_zero(s_q);
          if
          (is_r_zero == (uint64_t)0xFFFFFFFFFFFFFFFFU || is_s_zero == (uint64_t)0xFFFFFFFFFFFFFFFFU)
          {
            return false;
          }
          return true;
        }
      }
    }
  }
}

/*
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_sign_hashed_msg`.

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint8_t msgHash[32U] = { 0U };
  bool b;
  Hacl_Hash_SHA2_hash_256(msg, msg_len, msgHash);
  b = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  return b;
}

/*
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether a public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(uint8_t *m, uint8_t *public_key, uint8_t *signature)
{
  uint64_t pk_x[5U] = { 0U };
  uint64_t pk_y[5U] = { 0U };
  uint64_t r_q[4U] = { 0U };
  uint64_t s_q[4U] = { 0U };
  uint64_t z[4U] = { 0U };
  bool is_xy_on_curve = load_public_key(public_key, pk_x, pk_y);
  bool is_r_valid = load_qelem_vartime(r_q, signature);
  bool is_s_valid = load_qelem_vartime(s_q, signature + (uint32_t)32U);
  bool res0;
  load_qelem_modq(z, m);
  if (!(is_xy_on_curve && is_r_valid && is_s_valid))
  {
    res0 = false;
  }
  else
  {
    uint64_t p[15U] = { 0U };
    uint64_t res[15U] = { 0U };
    uint64_t *x1 = p;
    uint64_t *y1 = p + (uint32_t)5U;
    uint64_t *z10 = p + (uint32_t)10U;
    memcpy(x1, pk_x, (uint32_t)5U * sizeof (uint64_t));
    memcpy(y1, pk_y, (uint32_t)5U * sizeof (uint64_t));
    memset(z10, 0U, (uint32_t)5U * sizeof (uint64_t));
    z10[0U] = (uint64_t)1U;
    {
      uint64_t sinv[4U] = { 0U };
      uint64_t u1[4U] = { 0U };
      uint64_t u2[4U] = { 0U };
      qinv(sinv, s_q);
      qmul(u1, z, sinv);
      qmul(u2, r_q, sinv);
      point_mul_g_double_vartime(res, u1, u2, p);
      {
        uint64_t tmp[5U] = { 0U };
        uint64_t *pz = res + (uint32_t)10U;
        Hacl_K256_Field_fnormalize(tmp, pz);
        {
          bool b0 = Hacl_K256_Field_is_felem_zero_vartime(tmp);
          bool b;
          if (b0)
          {
            b = false;
          }
          else
          {
            uint64_t *x = res;
            uint64_t *z1 = res + (uint32_t)10U;
            uint8_t r_bytes[32U] = { 0U };
            uint64_t r_fe[5U] = { 0U };
            uint64_t tmp_q[5U] = { 0U };
            uint64_t tmp_x[5U] = { 0U };
            store_qelem(r_bytes, r_q);
            Hacl_K256_Field_load_felem(r_fe, r_bytes);
            Hacl_K256_Field_fnormalize(tmp_x, x);
            {
              bool is_rz_x = fmul_eq_vartime(r_fe, z1, tmp_x);
              bool res1;
              if (!is_rz_x)
              {
                bool is_r_lt_p_m_q = Hacl_K256_Field_is_felem_lt_prime_minus_order_vartime(r_fe);
                if (is_r_lt_p_m_q)
                {
                  tmp_q[0U] = (uint64_t)0x25e8cd0364141U;
                  tmp_q[1U] = (uint64_t)0xe6af48a03bbfdU;
                  tmp_q[2U] = (uint64_t)0xffffffebaaedcU;
                  tmp_q[3U] = (uint64_t)0xfffffffffffffU;
                  tmp_q[4U] = (uint64_t)0xffffffffffffU;
                  Hacl_K256_Field_fadd(tmp_q, r_fe, tmp_q);
                  res1 = fmul_eq_vartime(tmp_q, z1, tmp_x);
                }
                else
                {
                  res1 = false;
                }
              }
              else
              {
                res1 = true;
              }
              b = res1;
            }
          }
          res0 = b;
        }
      }
    }
  }
  return res0;
}

/*
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_verify_hashed_msg`.

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
)
{
  uint8_t mHash[32U] = { 0U };
  bool b;
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  b = Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(mHash, public_key, signature);
  return b;
}

/*
Compute canonical lowest S value for `signature` (R || S).

  The function returns `true` for successful normalization of S and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(uint8_t *signature)
{
  uint64_t s_q[4U] = { 0U };
  uint8_t *s = signature + (uint32_t)32U;
  bool is_sk_valid = load_qelem_vartime(s_q, s);
  if (!is_sk_valid)
  {
    return false;
  }
  {
    bool is_sk_lt_q_halved = is_qelem_le_q_halved_vartime(s_q);
    qnegate_conditional_vartime(s_q, !is_sk_lt_q_halved);
    store_qelem(signature + (uint32_t)32U, s_q);
    return true;
  }
}

/*
Check whether `signature` (R || S) is in canonical form.

  The function returns `true` if S is low-S normalized and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(uint8_t *signature)
{
  uint64_t s_q[4U] = { 0U };
  uint8_t *s = signature + (uint32_t)32U;
  bool is_s_valid = load_qelem_vartime(s_q, s);
  bool is_s_lt_q_halved = is_qelem_le_q_halved_vartime(s_q);
  return is_s_valid && is_s_lt_q_halved;
}

/*
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` and `private_key` < the order of the curve
    • 0 < `nonce` and `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  bool b = Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  if (b)
  {
    return Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(signature);
  }
  return false;
}

/*
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_sign_hashed_msg`.

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
)
{
  uint8_t msgHash[32U] = { 0U };
  bool b;
  Hacl_Hash_SHA2_hash_256(msg, msg_len, msgHash);
  b = Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(signature, msgHash, private_key, nonce);
  return b;
}

/*
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_hashed_msg` if needed.

  The function also checks whether a public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
  uint8_t *msgHash,
  uint8_t *public_key,
  uint8_t *signature
)
{
  bool is_s_normalized = Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(signature);
  if (!is_s_normalized)
  {
    return false;
  }
  return Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(msgHash, public_key, signature);
}

/*
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_verify_hashed_msg`.

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
)
{
  uint8_t mHash[32U] = { 0U };
  bool b;
  Hacl_Hash_SHA2_hash_256(msg, msg_len, mHash);
  b = Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(mHash, public_key, signature);
  return b;
}

/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the secp256k1 curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/


/*
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is valid point.
*/
bool Hacl_K256_ECDSA_public_key_uncompressed_to_raw(uint8_t *pk_raw, uint8_t *pk)
{
  uint8_t pk0 = pk[0U];
  if (pk0 != (uint8_t)0x04U)
  {
    return false;
  }
  memcpy(pk_raw, pk + (uint32_t)1U, (uint32_t)64U * sizeof (uint8_t));
  return true;
}

/*
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
void Hacl_K256_ECDSA_public_key_uncompressed_from_raw(uint8_t *pk, uint8_t *pk_raw)
{
  pk[0U] = (uint8_t)0x04U;
  memcpy(pk + (uint32_t)1U, pk_raw, (uint32_t)64U * sizeof (uint8_t));
}

/*
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is valid point.
*/
bool Hacl_K256_ECDSA_public_key_compressed_to_raw(uint8_t *pk_raw, uint8_t *pk)
{
  uint64_t xa[5U] = { 0U };
  uint64_t ya[5U] = { 0U };
  uint8_t *pk_xb = pk + (uint32_t)1U;
  bool b = Hacl_Impl_K256_Point_aff_point_decompress_vartime(xa, ya, pk);
  if (b)
  {
    memcpy(pk_raw, pk_xb, (uint32_t)32U * sizeof (uint8_t));
    Hacl_K256_Field_store_felem(pk_raw + (uint32_t)32U, ya);
  }
  return b;
}

/*
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
void Hacl_K256_ECDSA_public_key_compressed_from_raw(uint8_t *pk, uint8_t *pk_raw)
{
  uint8_t *pk_x = pk_raw;
  uint8_t *pk_y = pk_raw + (uint32_t)32U;
  uint8_t x0 = pk_y[31U];
  bool is_pk_y_odd = (x0 & (uint8_t)1U) == (uint8_t)1U;
  uint8_t ite;
  if (is_pk_y_odd)
  {
    ite = (uint8_t)0x03U;
  }
  else
  {
    ite = (uint8_t)0x02U;
  }
  pk[0U] = ite;
  memcpy(pk + (uint32_t)1U, pk_x, (uint32_t)32U * sizeof (uint8_t));
}

