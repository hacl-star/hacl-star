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


#include "Hacl_Bignum4096.h"

/*
Write `a + b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum4096_add(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res + i);
  }
  return c;
}

/*
Write `a - b mod 2^4096` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 4096-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum4096_sub(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res + i);
  }
  return c;
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128].
*/
void Hacl_Bignum4096_mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)128U;
  memset(res, 0U, resLen * sizeof (res[0U]));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U; i0++)
  {
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i], uu____0, res_ + i);
    }
    uint64_t r = c;
    res[(uint32_t)64U + i0] = r;
  }
}

static void bit_set(uint64_t *input, uint32_t ind)
{
  uint32_t i = ind / (uint32_t)64U;
  uint32_t j = ind % (uint32_t)64U;
  input[i] = input[i] | (uint64_t)1U << j;
}

static void add_mod_n(uint64_t *n1, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t tmp[64U] = { 0U };
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
  }
  uint64_t c00 = c0;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n1[i];
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

static void sub_mask(uint64_t *n1, uint64_t *a)
{
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t mod_mask[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(n1[i], a[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t *os = mod_mask;
    uint64_t x = n1[i];
    uint64_t x0 = mask1 & x;
    os[i] = x0;
  }
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = mod_mask[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, a + i);
  }
  uint64_t uu____1 = c;
}

static void mul_(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)130U;
  memset(res, 0U, resLen * sizeof (res[0U]));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)65U; i0++)
  {
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)65U; i++)
    {
      c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i], uu____0, res_ + i);
    }
    uint64_t r = c;
    res[(uint32_t)65U + i0] = r;
  }
}

static void precomp(uint32_t modBits, uint64_t *n1, uint64_t *res)
{
  memset(res, 0U, (uint32_t)64U * sizeof (res[0U]));
  bit_set(res, modBits - (uint32_t)1U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8321U - modBits; i++)
  {
    add_mod_n(n1, res, res, res);
  }
}

static void reduction(uint64_t *n1, uint64_t nInv_u64, uint64_t *c, uint64_t *res)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)64U + (uint32_t)1U; i0++)
  {
    uint64_t qj = nInv_u64 * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)64U; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n1[i], qj, res_ + i);
    }
    uint64_t r0 = c1;
    uint64_t c10 = r0;
    uint64_t c2 = c10;
    uint64_t *res2 = c + i0 + (uint32_t)64U;
    uint64_t *a0 = res2;
    uint64_t *res0 = res2;
    uint64_t c30 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)1U; i++)
    {
      uint64_t t1 = a0[i];
      uint64_t t2 = (&c2)[i];
      c30 = Lib_IntTypes_Intrinsics_add_carry_u64(c30, t1, t2, res0 + i);
    }
    uint64_t c0 = c30;
    uint64_t r;
    if
    (
      (uint32_t)1U
      < (uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U - i0 - (uint32_t)64U
    )
    {
      uint32_t
      rLen =
        (uint32_t)64U
        + (uint32_t)1U
        + (uint32_t)64U + (uint32_t)1U
        - i0
        - (uint32_t)64U
        - (uint32_t)1U;
      uint64_t *a1 = res2 + (uint32_t)1U;
      uint64_t *res1 = res2 + (uint32_t)1U;
      uint64_t c3 = c0;
      for (uint32_t i = (uint32_t)0U; i < rLen; i++)
      {
        uint64_t t1 = a1[i];
        c3 = Lib_IntTypes_Intrinsics_add_carry_u64(c3, t1, (uint64_t)0U, res1 + i);
      }
      uint64_t c11 = c3;
      r = c11;
    }
    else
    {
      r = c0;
    }
    uint64_t uu____0 = r;
  }
  memcpy(res,
    c + (uint32_t)64U + (uint32_t)1U,
    ((uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U - ((uint32_t)64U + (uint32_t)1U))
    * sizeof ((c + (uint32_t)64U + (uint32_t)1U)[0U]));
}

static void to(uint64_t *n1, uint64_t nInv_u64, uint64_t *r2, uint64_t *a, uint64_t *aM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t),
    (uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U);
  uint64_t tmp[(uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U];
  memset(tmp,
    0U,
    ((uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U) * sizeof (tmp[0U]));
  uint64_t *c = tmp;
  Hacl_Bignum4096_mul(a, r2, c);
  reduction(n1, nInv_u64, tmp, aM);
}

static void from(uint64_t *n1, uint64_t nInv_u64, uint64_t *aM, uint64_t *a)
{
  KRML_CHECK_SIZE(sizeof (uint64_t),
    (uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U);
  uint64_t tmp[(uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U];
  memset(tmp,
    0U,
    ((uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U) * sizeof (tmp[0U]));
  memcpy(tmp, aM, ((uint32_t)64U + (uint32_t)1U) * sizeof (aM[0U]));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)64U + (uint32_t)1U);
  uint64_t a_[(uint32_t)64U + (uint32_t)1U];
  memset(a_, 0U, ((uint32_t)64U + (uint32_t)1U) * sizeof (a_[0U]));
  reduction(n1, nInv_u64, tmp, a_);
  memcpy(a, a_, (uint32_t)64U * sizeof (a_[0U]));
}

static void
mont_mul(uint64_t *n1, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t),
    (uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U);
  uint64_t c[(uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U];
  memset(c, 0U, ((uint32_t)64U + (uint32_t)1U + (uint32_t)64U + (uint32_t)1U) * sizeof (c[0U]));
  mul_(aM, bM, c);
  reduction(n1, nInv_u64, c, resM);
}

static void
mod_exp_loop(
  uint64_t *n1,
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
      mont_mul(n1, nInv_u64, aM, accM, accM);
    }
    mont_mul(n1, nInv_u64, aM, aM, aM);
  }
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 4096-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128].
*/
void
Hacl_Bignum4096_mod_exp(uint64_t *n1, uint64_t *a, uint32_t bBits, uint64_t *b, uint64_t *res)
{
  uint64_t acc[64U] = { 0U };
  memset(acc, 0U, (uint32_t)64U * sizeof (acc[0U]));
  acc[0U] = (uint64_t)1U;
  uint32_t rLen = (uint32_t)65U;
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv_u64 = Hacl_Bignum_Montgomery_mod_inv_u64(n1[0U]);
  uint64_t r2[64U] = { 0U };
  precomp((uint32_t)4096U, n1, r2);
  KRML_CHECK_SIZE(sizeof (uint64_t), rLen);
  uint64_t aM[rLen];
  memset(aM, 0U, rLen * sizeof (aM[0U]));
  KRML_CHECK_SIZE(sizeof (uint64_t), rLen);
  uint64_t accM[rLen];
  memset(accM, 0U, rLen * sizeof (accM[0U]));
  to(n1, nInv_u64, r2, a, aM);
  to(n1, nInv_u64, r2, acc, accM);
  mod_exp_loop(n1, nInv_u64, bBits, bLen, b, aM, accM);
  from(n1, nInv_u64, accM, res);
  sub_mask(n1, res);
}

