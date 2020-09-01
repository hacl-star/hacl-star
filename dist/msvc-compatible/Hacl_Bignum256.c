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


#include "Hacl_Bignum256.h"

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum256_add(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_add_carry_u64(c, t1, t2, res + i);
  }
  return c;
}

/*
Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[64]
*/
uint64_t Hacl_Bignum256_sub(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, res + i);
  }
  return c;
}

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint64_t[64].
  The outparam res is meant to be a 8192-bit bignum, i.e. uint64_t[128].
*/
void Hacl_Bignum256_mul(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)8U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i], uu____0, res_ + i);
    }
    uint64_t r = c;
    res[(uint32_t)4U + i0] = r;
  }
}

static void bit_set(uint64_t *input, uint32_t ind)
{
  uint32_t i = ind / (uint32_t)64U;
  uint32_t j = ind % (uint32_t)64U;
  input[i] = input[i] | (uint64_t)1U << j;
}

static void add_mod_n(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint64_t tmp[4U] = { 0U };
  uint64_t c0 = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = b[i];
    c0 = Lib_IntTypes_Intrinsics_add_carry_u64(c0, t1, t2, res + i);
  }
  uint64_t c00 = c0;
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = res[i];
    uint64_t t2 = n[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, tmp + i);
  }
  uint64_t c1 = c;
  uint64_t c2 = c00 - c1;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = res;
    uint64_t x = (c2 & res[i]) | (~c2 & tmp[i]);
    os[i] = x;
  }
}

static void sub_mask(uint64_t *n, uint64_t *a)
{
  uint64_t mask = (uint64_t)0xFFFFFFFFFFFFFFFFU;
  uint64_t mod_mask[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(n[i], a[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t *os = mod_mask;
    uint64_t x = n[i];
    uint64_t x0 = mask1 & x;
    os[i] = x0;
  }
  uint64_t c = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t t1 = a[i];
    uint64_t t2 = mod_mask[i];
    c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, t2, a + i);
  }
  uint64_t uu____1 = c;
}

static void mul_(uint64_t *a, uint64_t *b, uint64_t *res)
{
  uint32_t resLen = (uint32_t)10U;
  memset(res, 0U, resLen * sizeof (uint64_t));
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
  {
    uint64_t uu____0 = b[i0];
    uint64_t *res_ = res + i0;
    uint64_t c = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
    {
      c = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c, a[i], uu____0, res_ + i);
    }
    uint64_t r = c;
    res[(uint32_t)5U + i0] = r;
  }
}

static void precomp(uint32_t modBits, uint64_t *n, uint64_t *res)
{
  memset(res, 0U, (uint32_t)4U * sizeof (uint64_t));
  bit_set(res, modBits - (uint32_t)1U);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)641U - modBits; i++)
  {
    add_mod_n(n, res, res, res);
  }
}

static void reduction(uint64_t *n, uint64_t nInv_u64, uint64_t *c, uint64_t *res)
{
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U + (uint32_t)1U; i0++)
  {
    uint64_t qj = nInv_u64 * c[i0];
    uint64_t *res_ = c + i0;
    uint64_t c1 = (uint64_t)0U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
    {
      c1 = Hacl_Bignum_Multiplication_mul_carry_add_u64_st(c1, n[i], qj, res_ + i);
    }
    uint64_t r0 = c1;
    uint64_t c10 = r0;
    uint64_t c2 = c10;
    uint64_t *res2 = c + i0 + (uint32_t)4U;
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
    ((uint32_t)1U < (uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U - i0 - (uint32_t)4U)
    {
      uint32_t
      rLen =
        (uint32_t)4U
        + (uint32_t)1U
        + (uint32_t)4U + (uint32_t)1U
        - i0
        - (uint32_t)4U
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
    c + (uint32_t)4U + (uint32_t)1U,
    ((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U - ((uint32_t)4U + (uint32_t)1U))
    * sizeof (uint64_t));
}

static void to(uint64_t *n, uint64_t nInv_u64, uint64_t *r2, uint64_t *a, uint64_t *aM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U);
  uint64_t
  *tmp = alloca(((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  memset(tmp,
    0U,
    ((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  uint64_t *c = tmp;
  Hacl_Bignum256_mul(a, r2, c);
  reduction(n, nInv_u64, tmp, aM);
}

static void from(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *a)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U);
  uint64_t
  *tmp = alloca(((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  memset(tmp,
    0U,
    ((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  memcpy(tmp, aM, ((uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U + (uint32_t)1U);
  uint64_t *a_ = alloca(((uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  memset(a_, 0U, ((uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  reduction(n, nInv_u64, tmp, a_);
  memcpy(a, a_, (uint32_t)4U * sizeof (uint64_t));
}

static void
mont_mul(uint64_t *n, uint64_t nInv_u64, uint64_t *aM, uint64_t *bM, uint64_t *resM)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U);
  uint64_t
  *c = alloca(((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  memset(c, 0U, ((uint32_t)4U + (uint32_t)1U + (uint32_t)4U + (uint32_t)1U) * sizeof (uint64_t));
  mul_(aM, bM, c);
  reduction(n, nInv_u64, c, resM);
}

static void
mod_exp_loop(
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
      mont_mul(n, nInv_u64, aM, accM, accM);
    }
    mont_mul(n, nInv_u64, aM, aM, aM);
  }
}

/*
Write `a ^ b mod n1` in `res`.

  The arguments a, n1 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[64].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. For instance, if b is a 256-bit bignum,
  bBits should be 256.
*/
void
Hacl_Bignum256_mod_exp(uint64_t *n, uint64_t *a, uint32_t bBits, uint64_t *b, uint64_t *res)
{
  uint64_t acc[4U] = { 0U };
  memset(acc, 0U, (uint32_t)4U * sizeof (uint64_t));
  acc[0U] = (uint64_t)1U;
  uint32_t rLen = (uint32_t)5U;
  uint32_t bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
  uint64_t nInv_u64 = Hacl_Bignum_ModInv64_mod_inv_u64(n[0U]);
  uint64_t r2[4U] = { 0U };
  precomp((uint32_t)256U, n, r2);
  KRML_CHECK_SIZE(sizeof (uint64_t), rLen);
  uint64_t *aM = alloca(rLen * sizeof (uint64_t));
  memset(aM, 0U, rLen * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), rLen);
  uint64_t *accM = alloca(rLen * sizeof (uint64_t));
  memset(accM, 0U, rLen * sizeof (uint64_t));
  to(n, nInv_u64, r2, a, aM);
  to(n, nInv_u64, r2, acc, accM);
  mod_exp_loop(n, nInv_u64, bBits, bLen, b, aM, accM);
  from(n, nInv_u64, accM, res);
  sub_mask(n, res);
}


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
    result of loading b, or NULL if the amount of required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum256_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if
  (
    len
    == (uint32_t)0U
    || !((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U <= (uint32_t)536870911U)
  )
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U);
  uint64_t
  *res = KRML_HOST_CALLOC((len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U, sizeof (uint64_t));
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    uint64_t *os = res2;
    uint64_t u = load64_be(tmp + (bnLen - i - (uint32_t)1U) * (uint32_t)8U);
    uint64_t x = u;
    os[i] = x;
  }
  return res2;
}

/*
Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 512 bytes of valid memory.
*/
void Hacl_Bignum256_bn_to_bytes_be(uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = ((uint32_t)32U - (uint32_t)1U) / (uint32_t)8U + (uint32_t)1U;
  uint32_t tmpLen = (uint32_t)8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = (uint32_t)0U; i < bnLen; i++)
  {
    store64_be(tmp + i * (uint32_t)8U, b[bnLen - i - (uint32_t)1U]);
  }
  memcpy(res, tmp + tmpLen - (uint32_t)32U, (uint32_t)32U * sizeof (uint8_t));
}


/***************/
/* Comparisons */
/***************/


/*
Returns true if and only if argument a is strictly less than the argument b.
*/
bool Hacl_Bignum256_lt(uint64_t *a, uint64_t *b)
{
  uint64_t acc = (uint64_t)0U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], b[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & (uint64_t)0xFFFFFFFFFFFFFFFFU) | (~blt & (uint64_t)0U)));
  }
  uint64_t mask = acc;
  return mask == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

