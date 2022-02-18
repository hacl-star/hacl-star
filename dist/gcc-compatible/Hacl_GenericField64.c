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


#include "Hacl_GenericField64.h"

#include "internal/Hacl_Kremlib.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************

A verified field arithmetic library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].

All the arithmetic operations are performed in the Montgomery domain.

All the functions below preserve the following invariant for a bignum `aM` in
Montgomery form.
  • aM < n

*******************************************************************************/


/*
Check whether this library will work for a modulus `n`.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
  • n % 2 = 1
  • 1 < n
*/
bool Hacl_GenericField64_field_modulus_check(uint32_t len, uint64_t *n)
{
  uint64_t m = Hacl_Bignum_Montgomery_bn_check_modulus_u64(len, n);
  return m == (uint64_t)0xFFFFFFFFFFFFFFFFU;
}

/*
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_GenericField64_field_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
*Hacl_GenericField64_field_init(uint32_t len, uint64_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *r2 = KRML_HOST_CALLOC(len, sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *n1 = KRML_HOST_CALLOC(len, sizeof (uint64_t));
  uint64_t *r21 = r2;
  uint64_t *n11 = n1;
  memcpy(n11, n, len * sizeof (uint64_t));
  uint32_t nBits = (uint32_t)64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(len, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r21);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 res = { .len = len, .n = n11, .mu = mu, .r2 = r21 };
  KRML_CHECK_SIZE(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64), (uint32_t)1U);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
  *buf = KRML_HOST_MALLOC(sizeof (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64));
  buf[0U] = res;
  return buf;
}

/*
Deallocate the memory previously allocated by Hacl_GenericField64_field_init.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void Hacl_GenericField64_field_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint64_t *n = k1.n;
  uint64_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/*
Return the size of a modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
uint32_t Hacl_GenericField64_field_get_len(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  return k1.len;
}

/*
Convert a bignum from the regular representation to the Montgomery representation.

  Write `a * R mod n` in `aM`.

  The argument a and the outparam aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void
Hacl_GenericField64_to_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *aM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Montgomery_bn_to_mont_u64(len1, k1.n, k1.mu, k1.r2, a, aM);
}

/*
Convert a result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField64_from_field(k, Hacl_GenericField64_to_field(k, a)) == a % n

  The argument aM and the outparam a are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void
Hacl_GenericField64_from_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *a
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, k1.n, k1.mu, aM, a);
}

/*
Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void
Hacl_GenericField64_add(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_bn_add_mod_n_u64(len1, k1.n, aM, bM, cM);
}

/*
Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void
Hacl_GenericField64_sub(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_bn_sub_mod_n_u64(len1, k1.n, aM, bM, cM);
}

/*
Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void
Hacl_GenericField64_mul(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, aM, bM, cM);
}

/*
Write `aM * aM mod n` in `cM`.

  The argument aM and the outparam cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void
Hacl_GenericField64_sqr(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *cM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, aM, cM);
}

/*
Convert a bignum `one` to its Montgomery representation.

  The outparam oneM is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void Hacl_GenericField64_one(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k, uint64_t *oneM)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, k1.n, k1.mu, k1.r2, oneM);
}

/*
Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than exp_vartime.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • b < pow2 bBits
*/
void
Hacl_GenericField64_exp_consttime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *resM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), k1.len);
  uint64_t aMc[k1.len];
  memset(aMc, 0U, k1.len * sizeof (uint64_t));
  memcpy(aMc, aM, k1.len * sizeof (uint64_t));
  if (bBits < (uint32_t)200U)
  {
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, k1.n, k1.mu, k1.r2, resM);
    uint64_t sw = (uint64_t)0U;
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - (uint32_t)1U) / (uint32_t)64U;
      uint32_t j = (bBits - i0 - (uint32_t)1U) % (uint32_t)64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & (uint64_t)1U;
      uint64_t sw1 = bit ^ sw;
      for (uint32_t i = (uint32_t)0U; i < len1; i++)
      {
        uint64_t dummy = ((uint64_t)0U - sw1) & (resM[i] ^ aMc[i]);
        resM[i] = resM[i] ^ dummy;
        aMc[i] = aMc[i] ^ dummy;
      }
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, aMc, resM, aMc);
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
      sw = bit;
    }
    uint64_t sw0 = sw;
    for (uint32_t i = (uint32_t)0U; i < len1; i++)
    {
      uint64_t dummy = ((uint64_t)0U - sw0) & (resM[i] ^ aMc[i]);
      resM[i] = resM[i] ^ dummy;
      aMc[i] = aMc[i] ^ dummy;
    }
  }
  else
  {
    uint32_t bLen;
    if (bBits == (uint32_t)0U)
    {
      bLen = (uint32_t)1U;
    }
    else
    {
      bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, k1.n, k1.mu, k1.r2, resM);
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * len1);
    uint64_t table[(uint32_t)16U * len1];
    memset(table, 0U, (uint32_t)16U * len1 * sizeof (uint64_t));
    memcpy(table, resM, len1 * sizeof (uint64_t));
    uint64_t *t1 = table + len1;
    memcpy(t1, aMc, len1 * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)14U; i++)
    {
      uint64_t *t11 = table + (i + (uint32_t)1U) * len1;
      uint64_t *t2 = table + (i + (uint32_t)2U) * len1;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, t11, aMc, t2);
    }
    if (bBits % (uint32_t)4U != (uint32_t)0U)
    {
      uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
      uint32_t i0 = bBits / (uint32_t)4U * (uint32_t)4U / (uint32_t)64U;
      uint32_t j = bBits / (uint32_t)4U * (uint32_t)4U % (uint32_t)64U;
      uint64_t p1 = b[i0] >> j;
      uint64_t ite;
      if (i0 + (uint32_t)1U < bLen && (uint32_t)0U < j)
      {
        ite = p1 | b[i0 + (uint32_t)1U] << ((uint32_t)64U - j);
      }
      else
      {
        ite = p1;
      }
      uint64_t bits_c = ite & mask_l;
      memcpy(resM, table, len1 * sizeof (uint64_t));
      for (uint32_t i1 = (uint32_t)0U; i1 < (uint32_t)15U; i1++)
      {
        uint64_t c = FStar_UInt64_eq_mask(bits_c, (uint64_t)(i1 + (uint32_t)1U));
        uint64_t *res_j = table + (i1 + (uint32_t)1U) * len1;
        for (uint32_t i = (uint32_t)0U; i < len1; i++)
        {
          uint64_t *os = resM;
          uint64_t x = (c & res_j[i]) | (~c & resM[i]);
          os[i] = x;
        }
      }
    }
    for (uint32_t i0 = (uint32_t)0U; i0 < bBits / (uint32_t)4U; i0++)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
      {
        Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
      }
      uint32_t bk = bBits - bBits % (uint32_t)4U;
      uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
      uint32_t i1 = (bk - (uint32_t)4U * i0 - (uint32_t)4U) / (uint32_t)64U;
      uint32_t j = (bk - (uint32_t)4U * i0 - (uint32_t)4U) % (uint32_t)64U;
      uint64_t p1 = b[i1] >> j;
      uint64_t ite;
      if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
      {
        ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
      }
      else
      {
        ite = p1;
      }
      uint64_t bits_l = ite & mask_l;
      KRML_CHECK_SIZE(sizeof (uint64_t), len1);
      uint64_t a_bits_l[len1];
      memset(a_bits_l, 0U, len1 * sizeof (uint64_t));
      memcpy(a_bits_l, table, len1 * sizeof (uint64_t));
      for (uint32_t i2 = (uint32_t)0U; i2 < (uint32_t)15U; i2++)
      {
        uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i2 + (uint32_t)1U));
        uint64_t *res_j = table + (i2 + (uint32_t)1U) * len1;
        for (uint32_t i = (uint32_t)0U; i < len1; i++)
        {
          uint64_t *os = a_bits_l;
          uint64_t x = (c & res_j[i]) | (~c & a_bits_l[i]);
          os[i] = x;
        }
      }
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, resM, a_bits_l, resM);
    }
  }
}

/*
Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  exp_consttime function for constant-time variant.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • b < pow2 bBits
*/
void
Hacl_GenericField64_exp_vartime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *resM
)
{
  uint32_t len1 = Hacl_GenericField64_field_get_len(k);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), k1.len);
  uint64_t aMc[k1.len];
  memset(aMc, 0U, k1.len * sizeof (uint64_t));
  memcpy(aMc, aM, k1.len * sizeof (uint64_t));
  if (bBits < (uint32_t)200U)
  {
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, k1.n, k1.mu, k1.r2, resM);
    for (uint32_t i = (uint32_t)0U; i < bBits; i++)
    {
      uint32_t i1 = i / (uint32_t)64U;
      uint32_t j = i % (uint32_t)64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & (uint64_t)1U;
      if (!(bit == (uint64_t)0U))
      {
        Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, resM, aMc, resM);
      }
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, aMc, aMc);
    }
  }
  else
  {
    uint32_t bLen;
    if (bBits == (uint32_t)0U)
    {
      bLen = (uint32_t)1U;
    }
    else
    {
      bLen = (bBits - (uint32_t)1U) / (uint32_t)64U + (uint32_t)1U;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, k1.n, k1.mu, k1.r2, resM);
    KRML_CHECK_SIZE(sizeof (uint64_t), (uint32_t)16U * len1);
    uint64_t table[(uint32_t)16U * len1];
    memset(table, 0U, (uint32_t)16U * len1 * sizeof (uint64_t));
    memcpy(table, resM, len1 * sizeof (uint64_t));
    uint64_t *t1 = table + len1;
    memcpy(t1, aMc, len1 * sizeof (uint64_t));
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)14U; i++)
    {
      uint64_t *t11 = table + (i + (uint32_t)1U) * len1;
      uint64_t *t2 = table + (i + (uint32_t)2U) * len1;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, t11, aMc, t2);
    }
    if (bBits % (uint32_t)4U != (uint32_t)0U)
    {
      uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
      uint32_t i = bBits / (uint32_t)4U * (uint32_t)4U / (uint32_t)64U;
      uint32_t j = bBits / (uint32_t)4U * (uint32_t)4U % (uint32_t)64U;
      uint64_t p1 = b[i] >> j;
      uint64_t ite;
      if (i + (uint32_t)1U < bLen && (uint32_t)0U < j)
      {
        ite = p1 | b[i + (uint32_t)1U] << ((uint32_t)64U - j);
      }
      else
      {
        ite = p1;
      }
      uint64_t bits_c = ite & mask_l;
      uint32_t bits_l32 = (uint32_t)bits_c;
      uint64_t *a_bits_l = table + bits_l32 * len1;
      memcpy(resM, a_bits_l, len1 * sizeof (uint64_t));
    }
    for (uint32_t i = (uint32_t)0U; i < bBits / (uint32_t)4U; i++)
    {
      for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
      {
        Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, k1.n, k1.mu, resM, resM);
      }
      uint32_t bk = bBits - bBits % (uint32_t)4U;
      uint64_t mask_l = (uint64_t)16U - (uint64_t)1U;
      uint32_t i1 = (bk - (uint32_t)4U * i - (uint32_t)4U) / (uint32_t)64U;
      uint32_t j = (bk - (uint32_t)4U * i - (uint32_t)4U) % (uint32_t)64U;
      uint64_t p1 = b[i1] >> j;
      uint64_t ite;
      if (i1 + (uint32_t)1U < bLen && (uint32_t)0U < j)
      {
        ite = p1 | b[i1 + (uint32_t)1U] << ((uint32_t)64U - j);
      }
      else
      {
        ite = p1;
      }
      uint64_t bits_l = ite & mask_l;
      KRML_CHECK_SIZE(sizeof (uint64_t), len1);
      uint64_t a_bits_l[len1];
      memset(a_bits_l, 0U, len1 * sizeof (uint64_t));
      uint32_t bits_l32 = (uint32_t)bits_l;
      uint64_t *a_bits_l1 = table + bits_l32 * len1;
      memcpy(a_bits_l, a_bits_l1, len1 * sizeof (uint64_t));
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, k1.n, k1.mu, resM, a_bits_l, resM);
    }
  }
}

/*
Write `aM ^ (-1) mod n` in `aInvM`.

  The argument aM and the outparam aInvM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < aM
*/
void
Hacl_GenericField64_inverse(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *aInvM
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint32_t len1 = k1.len;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t n2[len1];
  memset(n2, 0U, len1 * sizeof (uint64_t));
  uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64((uint64_t)0U, k1.n[0U], (uint64_t)2U, n2);
  uint64_t c1;
  if ((uint32_t)1U < len1)
  {
    uint32_t rLen = len1 - (uint32_t)1U;
    uint64_t *a1 = k1.n + (uint32_t)1U;
    uint64_t *res1 = n2 + (uint32_t)1U;
    uint64_t c = c0;
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
    c1 = c0;
  }
  Hacl_GenericField64_exp_vartime(k, aM, k1.len * (uint32_t)64U, n2, aInvM);
}

