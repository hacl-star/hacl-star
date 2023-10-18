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


#include "Hacl_GenericField64.h"

#include "internal/Hacl_Bignum_Base.h"
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


/**
Check whether this library will work for a modulus `n`.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
  • n % 2 = 1
  • 1 < n
*/
bool Hacl_GenericField64_field_modulus_check(uint32_t len, uint64_t *n)
{
  uint64_t m = Hacl_Bignum_Montgomery_bn_check_modulus_u64(len, n);
  return m == 0xFFFFFFFFFFFFFFFFULL;
}

/**
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
  uint64_t *r2 = (uint64_t *)KRML_HOST_CALLOC(len, sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t *n1 = (uint64_t *)KRML_HOST_CALLOC(len, sizeof (uint64_t));
  uint64_t *r21 = r2;
  uint64_t *n11 = n1;
  memcpy(n11, n, len * sizeof (uint64_t));
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(len, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r21);
  uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 res = { .len = len, .n = n11, .mu = mu, .r2 = r21 };
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
  *buf =
    (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *)KRML_HOST_MALLOC(sizeof (
        Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
      ));
  buf[0U] = res;
  return buf;
}

/**
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

/**
Return the size of a modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
uint32_t Hacl_GenericField64_field_get_len(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  return k1.len;
}

/**
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

/**
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

/**
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

/**
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

/**
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

/**
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

/**
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

/**
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
  uint64_t *aMc = (uint64_t *)alloca(k1.len * sizeof (uint64_t));
  memset(aMc, 0U, k1.len * sizeof (uint64_t));
  memcpy(aMc, aM, k1.len * sizeof (uint64_t));
  if (bBits < 200U)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
    uint64_t *ctx = (uint64_t *)alloca((len1 + len1) * sizeof (uint64_t));
    memset(ctx, 0U, (len1 + len1) * sizeof (uint64_t));
    memcpy(ctx, k1.n, len1 * sizeof (uint64_t));
    memcpy(ctx + len1, k1.r2, len1 * sizeof (uint64_t));
    uint64_t sw = 0ULL;
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + len1;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, ctx_n, k1.mu, ctx_r2, resM);
    for (uint32_t i0 = 0U; i0 < bBits; i0++)
    {
      uint32_t i1 = (bBits - i0 - 1U) / 64U;
      uint32_t j = (bBits - i0 - 1U) % 64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & 1ULL;
      uint64_t sw1 = bit ^ sw;
      for (uint32_t i = 0U; i < len1; i++)
      {
        uint64_t dummy = (0ULL - sw1) & (resM[i] ^ aMc[i]);
        resM[i] = resM[i] ^ dummy;
        aMc[i] = aMc[i] ^ dummy;
      }
      uint64_t *ctx_n0 = ctx;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, ctx_n0, k1.mu, aMc, resM, aMc);
      uint64_t *ctx_n1 = ctx;
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, ctx_n1, k1.mu, resM, resM);
      sw = bit;
    }
    uint64_t sw0 = sw;
    for (uint32_t i = 0U; i < len1; i++)
    {
      uint64_t dummy = (0ULL - sw0) & (resM[i] ^ aMc[i]);
      resM[i] = resM[i] ^ dummy;
      aMc[i] = aMc[i] ^ dummy;
    }
  }
  else
  {
    uint32_t bLen;
    if (bBits == 0U)
    {
      bLen = 1U;
    }
    else
    {
      bLen = (bBits - 1U) / 64U + 1U;
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
    uint64_t *ctx = (uint64_t *)alloca((len1 + len1) * sizeof (uint64_t));
    memset(ctx, 0U, (len1 + len1) * sizeof (uint64_t));
    memcpy(ctx, k1.n, len1 * sizeof (uint64_t));
    memcpy(ctx + len1, k1.r2, len1 * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), 16U * len1);
    uint64_t *table = (uint64_t *)alloca(16U * len1 * sizeof (uint64_t));
    memset(table, 0U, 16U * len1 * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t *tmp = (uint64_t *)alloca(len1 * sizeof (uint64_t));
    memset(tmp, 0U, len1 * sizeof (uint64_t));
    uint64_t *t0 = table;
    uint64_t *t1 = table + len1;
    uint64_t *ctx_n0 = ctx;
    uint64_t *ctx_r20 = ctx + len1;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, ctx_n0, k1.mu, ctx_r20, t0);
    memcpy(t1, aMc, len1 * sizeof (uint64_t));
    KRML_MAYBE_FOR7(i,
      0U,
      7U,
      1U,
      uint64_t *t11 = table + (i + 1U) * len1;
      uint64_t *ctx_n1 = ctx;
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, ctx_n1, k1.mu, t11, tmp);
      memcpy(table + (2U * i + 2U) * len1, tmp, len1 * sizeof (uint64_t));
      uint64_t *t2 = table + (2U * i + 2U) * len1;
      uint64_t *ctx_n = ctx;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, ctx_n, k1.mu, aMc, t2, tmp);
      memcpy(table + (2U * i + 3U) * len1, tmp, len1 * sizeof (uint64_t)););
    if (bBits % 4U != 0U)
    {
      uint32_t i0 = bBits / 4U * 4U;
      uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, i0, 4U);
      memcpy(resM, (uint64_t *)(table + 0U * len1), len1 * sizeof (uint64_t));
      KRML_MAYBE_FOR15(i1,
        0U,
        15U,
        1U,
        uint64_t c = FStar_UInt64_eq_mask(bits_c, (uint64_t)(i1 + 1U));
        const uint64_t *res_j = table + (i1 + 1U) * len1;
        for (uint32_t i = 0U; i < len1; i++)
        {
          uint64_t *os = resM;
          uint64_t x = (c & res_j[i]) | (~c & resM[i]);
          os[i] = x;
        });
    }
    else
    {
      uint64_t *ctx_n = ctx;
      uint64_t *ctx_r2 = ctx + len1;
      Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, ctx_n, k1.mu, ctx_r2, resM);
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t *tmp0 = (uint64_t *)alloca(len1 * sizeof (uint64_t));
    memset(tmp0, 0U, len1 * sizeof (uint64_t));
    for (uint32_t i0 = 0U; i0 < bBits / 4U; i0++)
    {
      KRML_MAYBE_FOR4(i,
        0U,
        4U,
        1U,
        uint64_t *ctx_n = ctx;
        Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, ctx_n, k1.mu, resM, resM););
      uint32_t k2 = bBits - bBits % 4U - 4U * i0 - 4U;
      uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, k2, 4U);
      memcpy(tmp0, (uint64_t *)(table + 0U * len1), len1 * sizeof (uint64_t));
      KRML_MAYBE_FOR15(i1,
        0U,
        15U,
        1U,
        uint64_t c = FStar_UInt64_eq_mask(bits_l, (uint64_t)(i1 + 1U));
        const uint64_t *res_j = table + (i1 + 1U) * len1;
        for (uint32_t i = 0U; i < len1; i++)
        {
          uint64_t *os = tmp0;
          uint64_t x = (c & res_j[i]) | (~c & tmp0[i]);
          os[i] = x;
        });
      uint64_t *ctx_n = ctx;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, ctx_n, k1.mu, resM, tmp0, resM);
    }
  }
}

/**
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
  uint64_t *aMc = (uint64_t *)alloca(k1.len * sizeof (uint64_t));
  memset(aMc, 0U, k1.len * sizeof (uint64_t));
  memcpy(aMc, aM, k1.len * sizeof (uint64_t));
  if (bBits < 200U)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
    uint64_t *ctx = (uint64_t *)alloca((len1 + len1) * sizeof (uint64_t));
    memset(ctx, 0U, (len1 + len1) * sizeof (uint64_t));
    memcpy(ctx, k1.n, len1 * sizeof (uint64_t));
    memcpy(ctx + len1, k1.r2, len1 * sizeof (uint64_t));
    uint64_t *ctx_n = ctx;
    uint64_t *ctx_r2 = ctx + len1;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, ctx_n, k1.mu, ctx_r2, resM);
    for (uint32_t i = 0U; i < bBits; i++)
    {
      uint32_t i1 = i / 64U;
      uint32_t j = i % 64U;
      uint64_t tmp = b[i1];
      uint64_t bit = tmp >> j & 1ULL;
      if (!(bit == 0ULL))
      {
        uint64_t *ctx_n0 = ctx;
        Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, ctx_n0, k1.mu, resM, aMc, resM);
      }
      uint64_t *ctx_n0 = ctx;
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, ctx_n0, k1.mu, aMc, aMc);
    }
  }
  else
  {
    uint32_t bLen;
    if (bBits == 0U)
    {
      bLen = 1U;
    }
    else
    {
      bLen = (bBits - 1U) / 64U + 1U;
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), len1 + len1);
    uint64_t *ctx = (uint64_t *)alloca((len1 + len1) * sizeof (uint64_t));
    memset(ctx, 0U, (len1 + len1) * sizeof (uint64_t));
    memcpy(ctx, k1.n, len1 * sizeof (uint64_t));
    memcpy(ctx + len1, k1.r2, len1 * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), 16U * len1);
    uint64_t *table = (uint64_t *)alloca(16U * len1 * sizeof (uint64_t));
    memset(table, 0U, 16U * len1 * sizeof (uint64_t));
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t *tmp = (uint64_t *)alloca(len1 * sizeof (uint64_t));
    memset(tmp, 0U, len1 * sizeof (uint64_t));
    uint64_t *t0 = table;
    uint64_t *t1 = table + len1;
    uint64_t *ctx_n0 = ctx;
    uint64_t *ctx_r20 = ctx + len1;
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, ctx_n0, k1.mu, ctx_r20, t0);
    memcpy(t1, aMc, len1 * sizeof (uint64_t));
    KRML_MAYBE_FOR7(i,
      0U,
      7U,
      1U,
      uint64_t *t11 = table + (i + 1U) * len1;
      uint64_t *ctx_n1 = ctx;
      Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, ctx_n1, k1.mu, t11, tmp);
      memcpy(table + (2U * i + 2U) * len1, tmp, len1 * sizeof (uint64_t));
      uint64_t *t2 = table + (2U * i + 2U) * len1;
      uint64_t *ctx_n = ctx;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, ctx_n, k1.mu, aMc, t2, tmp);
      memcpy(table + (2U * i + 3U) * len1, tmp, len1 * sizeof (uint64_t)););
    if (bBits % 4U != 0U)
    {
      uint32_t i = bBits / 4U * 4U;
      uint64_t bits_c = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, i, 4U);
      uint32_t bits_l32 = (uint32_t)bits_c;
      const uint64_t *a_bits_l = table + bits_l32 * len1;
      memcpy(resM, (uint64_t *)a_bits_l, len1 * sizeof (uint64_t));
    }
    else
    {
      uint64_t *ctx_n = ctx;
      uint64_t *ctx_r2 = ctx + len1;
      Hacl_Bignum_Montgomery_bn_from_mont_u64(len1, ctx_n, k1.mu, ctx_r2, resM);
    }
    KRML_CHECK_SIZE(sizeof (uint64_t), len1);
    uint64_t *tmp0 = (uint64_t *)alloca(len1 * sizeof (uint64_t));
    memset(tmp0, 0U, len1 * sizeof (uint64_t));
    for (uint32_t i = 0U; i < bBits / 4U; i++)
    {
      KRML_MAYBE_FOR4(i0,
        0U,
        4U,
        1U,
        uint64_t *ctx_n = ctx;
        Hacl_Bignum_Montgomery_bn_mont_sqr_u64(len1, ctx_n, k1.mu, resM, resM););
      uint32_t k2 = bBits - bBits % 4U - 4U * i - 4U;
      uint64_t bits_l = Hacl_Bignum_Lib_bn_get_bits_u64(bLen, b, k2, 4U);
      uint32_t bits_l32 = (uint32_t)bits_l;
      const uint64_t *a_bits_l = table + bits_l32 * len1;
      memcpy(tmp0, (uint64_t *)a_bits_l, len1 * sizeof (uint64_t));
      uint64_t *ctx_n = ctx;
      Hacl_Bignum_Montgomery_bn_mont_mul_u64(len1, ctx_n, k1.mu, resM, tmp0, resM);
    }
  }
}

/**
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
  uint64_t *n2 = (uint64_t *)alloca(len1 * sizeof (uint64_t));
  memset(n2, 0U, len1 * sizeof (uint64_t));
  uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(0ULL, k1.n[0U], 2ULL, n2);
  uint64_t c1;
  if (1U < len1)
  {
    uint64_t *a1 = k1.n + 1U;
    uint64_t *res1 = n2 + 1U;
    uint64_t c = c0;
    for (uint32_t i = 0U; i < (len1 - 1U) / 4U; i++)
    {
      uint64_t t1 = a1[4U * i];
      uint64_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i0);
      uint64_t t10 = a1[4U * i + 1U];
      uint64_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t10, 0ULL, res_i1);
      uint64_t t11 = a1[4U * i + 2U];
      uint64_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t11, 0ULL, res_i2);
      uint64_t t12 = a1[4U * i + 3U];
      uint64_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t12, 0ULL, res_i);
    }
    for (uint32_t i = (len1 - 1U) / 4U * 4U; i < len1 - 1U; i++)
    {
      uint64_t t1 = a1[i];
      uint64_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u64(c, t1, 0ULL, res_i);
    }
    uint64_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c0;
  }
  KRML_MAYBE_UNUSED_VAR(c1);
  Hacl_GenericField64_exp_vartime(k, aM, k1.len * 64U, n2, aInvM);
}

