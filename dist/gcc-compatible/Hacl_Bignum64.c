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


#include "Hacl_Bignum64.h"

#include "internal/Hacl_Bignum_Base.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************

A verified bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/**
Write `a + b mod 2 ^ (64 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len]
*/
uint64_t Hacl_Bignum64_add(uint32_t len, uint64_t *a, uint64_t *b, uint64_t *res)
{
  return Hacl_Bignum_Addition_bn_add_eq_len_u64(len, a, b, res);
}

/**
Write `a - b mod 2 ^ (64 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len]
*/
uint64_t Hacl_Bignum64_sub(uint32_t len, uint64_t *a, uint64_t *b, uint64_t *res)
{
  return Hacl_Bignum_Addition_bn_sub_eq_len_u64(len, a, b, res);
}

/**
Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum64_add_mod(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  Hacl_Bignum_bn_add_mod_n_u64(len, n, a, b, res);
}

/**
Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum64_sub_mod(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res)
{
  Hacl_Bignum_bn_sub_mod_n_u64(len, n, a, b, res);
}

/**
Write `a * b` in `res`.

  The arguments a and b are meant to be `len` limbs in size, i.e. uint64_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint64_t[2*len].
*/
void Hacl_Bignum64_mul(uint32_t len, uint64_t *a, uint64_t *b, uint64_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len, a, b, tmp, res);
}

/**
Write `a * a` in `res`.

  The argument a is meant to be `len` limbs in size, i.e. uint64_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint64_t[2*len].
*/
void Hacl_Bignum64_sqr(uint32_t len, uint64_t *a, uint64_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), 4U * len);
  uint64_t tmp[4U * len];
  memset(tmp, 0U, 4U * len * sizeof (uint64_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len, a, tmp, res);
}

static inline void
bn_slow_precomp(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint64_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t a_mod[len];
  memset(a_mod, 0U, len * sizeof (uint64_t));
  KRML_CHECK_SIZE(sizeof (uint64_t), len + len);
  uint64_t a1[len + len];
  memset(a1, 0U, (len + len) * sizeof (uint64_t));
  memcpy(a1, a, (len + len) * sizeof (uint64_t));
  Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(len, n, mu, a1, a_mod);
  Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a_mod, res);
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be `2*len` limbs in size, i.e. uint64_t[2*len].
  The argument n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1 
*/
bool Hacl_Bignum64_mod(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *res)
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
  uint64_t is_valid_m = m0 & m1;
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(len, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t r2[len];
    memset(r2, 0U, len * sizeof (uint64_t));
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2);
    uint64_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint64(n[0U]);
    bn_slow_precomp(len, n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
bool
Hacl_Bignum64_mod_exp_vartime(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64(len, n, a, bBits, b);
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(len, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64(len, nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • n % 2 = 1
   • 1 < n
   • b < pow2 bBits
   • a < n
*/
bool
Hacl_Bignum64_mod_exp_consttime(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  uint64_t is_valid_m = Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64(len, n, a, bBits, b);
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(len, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64(len, nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}

/**
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime

  The function returns false if any of the following preconditions are violated,
  true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n
*/
bool Hacl_Bignum64_mod_inv_prime_vartime(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *res)
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
  uint64_t m1 = acc0;
  uint64_t m00 = m0 & m1;
  KRML_CHECK_SIZE(sizeof (uint64_t), len);
  uint64_t bn_zero[len];
  memset(bn_zero, 0U, len * sizeof (uint64_t));
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  uint64_t res10 = mask1;
  uint64_t m10 = res10;
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], n[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  uint64_t m2 = acc;
  uint64_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t nBits = 64U * (uint32_t)Hacl_Bignum_Lib_bn_get_top_index_u64(len, n);
  if (is_valid_m == 0xFFFFFFFFFFFFFFFFULL)
  {
    KRML_CHECK_SIZE(sizeof (uint64_t), len);
    uint64_t n2[len];
    memset(n2, 0U, len * sizeof (uint64_t));
    uint64_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u64(0ULL, n[0U], 2ULL, n2);
    uint64_t c1;
    if (1U < len)
    {
      uint64_t *a1 = n + 1U;
      uint64_t *res1 = n2 + 1U;
      uint64_t c = c0;
      for (uint32_t i = 0U; i < (len - 1U) / 4U; i++)
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
      for (uint32_t i = (len - 1U) / 4U * 4U; i < len - 1U; i++)
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
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64(len, nBits, n, a, 64U * len, n2, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint64_t));
  }
  return is_valid_m == 0xFFFFFFFFFFFFFFFFULL;
}


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum64_mont_ctx_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
*Hacl_Bignum64_mont_ctx_init(uint32_t len, uint64_t *n)
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
Deallocate the memory previously allocated by Hacl_Bignum64_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.
*/
void Hacl_Bignum64_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  uint64_t *n = k1.n;
  uint64_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/**
Write `a mod n` in `res`.

  The argument a is meant to be `2*len` limbs in size, i.e. uint64_t[2*len].
  The outparam res is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.
*/
void
Hacl_Bignum64_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  bn_slow_precomp(len1, k1.n, k1.mu, k1.r2, a, res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_consttime_* functions for constant-time variants.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum64_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(len1,
    k1.n,
    k1.mu,
    k1.r2,
    a,
    bBits,
    b,
    res);
}

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_vartime_*.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • b < pow2 bBits
  • a < n
*/
void
Hacl_Bignum64_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(len1,
    k1.n,
    k1.mu,
    k1.r2,
    a,
    bBits,
    b,
    res);
}

/**
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum64_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n
*/
void
Hacl_Bignum64_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint64_t), len1);
  uint64_t n2[len1];
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
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(len1,
    k1.n,
    k1.mu,
    k1.r2,
    a,
    64U * len1,
    n2,
    res);
}


/********************/
/* Loads and stores */
/********************/


/**
Load a bid-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum64_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if (len == 0U || !((len - 1U) / 8U + 1U <= 536870911U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - 1U) / 8U + 1U);
  uint64_t *res = (uint64_t *)KRML_HOST_CALLOC((len - 1U) / 8U + 1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 8U + 1U;
  uint32_t tmpLen = 8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    uint64_t *os = res2;
    uint64_t u = load64_be(tmp + (bnLen - i - 1U) * 8U);
    uint64_t x = u;
    os[i] = x;
  }
  return res2;
}

/**
Load a little-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum64_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if (len == 0U || !((len - 1U) / 8U + 1U <= 536870911U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint64_t), (len - 1U) / 8U + 1U);
  uint64_t *res = (uint64_t *)KRML_HOST_CALLOC((len - 1U) / 8U + 1U, sizeof (uint64_t));
  if (res == NULL)
  {
    return res;
  }
  uint64_t *res1 = res;
  uint64_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 8U + 1U;
  uint32_t tmpLen = 8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < (len - 1U) / 8U + 1U; i++)
  {
    uint64_t *os = res2;
    uint8_t *bj = tmp + i * 8U;
    uint64_t u = load64_le(bj);
    uint64_t r1 = u;
    uint64_t x = r1;
    os[i] = x;
  }
  return res2;
}

/**
Serialize a bignum into big-endian memory.

  The argument b points to a bignum of ⌈len / 8⌉ size.
  The outparam res points to `len` bytes of valid memory.
*/
void Hacl_Bignum64_bn_to_bytes_be(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - 1U) / 8U + 1U;
  uint32_t tmpLen = 8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    store64_be(tmp + i * 8U, b[bnLen - i - 1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
}

/**
Serialize a bignum into little-endian memory.

  The argument b points to a bignum of ⌈len / 8⌉ size.
  The outparam res points to `len` bytes of valid memory.
*/
void Hacl_Bignum64_bn_to_bytes_le(uint32_t len, uint64_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - 1U) / 8U + 1U;
  uint32_t tmpLen = 8U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t tmp[tmpLen];
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    store64_le(tmp + i * 8U, b[i]);
  }
  memcpy(res, tmp, len * sizeof (uint8_t));
}


/***************/
/* Comparisons */
/***************/


/**
Returns 2^64 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be `len` limbs in size, i.e. uint64_t[len].
*/
uint64_t Hacl_Bignum64_lt_mask(uint32_t len, uint64_t *a, uint64_t *b)
{
  uint64_t acc = 0ULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t beq = FStar_UInt64_eq_mask(a[i], b[i]);
    uint64_t blt = ~FStar_UInt64_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & ((blt & 0xFFFFFFFFFFFFFFFFULL) | (~blt & 0ULL)));
  }
  return acc;
}

/**
Returns 2^64 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be `len` limbs in size, i.e. uint64_t[len].
*/
uint64_t Hacl_Bignum64_eq_mask(uint32_t len, uint64_t *a, uint64_t *b)
{
  uint64_t mask = 0xFFFFFFFFFFFFFFFFULL;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint64_t uu____0 = FStar_UInt64_eq_mask(a[i], b[i]);
    mask = uu____0 & mask;
  }
  uint64_t mask1 = mask;
  return mask1;
}

