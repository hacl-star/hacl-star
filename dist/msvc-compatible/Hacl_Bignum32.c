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


#include "Hacl_Bignum32.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
#include "internal/Hacl_Bignum.h"

/*******************************************************************************

A verified bignum library.

This is a 32-bit optimized version, where bignums are represented as an array
of `len` unsigned 32-bit integers, i.e. uint32_t[len].

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/**
Write `a + b mod 2 ^ (32 * len)` in `res`.

  This function returns the carry.
  
  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly equal memory
    location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[out] res Points to `len` number of limbs where the carry is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`.
*/
uint32_t Hacl_Bignum32_add(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res)
{
  return Hacl_Bignum_Addition_bn_add_eq_len_u32(len, a, b, res);
}

/**
Write `a - b mod 2 ^ (32 * len)` in `res`.

  This functions returns the carry.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly
    equal memory location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[out] res Points to `len` number of limbs where the carry is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`.
*/
uint32_t Hacl_Bignum32_sub(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res)
{
  return Hacl_Bignum_Addition_bn_sub_eq_len_u32(len, a, b, res);
}

/**
Write `(a + b) mod n` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly
    equal memory location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `res`.
  @param[out] res Points to `len` number of limbs where the result is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `a < n`
    - `b < n`
*/
void Hacl_Bignum32_add_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res)
{
  Hacl_Bignum_bn_add_mod_n_u32(len, n, a, b, res);
}

/**
Write `(a - b) mod n` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `b` or `res`. May have exactly
    equal memory location to `b` or `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must not
    partially overlap the memory locations of `a` or `res`. May have exactly
    equal memory location to `a` or `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `res`.
  @param[out] res Points to `len` number of limbs where the result is written, i.e. `uint32_t[len]`.
    Must not partially overlap the memory locations of `a` or `b`. May have
    exactly equal memory location to `a` or `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `a < n`
    - `b < n`
*/
void Hacl_Bignum32_sub_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res)
{
  Hacl_Bignum_bn_sub_mod_n_u32(len, n, a, b, res);
}

/**
Write `a * b` in `res`.

  @param[in] len Number of limbs.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `b` and `res`.
  @param[in] b Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a` and `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory locations of `a` and `b`.
*/
void Hacl_Bignum32_mul(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t *tmp = (uint32_t *)alloca(4U * len * sizeof (uint32_t));
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len, a, b, tmp, res);
}

/**
Write `a * a` in `res`.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory location of `a`.
*/
void Hacl_Bignum32_sqr(uint32_t len, uint32_t *a, uint32_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), 4U * len);
  uint32_t *tmp = (uint32_t *)alloca(4U * len * sizeof (uint32_t));
  memset(tmp, 0U, 4U * len * sizeof (uint32_t));
  Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len, a, tmp, res);
}

static inline void
bn_slow_precomp(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t *res
)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *a_mod = (uint32_t *)alloca(len * sizeof (uint32_t));
  memset(a_mod, 0U, len * sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), len + len);
  uint32_t *a1 = (uint32_t *)alloca((len + len) * sizeof (uint32_t));
  memset(a1, 0U, (len + len) * sizeof (uint32_t));
  memcpy(a1, a, (len + len) * sizeof (uint32_t));
  Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(len, n, mu, a1, a_mod);
  Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a_mod, res);
}

/**
Write `a mod n` in `res`.

  @param[in] a Points to `2*len` number of limbs, i.e. `uint32_t[2*len]`. Must be
    disjoint from the memory location of `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `n`.
  
  @return `false` if any precondition is violated, `true` otherwise.
  
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `1 < n`
    - `n % 2 = 1`
*/
bool Hacl_Bignum32_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *one = (uint32_t *)alloca(len * sizeof (uint32_t));
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
    acc = (beq & acc) | (~beq & blt);
  }
  uint32_t m1 = acc;
  uint32_t is_valid_m = m0 & m1;
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *r2 = (uint32_t *)alloca(len * sizeof (uint32_t));
    memset(r2, 0U, len * sizeof (uint32_t));
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2);
    uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
    bn_slow_precomp(len, n, mu, r2, a, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
}

/**
Write `a ^ b mod n` in `res`.

  This function is *NOT* constant-time on the argument `b`. See the
  `mod_exp_consttime_*` functions for constant-time variants.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `n` and `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `n`.
    
  @return `false` if any preconditions are violated, `true` otherwise.
  
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`
    - `b < pow2 bBits`
    - `a < n`
*/
bool
Hacl_Bignum32_mod_exp_vartime(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(len, n, a, bBits, b);
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32(len, nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
}

/**
Write `a ^ b mod n` in `res`.

  This function is constant-time over its argument `b`, at the cost of a slower
  execution time than `mod_exp_vartime_*`.
  
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `n` and `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a`, `b`, and `n`.
    
  @return `false` if any preconditions are violated, `true` otherwise.

  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`
    - `b < pow2 bBits`
    - `a < n`
*/
bool
Hacl_Bignum32_mod_exp_consttime(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  uint32_t is_valid_m = Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(len, n, a, bBits, b);
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32(len, nBits, n, a, bBits, b, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
}

/**
Write `a ^ (-1) mod n` in `res`.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `n` and `res`.
  @param[in] n Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a` and `n`.
    
  @return `false` if any preconditions (except the precondition: `n` is a prime)
    are violated, `true` otherwise.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n` is a prime
    - `n % 2 = 1`
    - `1 < n`
    - `0 < a`
    - `a < n`
*/
bool Hacl_Bignum32_mod_inv_prime_vartime(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *one = (uint32_t *)alloca(len * sizeof (uint32_t));
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
    acc0 = (beq & acc0) | (~beq & blt);
  }
  uint32_t m1 = acc0;
  uint32_t m00 = m0 & m1;
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *bn_zero = (uint32_t *)alloca(len * sizeof (uint32_t));
  memset(bn_zero, 0U, len * sizeof (uint32_t));
  uint32_t mask = 0xFFFFFFFFU;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], bn_zero[i]);
    mask = uu____0 & mask;
  }
  uint32_t mask1 = mask;
  uint32_t res10 = mask1;
  uint32_t m10 = res10;
  uint32_t acc = 0U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[i], n[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], n[i]);
    acc = (beq & acc) | (~beq & blt);
  }
  uint32_t m2 = acc;
  uint32_t is_valid_m = (m00 & ~m10) & m2;
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  if (is_valid_m == 0xFFFFFFFFU)
  {
    KRML_CHECK_SIZE(sizeof (uint32_t), len);
    uint32_t *n2 = (uint32_t *)alloca(len * sizeof (uint32_t));
    memset(n2, 0U, len * sizeof (uint32_t));
    uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(0U, n[0U], 2U, n2);
    uint32_t c1;
    if (1U < len)
    {
      uint32_t *a1 = n + 1U;
      uint32_t *res1 = n2 + 1U;
      uint32_t c = c0;
      for (uint32_t i = 0U; i < (len - 1U) / 4U; i++)
      {
        uint32_t t1 = a1[4U * i];
        uint32_t *res_i0 = res1 + 4U * i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i0);
        uint32_t t10 = a1[4U * i + 1U];
        uint32_t *res_i1 = res1 + 4U * i + 1U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, 0U, res_i1);
        uint32_t t11 = a1[4U * i + 2U];
        uint32_t *res_i2 = res1 + 4U * i + 2U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, 0U, res_i2);
        uint32_t t12 = a1[4U * i + 3U];
        uint32_t *res_i = res1 + 4U * i + 3U;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, 0U, res_i);
      }
      for (uint32_t i = (len - 1U) / 4U * 4U; i < len - 1U; i++)
      {
        uint32_t t1 = a1[i];
        uint32_t *res_i = res1 + i;
        c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i);
      }
      uint32_t c10 = c;
      c1 = c10;
    }
    else
    {
      c1 = c0;
    }
    KRML_MAYBE_UNUSED_VAR(c1);
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32(len, nBits, n, a, 32U * len, n2, res);
  }
  else
  {
    memset(res, 0U, len * sizeof (uint32_t));
  }
  return is_valid_m == 0xFFFFFFFFU;
}


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/**
Heap-allocate and initialize a montgomery context.

  @param n Points to `len` number of limbs, i.e. `uint32_t[len]`.

  @return A pointer to an allocated and initialized Montgomery context is returned.
    Clients will need to call `Hacl_Bignum32_mont_ctx_free` on the return value to
    avoid memory leaks.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n % 2 = 1`
    - `1 < n`
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
*Hacl_Bignum32_mont_ctx_init(uint32_t len, uint32_t *n)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *r2 = (uint32_t *)KRML_HOST_CALLOC(len, sizeof (uint32_t));
  KRML_CHECK_SIZE(sizeof (uint32_t), len);
  uint32_t *n1 = (uint32_t *)KRML_HOST_CALLOC(len, sizeof (uint32_t));
  uint32_t *r21 = r2;
  uint32_t *n11 = n1;
  memcpy(n11, n, len * sizeof (uint32_t));
  uint32_t nBits = 32U * Hacl_Bignum_Lib_bn_get_top_index_u32(len, n);
  Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r21);
  uint32_t mu = Hacl_Bignum_ModInvLimb_mod_inv_uint32(n[0U]);
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 res = { .len = len, .n = n11, .mu = mu, .r2 = r21 };
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
  *buf =
    (Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *)KRML_HOST_MALLOC(sizeof (
        Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
      ));
  buf[0U] = res;
  return buf;
}

/**
Deallocate the memory previously allocated by Hacl_Bignum32_mont_ctx_init.

  @param k Points to a Montgomery context obtained through `Hacl_Bignum32_mont_ctx_init`.
*/
void Hacl_Bignum32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  uint32_t *n = k1.n;
  uint32_t *r2 = k1.r2;
  KRML_HOST_FREE(n);
  KRML_HOST_FREE(r2);
  KRML_HOST_FREE(k);
}

/**
Write `a mod n` in `res`.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `2*len` number of limbs, i.e. `uint32_t[2*len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a`.
*/
void
Hacl_Bignum32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  bn_slow_precomp(len1, k1.n, k1.mu, k1.r2, a, res);
}

/**
Write `a ^ b mod n` in `res`.

  This function is *NOT* constant-time on the argument `b`. See the
  `mod_exp_consttime_*` functions for constant-time variants.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `b < pow2 bBits`
    - `a < n`
*/
void
Hacl_Bignum32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(len1,
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

  This function is constant-time over its argument b, at the cost of a slower
  execution time than `mod_exp_vartime_*`.

  @param[in] k Points to a Montgomery context obtained from `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[in] b Points to a bignum of any size, with an upper bound of `bBits` number of
    significant bits. Must be disjoint from the memory location of `res`.
  @param[in] bBits An upper bound on the number of significant bits of `b`.
    A tighter bound results in faster execution time. When in doubt, the number
    of bits for the bignum size is always a safe default, e.g. if `b` is a 4096-bit
    bignum, `bBits` should be `4096`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory locations of `a` and `b`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `b < pow2 bBits`
    - `a < n`
*/
void
Hacl_Bignum32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(len1,
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

  @param[in] k Points to a Montgomery context obtained through `Hacl_Bignum32_mont_ctx_init`.
  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `a`.
    
  @pre Before calling this function, the caller will need to ensure that the following
    preconditions are observed:
    - `n` is a prime
    - `0 < a`
    - `a < n`
*/
void
Hacl_Bignum32_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
)
{
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k10 = *k;
  uint32_t len1 = k10.len;
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 k1 = *k;
  KRML_CHECK_SIZE(sizeof (uint32_t), len1);
  uint32_t *n2 = (uint32_t *)alloca(len1 * sizeof (uint32_t));
  memset(n2, 0U, len1 * sizeof (uint32_t));
  uint32_t c0 = Lib_IntTypes_Intrinsics_sub_borrow_u32(0U, k1.n[0U], 2U, n2);
  uint32_t c1;
  if (1U < len1)
  {
    uint32_t *a1 = k1.n + 1U;
    uint32_t *res1 = n2 + 1U;
    uint32_t c = c0;
    for (uint32_t i = 0U; i < (len1 - 1U) / 4U; i++)
    {
      uint32_t t1 = a1[4U * i];
      uint32_t *res_i0 = res1 + 4U * i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i0);
      uint32_t t10 = a1[4U * i + 1U];
      uint32_t *res_i1 = res1 + 4U * i + 1U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t10, 0U, res_i1);
      uint32_t t11 = a1[4U * i + 2U];
      uint32_t *res_i2 = res1 + 4U * i + 2U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t11, 0U, res_i2);
      uint32_t t12 = a1[4U * i + 3U];
      uint32_t *res_i = res1 + 4U * i + 3U;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t12, 0U, res_i);
    }
    for (uint32_t i = (len1 - 1U) / 4U * 4U; i < len1 - 1U; i++)
    {
      uint32_t t1 = a1[i];
      uint32_t *res_i = res1 + i;
      c = Lib_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0U, res_i);
    }
    uint32_t c10 = c;
    c1 = c10;
  }
  else
  {
    c1 = c0;
  }
  KRML_MAYBE_UNUSED_VAR(c1);
  Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(len1,
    k1.n,
    k1.mu,
    k1.r2,
    a,
    32U * len1,
    n2,
    res);
}


/********************/
/* Loads and stores */
/********************/


/**
Load a bid-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_be(uint32_t len, uint8_t *b)
{
  if (len == 0U || !((len - 1U) / 4U + 1U <= 1073741823U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - 1U) / 4U + 1U);
  uint32_t *res = (uint32_t *)KRML_HOST_CALLOC((len - 1U) / 4U + 1U, sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 4U + 1U;
  uint32_t tmpLen = 4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp + tmpLen - len, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    uint32_t *os = res2;
    uint32_t u = load32_be(tmp + (bnLen - i - 1U) * 4U);
    uint32_t x = u;
    os[i] = x;
  }
  return res2;
}

/**
Load a little-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_le(uint32_t len, uint8_t *b)
{
  if (len == 0U || !((len - 1U) / 4U + 1U <= 1073741823U))
  {
    return NULL;
  }
  KRML_CHECK_SIZE(sizeof (uint32_t), (len - 1U) / 4U + 1U);
  uint32_t *res = (uint32_t *)KRML_HOST_CALLOC((len - 1U) / 4U + 1U, sizeof (uint32_t));
  if (res == NULL)
  {
    return res;
  }
  uint32_t *res1 = res;
  uint32_t *res2 = res1;
  uint32_t bnLen = (len - 1U) / 4U + 1U;
  uint32_t tmpLen = 4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  memcpy(tmp, b, len * sizeof (uint8_t));
  for (uint32_t i = 0U; i < (len - 1U) / 4U + 1U; i++)
  {
    uint32_t *os = res2;
    uint8_t *bj = tmp + i * 4U;
    uint32_t u = load32_le(bj);
    uint32_t r1 = u;
    uint32_t x = r1;
    os[i] = x;
  }
  return res2;
}

/**
Serialize a bignum into big-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`.
*/
void Hacl_Bignum32_bn_to_bytes_be(uint32_t len, uint32_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - 1U) / 4U + 1U;
  uint32_t tmpLen = 4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    store32_be(tmp + i * 4U, b[bnLen - i - 1U]);
  }
  memcpy(res, tmp + tmpLen - len, len * sizeof (uint8_t));
}

/**
Serialize a bignum into little-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`.
*/
void Hacl_Bignum32_bn_to_bytes_le(uint32_t len, uint32_t *b, uint8_t *res)
{
  uint32_t bnLen = (len - 1U) / 4U + 1U;
  uint32_t tmpLen = 4U * bnLen;
  KRML_CHECK_SIZE(sizeof (uint8_t), tmpLen);
  uint8_t *tmp = (uint8_t *)alloca(tmpLen * sizeof (uint8_t));
  memset(tmp, 0U, tmpLen * sizeof (uint8_t));
  for (uint32_t i = 0U; i < bnLen; i++)
  {
    store32_le(tmp + i * 4U, b[i]);
  }
  memcpy(res, tmp, len * sizeof (uint8_t));
}


/***************/
/* Comparisons */
/***************/


/**
Returns 2^32 - 1 if a < b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if `a < b`, otherwise, `0`.
*/
uint32_t Hacl_Bignum32_lt_mask(uint32_t len, uint32_t *a, uint32_t *b)
{
  uint32_t acc = 0U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t beq = FStar_UInt32_eq_mask(a[i], b[i]);
    uint32_t blt = ~FStar_UInt32_gte_mask(a[i], b[i]);
    acc = (beq & acc) | (~beq & blt);
  }
  return acc;
}

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if a = b, otherwise, `0`.
*/
uint32_t Hacl_Bignum32_eq_mask(uint32_t len, uint32_t *a, uint32_t *b)
{
  uint32_t mask = 0xFFFFFFFFU;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint32_t uu____0 = FStar_UInt32_eq_mask(a[i], b[i]);
    mask = uu____0 & mask;
  }
  uint32_t mask1 = mask;
  return mask1;
}

