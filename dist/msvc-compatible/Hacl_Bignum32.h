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


#ifndef __Hacl_Bignum32_H
#define __Hacl_Bignum32_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Bignum.h"

typedef Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *Hacl_Bignum32_pbn_mont_ctx_u32;

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
uint32_t Hacl_Bignum32_add(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

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
uint32_t Hacl_Bignum32_sub(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

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
void Hacl_Bignum32_add_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

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
void Hacl_Bignum32_sub_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

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
void Hacl_Bignum32_mul(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

/**
Write `a * a` in `res`.

  @param[in] a Points to `len` number of limbs, i.e. `uint32_t[len]`. Must be
    disjoint from the memory location of `res`.
  @param[out] res Points to `2*len` number of limbs where the result is written, i.e. `uint32_t[2*len]`.
    Must be disjoint from the memory location of `a`.
*/
void Hacl_Bignum32_sqr(uint32_t len, uint32_t *a, uint32_t *res);

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
bool Hacl_Bignum32_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res);

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
);

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
);

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
bool
Hacl_Bignum32_mod_inv_prime_vartime(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res);


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
*Hacl_Bignum32_mont_ctx_init(uint32_t len, uint32_t *n);

/**
Deallocate the memory previously allocated by Hacl_Bignum32_mont_ctx_init.

  @param k Points to a Montgomery context obtained through `Hacl_Bignum32_mont_ctx_init`.
*/
void Hacl_Bignum32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

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
);

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
);

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
);

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
);


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
uint32_t *Hacl_Bignum32_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

/**
Load a little-endian bignum from memory.

  @param len Size of `b` as number of bytes.
  @param b Points to `len` number of bytes, i.e. `uint8_t[len]`.
  
  @return A heap-allocated bignum of size sufficient to hold the result of
    loading `b`. Otherwise, `NULL`, if either the allocation failed, or the amount
    of required memory would exceed 4GB. Clients must `free(3)` any non-null return
    value to avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

/**
Serialize a bignum into big-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`.
*/
void Hacl_Bignum32_bn_to_bytes_be(uint32_t len, uint32_t *b, uint8_t *res);

/**
Serialize a bignum into little-endian memory.

  @param[in] len Size of `b` as number of bytes.
  @param[in] b Points to a bignum of `ceil(len/4)` size. Must be disjoint from
    the memory location of `res`.
  @param[out] res Points to `len` number of bytes, i.e. `uint8_t[len]`. Must be
    disjoint from the memory location of `b`.
*/
void Hacl_Bignum32_bn_to_bytes_le(uint32_t len, uint32_t *b, uint8_t *res);


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
uint32_t Hacl_Bignum32_lt_mask(uint32_t len, uint32_t *a, uint32_t *b);

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

  @param len Number of limbs.
  @param a Points to `len` number of limbs, i.e. `uint32_t[len]`.
  @param b Points to `len` number of limbs, i.e. `uint32_t[len]`.
  
  @return `2^32 - 1` if a = b, otherwise, `0`.
*/
uint32_t Hacl_Bignum32_eq_mask(uint32_t len, uint32_t *a, uint32_t *b);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum32_H_DEFINED
#endif
