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


#ifndef __Hacl_Bignum256_H
#define __Hacl_Bignum256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "lib_intrinsics.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Bignum.h"

/* SNIPPET_START: Hacl_Bignum256_add */

/*******************************************************************************

A verified 256-bit bignum library.

This is a 64-bit optimized version, where bignums are represented as an array
of four unsigned 64-bit integers, i.e. uint64_t[4]. Furthermore, the
limbs are stored in little-endian format, i.e. the least significant limb is at
index 0. Each limb is stored in native format in memory. Example:

  uint64_t sixteen[4] = { 0x10; 0x00; 0x00; 0x00 }

We strongly encourage users to go through the conversion functions, e.g.
bn_from_bytes_be, to i) not depend on internal representation choices and ii)
have the ability to switch easily to a 32-bit optimized version in the future.

*******************************************************************************/

/************************/
/* Arithmetic functions */
/************************/


/*
Write `a + b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]
*/
uint64_t Hacl_Bignum256_add(uint64_t *a, uint64_t *b, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_add */

/* SNIPPET_START: Hacl_Bignum256_sub */

/*
Write `a - b mod 2^256` in `res`.

  This functions returns the carry.

  The arguments a, b and res are meant to be 256-bit bignums, i.e. uint64_t[4]
*/
uint64_t Hacl_Bignum256_sub(uint64_t *a, uint64_t *b, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_sub */

/* SNIPPET_START: Hacl_Bignum256_mul */

/*
Write `a * b` in `res`.

  The arguments a and b are meant to be 256-bit bignums, i.e. uint64_t[4].
  The outparam res is meant to be a 512-bit bignum, i.e. uint64_t[8].
*/
void Hacl_Bignum256_mul(uint64_t *a, uint64_t *b, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_mul */

/* SNIPPET_START: Hacl_Bignum256_mod_precompr2 */

/*
Write `a mod n` in `res`

  The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
  The argument n, r2 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument r2 is a precomputed constant 2 ^ 512 mod n obtained through Hacl_Bignum256_new_precompr2.

  This function is *UNSAFE* and requires C clients to observe the precondition
  of bn_mod_slow_precompr2_lemma in Hacl.Spec.Bignum.ModReduction.fst, which
  amounts to:
  • 1 < n
  • n % 2 = 1
  • a < n * n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod below.
*/
void Hacl_Bignum256_mod_precompr2(uint64_t *n, uint64_t *a, uint64_t *r2, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_mod_precompr2 */

/* SNIPPET_START: Hacl_Bignum256_mod */

/*
Write `a mod n` in `res`

  The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
  The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  The function returns false if any of the preconditions of mod_precompr2 above
  are violated, true otherwise.
*/
bool Hacl_Bignum256_mod(uint64_t *n, uint64_t *a, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_mod */

/* SNIPPET_START: Hacl_Bignum256_mod_exp_precompr2 */

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument r2 is a precomputed constant 2 ^ 512 mod n obtained through Hacl_Bignum256_new_precompr2.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_mont_ladder_* functions for constant-time variants.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp below.
*/
void
Hacl_Bignum256_mod_exp_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
);

/* SNIPPET_END: Hacl_Bignum256_mod_exp_precompr2 */

/* SNIPPET_START: Hacl_Bignum256_mod_exp */

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 4096-bit bignum, bBits should be 4096.

  The function is *NOT* constant-time on the argument b. See the
  mod_exp_mont_ladder_* functions for constant-time variants.

  The function returns false if any of the preconditions of mod_exp_precompr2 are
  violated, true otherwise.
*/
bool
Hacl_Bignum256_mod_exp(uint64_t *n, uint64_t *a, uint32_t bBits, uint64_t *b, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_mod_exp */

/* SNIPPET_START: Hacl_Bignum256_mod_exp_mont_ladder_precompr2 */

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n, r2 and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument r2 is a precomputed constant 2 ^ 512 mod n.
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp_precompr2.

  This function is *UNSAFE* and requires C clients to observe bn_mod_exp_pre
  from Hacl.Spec.Bignum.Exponentiation.fsti, which amounts to:
  • n % 2 = 1
  • 1 < n
  • 0 < b
  • b < pow2 bBits
  • a < n

  Owing to the absence of run-time checks, and factoring out the precomputation
  r2, this function is notably faster than mod_exp_mont_ladder below.
*/
void
Hacl_Bignum256_mod_exp_mont_ladder_precompr2(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *r2,
  uint64_t *res
);

/* SNIPPET_END: Hacl_Bignum256_mod_exp_mont_ladder_precompr2 */

/* SNIPPET_START: Hacl_Bignum256_mod_exp_mont_ladder */

/*
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than mod_exp.

  The function returns false if any of the preconditions of
  mod_exp_mont_ladder_precompr2 are violated, true otherwise.
*/
bool
Hacl_Bignum256_mod_exp_mont_ladder(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

/* SNIPPET_END: Hacl_Bignum256_mod_exp_mont_ladder */

/* SNIPPET_START: Hacl_Bignum256_new_precompr2 */

/*
Compute `2 ^ (128 * nLen) mod n`.

  The argument n points to a bignum of size nLen of valid memory.
  The function returns a heap-allocated bignum of size nLen, or NULL if:
  • the allocation failed, or
  • the amount of required memory would exceed 4GB, or
  • n % 2 = 1 && 1 < n does not hold

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum256_new_precompr2(uint32_t len, uint64_t *n);

/* SNIPPET_END: Hacl_Bignum256_new_precompr2 */

/* SNIPPET_START: Hacl_Bignum256_mod_inv_prime */

/*
Write `a ^ (-1) mod n` in `res`.

  The arguments a, n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].

  This function is *UNSAFE* and requires C clients to observe the precondition of
  bn_mod_inv_prime_lemma from Hacl.Spec.Bignum.ModInv.fst, which amounts to:
  • n is a prime

  The function returns false if any of the following preconditions are violated, true otherwise.
  • n % 2 = 1
  • 1 < n
  • 0 < a
  • a < n 
*/
bool Hacl_Bignum256_mod_inv_prime(uint64_t *n, uint64_t *a, uint64_t *res);

/* SNIPPET_END: Hacl_Bignum256_mod_inv_prime */

/* SNIPPET_START: Hacl_Bignum256_new_bn_from_bytes_be */


/********************/
/* Loads and stores */
/********************/


/*
Load a bid-endian bignum from memory.

  The argument b points to len bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint64_t *Hacl_Bignum256_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

/* SNIPPET_END: Hacl_Bignum256_new_bn_from_bytes_be */

/* SNIPPET_START: Hacl_Bignum256_bn_to_bytes_be */

/*
Serialize a bignum into big-endian memory.

  The argument b points to a 256-bit bignum.
  The outparam res points to 32 bytes of valid memory.
*/
void Hacl_Bignum256_bn_to_bytes_be(uint64_t *b, uint8_t *res);

/* SNIPPET_END: Hacl_Bignum256_bn_to_bytes_be */

/* SNIPPET_START: Hacl_Bignum256_lt_mask */


/***************/
/* Comparisons */
/***************/


/*
Returns 2 ^ 64 - 1 if and only if argument a is strictly less than the argument b, otherwise returns 0.
*/
uint64_t Hacl_Bignum256_lt_mask(uint64_t *a, uint64_t *b);

/* SNIPPET_END: Hacl_Bignum256_lt_mask */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum256_H_DEFINED
#endif
