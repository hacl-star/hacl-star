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


#ifndef __Hacl_Bignum32_H
#define __Hacl_Bignum32_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Krmllib.h"
#include "Hacl_Bignum_Base.h"
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

  This functions returns the carry.

  The arguments a, b and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len]
*/
uint32_t Hacl_Bignum32_add(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

/**
Write `a - b mod 2 ^ (32 * len)` in `res`.

  This functions returns the carry.

  The arguments a, b and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len]
*/
uint32_t Hacl_Bignum32_sub(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

/**
Write `(a + b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum32_add_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

/**
Write `(a - b) mod n` in `res`.

  The arguments a, b, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • a < n
  • b < n
*/
void Hacl_Bignum32_sub_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

/**
Write `a * b` in `res`.

  The arguments a and b are meant to be `len` limbs in size, i.e. uint32_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
*/
void Hacl_Bignum32_mul(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

/**
Write `a * a` in `res`.

  The argument a is meant to be `len` limbs in size, i.e. uint32_t[len].
  The outparam res is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
*/
void Hacl_Bignum32_sqr(uint32_t len, uint32_t *a, uint32_t *res);

/**
Write `a mod n` in `res`.

  The argument a is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
  The argument n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

  The function returns false if any of the following preconditions are violated,
  true otherwise.
   • 1 < n
   • n % 2 = 1 
*/
bool Hacl_Bignum32_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res);

/**
Write `a ^ b mod n` in `res`.

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

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

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

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

  The arguments a, n and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].

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
bool
Hacl_Bignum32_mod_inv_prime_vartime(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res);


/**********************************************/
/* Arithmetic functions with precomputations. */
/**********************************************/


/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint32_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_Bignum32_mont_ctx_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
*Hacl_Bignum32_mont_ctx_init(uint32_t len, uint32_t *n);

/**
Deallocate the memory previously allocated by Hacl_Bignum32_mont_ctx_init.

  The argument k is a montgomery context obtained through Hacl_Bignum32_mont_ctx_init.
*/
void Hacl_Bignum32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

/**
Write `a mod n` in `res`.

  The argument a is meant to be `2*len` limbs in size, i.e. uint32_t[2*len].
  The outparam res is meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum32_mont_ctx_init.
*/
void
Hacl_Bignum32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum32_mont_ctx_init.

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
Hacl_Bignum32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

/**
Write `a ^ b mod n` in `res`.

  The arguments a and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum32_mont_ctx_init.

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
Hacl_Bignum32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

/**
Write `a ^ (-1) mod n` in `res`.

  The argument a and the outparam res are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_Bignum32_mont_ctx_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < a
  • a < n
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

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

/**
Load a little-endian bignum from memory.

  The argument b points to `len` bytes of valid memory.
  The function returns a heap-allocated bignum of size sufficient to hold the
   result of loading b, or NULL if either the allocation failed, or the amount of
    required memory would exceed 4GB.

  If the return value is non-null, clients must eventually call free(3) on it to
  avoid memory leaks.
*/
uint32_t *Hacl_Bignum32_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

/**
Serialize a bignum into big-endian memory.

  The argument b points to a bignum of ⌈len / 4⌉ size.
  The outparam res points to `len` bytes of valid memory.
*/
void Hacl_Bignum32_bn_to_bytes_be(uint32_t len, uint32_t *b, uint8_t *res);

/**
Serialize a bignum into little-endian memory.

  The argument b points to a bignum of ⌈len / 4⌉ size.
  The outparam res points to `len` bytes of valid memory.
*/
void Hacl_Bignum32_bn_to_bytes_le(uint32_t len, uint32_t *b, uint8_t *res);


/***************/
/* Comparisons */
/***************/


/**
Returns 2^32 - 1 if a < b, otherwise returns 0.

 The arguments a and b are meant to be `len` limbs in size, i.e. uint32_t[len].
*/
uint32_t Hacl_Bignum32_lt_mask(uint32_t len, uint32_t *a, uint32_t *b);

/**
Returns 2^32 - 1 if a = b, otherwise returns 0.

 The arguments a and b are meant to be `len` limbs in size, i.e. uint32_t[len].
*/
uint32_t Hacl_Bignum32_eq_mask(uint32_t len, uint32_t *a, uint32_t *b);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum32_H_DEFINED
#endif
