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


#ifndef __Hacl_GenericField32_H
#define __Hacl_GenericField32_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Bignum_Base.h"
#include "Hacl_Bignum.h"

/* SNIPPET_START: Hacl_GenericField32_pbn_mont_ctx_u32 */

typedef Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *Hacl_GenericField32_pbn_mont_ctx_u32;

/* SNIPPET_END: Hacl_GenericField32_pbn_mont_ctx_u32 */

/* SNIPPET_START: Hacl_GenericField32_field_modulus_check */

/*******************************************************************************

A verified field arithmetic library.

This is a 32-bit optimized version, where bignums are represented as an array
of `len` unsigned 32-bit integers, i.e. uint32_t[len].

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
bool Hacl_GenericField32_field_modulus_check(uint32_t len, uint32_t *n);

/* SNIPPET_END: Hacl_GenericField32_field_modulus_check */

/* SNIPPET_START: Hacl_GenericField32_field_init */

/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint32_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_GenericField32_field_free on the return value
  to avoid memory leaks.
*/
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
*Hacl_GenericField32_field_init(uint32_t len, uint32_t *n);

/* SNIPPET_END: Hacl_GenericField32_field_init */

/* SNIPPET_START: Hacl_GenericField32_field_free */

/**
Deallocate the memory previously allocated by Hacl_GenericField32_field_init.

  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void Hacl_GenericField32_field_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

/* SNIPPET_END: Hacl_GenericField32_field_free */

/* SNIPPET_START: Hacl_GenericField32_field_get_len */

/**
Return the size of a modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
uint32_t Hacl_GenericField32_field_get_len(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

/* SNIPPET_END: Hacl_GenericField32_field_get_len */

/* SNIPPET_START: Hacl_GenericField32_to_field */

/**
Convert a bignum from the regular representation to the Montgomery representation.

  Write `a * R mod n` in `aM`.

  The argument a and the outparam aM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void
Hacl_GenericField32_to_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *aM
);

/* SNIPPET_END: Hacl_GenericField32_to_field */

/* SNIPPET_START: Hacl_GenericField32_from_field */

/**
Convert a result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField32_from_field(k, Hacl_GenericField32_to_field(k, a)) == a % n

  The argument aM and the outparam a are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void
Hacl_GenericField32_from_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *a
);

/* SNIPPET_END: Hacl_GenericField32_from_field */

/* SNIPPET_START: Hacl_GenericField32_add */

/**
Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void
Hacl_GenericField32_add(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *cM
);

/* SNIPPET_END: Hacl_GenericField32_add */

/* SNIPPET_START: Hacl_GenericField32_sub */

/**
Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void
Hacl_GenericField32_sub(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *cM
);

/* SNIPPET_END: Hacl_GenericField32_sub */

/* SNIPPET_START: Hacl_GenericField32_mul */

/**
Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void
Hacl_GenericField32_mul(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *cM
);

/* SNIPPET_END: Hacl_GenericField32_mul */

/* SNIPPET_START: Hacl_GenericField32_sqr */

/**
Write `aM * aM mod n` in `cM`.

  The argument aM and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void
Hacl_GenericField32_sqr(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *cM
);

/* SNIPPET_END: Hacl_GenericField32_sqr */

/* SNIPPET_START: Hacl_GenericField32_one */

/**
Convert a bignum `one` to its Montgomery representation.

  The outparam oneM is meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
void Hacl_GenericField32_one(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k, uint32_t *oneM);

/* SNIPPET_END: Hacl_GenericField32_one */

/* SNIPPET_START: Hacl_GenericField32_exp_consttime */

/**
Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.

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
Hacl_GenericField32_exp_consttime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *resM
);

/* SNIPPET_END: Hacl_GenericField32_exp_consttime */

/* SNIPPET_START: Hacl_GenericField32_exp_vartime */

/**
Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.

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
Hacl_GenericField32_exp_vartime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *resM
);

/* SNIPPET_END: Hacl_GenericField32_exp_vartime */

/* SNIPPET_START: Hacl_GenericField32_inverse */

/**
Write `aM ^ (-1) mod n` in `aInvM`.

  The argument aM and the outparam aInvM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < aM
*/
void
Hacl_GenericField32_inverse(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *aInvM
);

/* SNIPPET_END: Hacl_GenericField32_inverse */

#if defined(__cplusplus)
}
#endif

#define __Hacl_GenericField32_H_DEFINED
#endif
