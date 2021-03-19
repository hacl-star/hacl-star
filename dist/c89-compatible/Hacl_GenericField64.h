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


#ifndef __Hacl_GenericField64_H
#define __Hacl_GenericField64_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Bignum.h"

typedef struct Hacl_Bignum_GenericField_bn_mont_ctx_u64_s
{
  uint32_t nBits;
  uint32_t len;
  uint64_t *n;
  uint64_t mu;
  uint64_t *r2;
}
Hacl_Bignum_GenericField_bn_mont_ctx_u64;

/*******************************************************************************

A verified field arithmetic library.

This is a 64-bit optimized version, where bignums are represented as an array
of `len` unsigned 64-bit integers, i.e. uint64_t[len].
All the arithmetic operations are performed in the Montgomery domain.

*******************************************************************************/


/*
Allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument nBits is an exact number of significant bits of n.

  This function is *UNSAFE* and requires C clients to observe bn_mont_ctx_pre
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:

  • 0 < nBits /\ (nBits - 1) / bits t < len
  • pow2 (nBits - 1) < n /\ n < pow2 nBits

  • n % 2 = 1
  • 1 < n

  • n is a prime // needed for the modular multiplicative inverse

*/
Hacl_Bignum_GenericField_bn_mont_ctx_u64
Hacl_GenericField64_field_init(uint32_t len, uint32_t nBits, uint64_t *n);

/*
Return a size of the modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
uint32_t Hacl_GenericField64_field_get_len(Hacl_Bignum_GenericField_bn_mont_ctx_u64 k);

/*
Convert a bignum to its Montgomery representation.

  Write `a * R mod n` in `aM`.

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_to_field
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • a < n

*/
void
Hacl_GenericField64_to_field(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *a,
  uint64_t *aM
);

/*
Convert the result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField64_from_field(k, Hacl_GenericField64_to_field(k, a)) == a

  The arguments a and aM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_from_field
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n

*/
void
Hacl_GenericField64_from_field(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *a
);

/*
Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_add
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n 
*/
void
Hacl_GenericField64_add(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
);

/*
Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_sub
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n 
*/
void
Hacl_GenericField64_sub(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
);

/*
Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_mul
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • bM < n 
*/
void
Hacl_GenericField64_mul(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
);

/*
Write `aM * aM mod n` in `cM`.

  The arguments aM and cM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_sqr
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n 
*/
void
Hacl_GenericField64_sqr(Hacl_Bignum_GenericField_bn_mont_ctx_u64 k, uint64_t *aM, uint64_t *cM);

/*
Convert a bignum `one` to its Montgomery representation.

  The argument oneM is meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.
*/
void Hacl_GenericField64_one(Hacl_Bignum_GenericField_bn_mont_ctx_u64 k, uint64_t *oneM);

/*
Write `aM ^ (-1) mod n` in `aInvM`.

  The arguments aM and aInvM are meant to be `len` limbs in size, i.e. uint64_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField64_field_init.

  This function is *UNSAFE* and requires C clients to observe bn_field_inv
  from Hacl.Spec.Bignum.GenericField.fsti, which amounts to:
  • aM < n
  • 0 < aM 
*/
void
Hacl_GenericField64_inverse(
  Hacl_Bignum_GenericField_bn_mont_ctx_u64 k,
  uint64_t *aM,
  uint64_t *aInvM
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_GenericField64_H_DEFINED
#endif
