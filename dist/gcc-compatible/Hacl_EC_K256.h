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


#ifndef __Hacl_EC_K256_H
#define __Hacl_EC_K256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

/*******************************************************************************
  Verified field arithmetic modulo p = 2^256 - 0x1000003D1.

  This is a 64-bit optimized version, where a field element in radix-2^{52} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/


/**
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_K256_mk_felem_zero(uint64_t *f);

/**
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_K256_mk_felem_one(uint64_t *f);

/**
Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_add(uint64_t *a, uint64_t *b, uint64_t *out);

/**
Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out);

/**
Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out);

/**
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_felem_sqr(uint64_t *a, uint64_t *out);

/**
Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_K256_felem_inv(uint64_t *a, uint64_t *out);

/**
Load a bid-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint
*/
void Hacl_EC_K256_felem_load(uint8_t *b, uint64_t *out);

/**
Serialize a field element into big-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_K256_felem_store(uint64_t *a, uint8_t *out);

/*******************************************************************************
  Verified group operations for the secp256k1 curve of the form y^2 = x^3 + 7.

  This is a 64-bit optimized version, where a group element in projective coordinates
  is represented as an array of 15 unsigned 64-bit integers, i.e., uint64_t[15].
*******************************************************************************/


/**
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
void Hacl_EC_K256_mk_point_at_inf(uint64_t *p);

/**
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 15 limbs in size, i.e., uint64_t[15].
*/
void Hacl_EC_K256_mk_base_point(uint64_t *p);

/**
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_point_negate(uint64_t *p, uint64_t *out);

/**
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_K256_point_add(uint64_t *p, uint64_t *q, uint64_t *out);

/**
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either disjoint or equal
*/
void Hacl_EC_K256_point_double(uint64_t *p, uint64_t *out);

/**
Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 15 limbs in size, i.e., uint64_t[15].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a bid-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint
*/
void Hacl_EC_K256_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out);

/**
Convert a point from projective coordinates to its raw form.

  The argument `p` points to a point of 15 limbs in size, i.e., uint64_t[15].
  The outparam `out` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first converts a given point `p` from projective to affine coordinates
  and then writes [ `x`; `y` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint.
*/
void Hacl_EC_K256_point_store(uint64_t *p, uint8_t *out);

/**
Convert a point to projective coordinates from its raw form.

  The argument `b` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The outparam `out` points to a point of 15 limbs in size, i.e., uint64_t[15].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` is valid point, i.e., x < prime and y < prime and (x, y) is on the curve
  • `b` and `out` are disjoint.
*/
void Hacl_EC_K256_point_load(uint8_t *b, uint64_t *out);

/**
Check whether a point is valid.

  The function returns `true` if a point is valid and `false` otherwise.

  The argument `b` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The point (x || y) is valid:
    • x < prime and y < prime
    • (x, y) is on the curve.

  This function is NOT constant-time.
*/
bool Hacl_EC_K256_is_point_valid(uint8_t *b);

#if defined(__cplusplus)
}
#endif

#define __Hacl_EC_K256_H_DEFINED
#endif
