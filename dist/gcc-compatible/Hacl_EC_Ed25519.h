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


#ifndef __Hacl_EC_Ed25519_H
#define __Hacl_EC_Ed25519_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Krmllib.h"

/*******************************************************************************
  Verified field arithmetic modulo p = 2^255 - 19.

  This is a 64-bit optimized version, where a field element in radix-2^{51} is
  represented as an array of five unsigned 64-bit integers, i.e., uint64_t[5].
*******************************************************************************/


/**
Write the additive identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_Ed25519_mk_felem_zero(uint64_t *b);

/**
Write the multiplicative identity in `f`.

  The outparam `f` is meant to be 5 limbs in size, i.e., uint64_t[5].
*/
void Hacl_EC_Ed25519_mk_felem_one(uint64_t *b);

/**
Write `a + b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_felem_add(uint64_t *a, uint64_t *b, uint64_t *out);

/**
Write `a - b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out);

/**
Write `a * b mod p` in `out`.

  The arguments `a`, `b`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a`, `b`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out);

/**
Write `a * a mod p` in `out`.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are either disjoint or equal
*/
void Hacl_EC_Ed25519_felem_sqr(uint64_t *a, uint64_t *out);

/**
Write `a ^ (p - 2) mod p` in `out`.

  The function computes modular multiplicative inverse if `a` <> zero.

  The argument `a`, and the outparam `out` are meant to be 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_Ed25519_felem_inv(uint64_t *a, uint64_t *out);

/**
Load a little-endian field element from memory.

  The argument `b` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a field element of 5 limbs in size, i.e., uint64_t[5].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `b` and `out` are disjoint

  NOTE that the function also performs the reduction modulo 2^255.
*/
void Hacl_EC_Ed25519_felem_load(uint8_t *b, uint64_t *out);

/**
Serialize a field element into little-endian memory.

  The argument `a` points to a field element of 5 limbs in size, i.e., uint64_t[5].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `a` and `out` are disjoint
*/
void Hacl_EC_Ed25519_felem_store(uint64_t *a, uint8_t *out);

/*******************************************************************************
  Verified group operations for the edwards25519 elliptic curve of the form
  −x^2 + y^2 = 1 − (121665/121666) * x^2 * y^2.

  This is a 64-bit optimized version, where a group element in extended homogeneous
  coordinates (X, Y, Z, T) is represented as an array of 20 unsigned 64-bit
  integers, i.e., uint64_t[20].
*******************************************************************************/


/**
Write the point at infinity (additive identity) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20].
*/
void Hacl_EC_Ed25519_mk_point_at_inf(uint64_t *p);

/**
Write the base point (generator) in `p`.

  The outparam `p` is meant to be 20 limbs in size, i.e., uint64_t[20].
*/
void Hacl_EC_Ed25519_mk_base_point(uint64_t *p);

/**
Write `-p` in `out` (point negation).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint
*/
void Hacl_EC_Ed25519_point_negate(uint64_t *p, uint64_t *out);

/**
Write `p + q` in `out` (point addition).

  The arguments `p`, `q` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p`, `q`, and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_point_add(uint64_t *p, uint64_t *q, uint64_t *out);

/**
Write `p + p` in `out` (point doubling).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are either pairwise disjoint or equal
*/
void Hacl_EC_Ed25519_point_double(uint64_t *p, uint64_t *out);

/**
Write `[scalar]p` in `out` (point multiplication or scalar multiplication).

  The argument `p` and the outparam `out` are meant to be 20 limbs in size, i.e., uint64_t[20].
  The argument `scalar` is meant to be 32 bytes in size, i.e., uint8_t[32].

  The function first loads a little-endian scalar element from `scalar` and
  then computes a point multiplication.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `scalar`, `p`, and `out` are pairwise disjoint
*/
void Hacl_EC_Ed25519_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out);

/**
Checks whether `p` is equal to `q` (point equality).

  The function returns `true` if `p` is equal to `q` and `false` otherwise.

  The arguments `p` and `q` are meant to be 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `q` are either disjoint or equal
*/
bool Hacl_EC_Ed25519_point_eq(uint64_t *p, uint64_t *q);

/**
Compress a point in extended homogeneous coordinates to its compressed form.

  The argument `p` points to a point of 20 limbs in size, i.e., uint64_t[20].
  The outparam `out` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first converts a given point `p` from extended homogeneous to affine coordinates
  and then writes [ 2^255 * (`x` % 2) + `y` ] in `out`.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `p` and `out` are disjoint
*/
void Hacl_EC_Ed25519_point_compress(uint64_t *p, uint8_t *out);

/**
Decompress a point in extended homogeneous coordinates from its compressed form.

  The function returns `true` for successful decompression of a compressed point
  and `false` otherwise.

  The argument `s` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The outparam `out` points to a point of 20 limbs in size, i.e., uint64_t[20].

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • `s` and `out` are disjoint
*/
bool Hacl_EC_Ed25519_point_decompress(uint8_t *s, uint64_t *out);

#if defined(__cplusplus)
}
#endif

#define __Hacl_EC_Ed25519_H_DEFINED
#endif
