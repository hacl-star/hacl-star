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


#ifndef __Hacl_Ed25519_H
#define __Hacl_Ed25519_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Hash.h"
#include "Hacl_Curve25519_51.h"

/* SNIPPET_START: Hacl_Bignum25519_fdifference */

void Hacl_Bignum25519_fdifference(uint64_t *a, uint64_t *b);

/* SNIPPET_END: Hacl_Bignum25519_fdifference */

/* SNIPPET_START: Hacl_Bignum25519_reduce_513 */

void Hacl_Bignum25519_reduce_513(uint64_t *a);

/* SNIPPET_END: Hacl_Bignum25519_reduce_513 */

/* SNIPPET_START: Hacl_Bignum25519_inverse */

void Hacl_Bignum25519_inverse(uint64_t *out, uint64_t *a);

/* SNIPPET_END: Hacl_Bignum25519_inverse */

/* SNIPPET_START: Hacl_Bignum25519_load_51 */

void Hacl_Bignum25519_load_51(uint64_t *output, uint8_t *input);

/* SNIPPET_END: Hacl_Bignum25519_load_51 */

/* SNIPPET_START: Hacl_Bignum25519_store_51 */

void Hacl_Bignum25519_store_51(uint8_t *output, uint64_t *input);

/* SNIPPET_END: Hacl_Bignum25519_store_51 */

/* SNIPPET_START: Hacl_Impl_Ed25519_PointAdd_point_add */

void Hacl_Impl_Ed25519_PointAdd_point_add(uint64_t *out, uint64_t *p, uint64_t *q);

/* SNIPPET_END: Hacl_Impl_Ed25519_PointAdd_point_add */

/* SNIPPET_START: Hacl_Impl_Ed25519_Ladder_point_mul */

void Hacl_Impl_Ed25519_Ladder_point_mul(uint64_t *result, uint8_t *scalar, uint64_t *q);

/* SNIPPET_END: Hacl_Impl_Ed25519_Ladder_point_mul */

/* SNIPPET_START: Hacl_Impl_Ed25519_PointCompress_point_compress */

void Hacl_Impl_Ed25519_PointCompress_point_compress(uint8_t *z, uint64_t *p);

/* SNIPPET_END: Hacl_Impl_Ed25519_PointCompress_point_compress */

/* SNIPPET_START: Hacl_Impl_Ed25519_PointDecompress_point_decompress */

bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(uint64_t *out, uint8_t *s);

/* SNIPPET_END: Hacl_Impl_Ed25519_PointDecompress_point_decompress */

/* SNIPPET_START: Hacl_Impl_Ed25519_PointEqual_point_equal */

bool Hacl_Impl_Ed25519_PointEqual_point_equal(uint64_t *p, uint64_t *q);

/* SNIPPET_END: Hacl_Impl_Ed25519_PointEqual_point_equal */

/* SNIPPET_START: Hacl_Ed25519_sign */

void Hacl_Ed25519_sign(uint8_t *signature, uint8_t *priv, uint32_t len, uint8_t *msg);

/* SNIPPET_END: Hacl_Ed25519_sign */

/* SNIPPET_START: Hacl_Ed25519_verify */

bool Hacl_Ed25519_verify(uint8_t *pub, uint32_t len, uint8_t *msg, uint8_t *signature);

/* SNIPPET_END: Hacl_Ed25519_verify */

/* SNIPPET_START: Hacl_Ed25519_secret_to_public */

void Hacl_Ed25519_secret_to_public(uint8_t *pub, uint8_t *priv);

/* SNIPPET_END: Hacl_Ed25519_secret_to_public */

/* SNIPPET_START: Hacl_Ed25519_expand_keys */

void Hacl_Ed25519_expand_keys(uint8_t *ks, uint8_t *priv);

/* SNIPPET_END: Hacl_Ed25519_expand_keys */

/* SNIPPET_START: Hacl_Ed25519_sign_expanded */

void Hacl_Ed25519_sign_expanded(uint8_t *signature, uint8_t *ks, uint32_t len, uint8_t *msg);

/* SNIPPET_END: Hacl_Ed25519_sign_expanded */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Ed25519_H_DEFINED
#endif
