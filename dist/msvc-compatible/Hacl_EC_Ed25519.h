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


#ifndef __Hacl_EC_Ed25519_H
#define __Hacl_EC_Ed25519_H

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
#include "Hacl_Bignum25519_51.h"

void Hacl_EC_Ed25519_mk_felem_zero(uint64_t *b);

void Hacl_EC_Ed25519_mk_felem_one(uint64_t *b);

void Hacl_EC_Ed25519_felem_add(uint64_t *a, uint64_t *b, uint64_t *out);

void Hacl_EC_Ed25519_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out);

void Hacl_EC_Ed25519_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out);

void Hacl_EC_Ed25519_felem_inv(uint64_t *a, uint64_t *out);

void Hacl_EC_Ed25519_felem_load(uint8_t *b, uint64_t *out);

void Hacl_EC_Ed25519_felem_store(uint64_t *a, uint8_t *out);

void Hacl_EC_Ed25519_mk_point_at_inf(uint64_t *p);

void Hacl_EC_Ed25519_mk_base_point(uint64_t *p);

void Hacl_EC_Ed25519_point_negate(uint64_t *p, uint64_t *out);

void Hacl_EC_Ed25519_point_add(uint64_t *p, uint64_t *q, uint64_t *out);

void Hacl_EC_Ed25519_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out);

bool Hacl_EC_Ed25519_point_eq(uint64_t *p, uint64_t *q);

void Hacl_EC_Ed25519_point_compress(uint64_t *p, uint8_t *out);

bool Hacl_EC_Ed25519_point_decompress(uint8_t *s, uint64_t *out);

#if defined(__cplusplus)
}
#endif

#define __Hacl_EC_Ed25519_H_DEFINED
#endif
