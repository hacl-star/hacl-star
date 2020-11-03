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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Hash.h"
#include "Hacl_Curve25519_51.h"

void Hacl_Bignum25519_fdifference(u64 *a, u64 *b);

void Hacl_Bignum25519_reduce_513(u64 *a);

void Hacl_Bignum25519_inverse(u64 *out, u64 *a);

void Hacl_Bignum25519_load_51(u64 *output, u8 *input);

void Hacl_Bignum25519_store_51(u8 *output, u64 *input);

void Hacl_Impl_Ed25519_PointAdd_point_add(u64 *out, u64 *p, u64 *q);

void Hacl_Impl_Ed25519_Ladder_point_mul(u64 *result, u8 *scalar, u64 *q);

void Hacl_Impl_Ed25519_PointCompress_point_compress(u8 *z, u64 *p);

bool Hacl_Impl_Ed25519_PointDecompress_point_decompress(u64 *out, u8 *s);

bool Hacl_Impl_Ed25519_PointEqual_point_equal(u64 *p, u64 *q);

void Hacl_Ed25519_sign(u8 *signature, u8 *priv, u32 len, u8 *msg);

bool Hacl_Ed25519_verify(u8 *pub, u32 len, u8 *msg, u8 *signature);

void Hacl_Ed25519_secret_to_public(u8 *pub, u8 *priv);

void Hacl_Ed25519_expand_keys(u8 *ks, u8 *priv);

void Hacl_Ed25519_sign_expanded(u8 *signature, u8 *ks, u32 len, u8 *msg);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Ed25519_H_DEFINED
#endif
