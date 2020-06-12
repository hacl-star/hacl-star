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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_P256_DH_H
#define __Hacl_P256_DH_H

#include "Hacl_Kremlib.h"
#include "Hacl_P256.h"
#include "Hacl_Hash.h"
#include "Hacl_Spec.h"


u64 Hacl_P256_DH_ecdsa_sign_p256_sha2(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

u64 Hacl_P256_DH_ecdsa_sign_p256_sha384(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

u64 Hacl_P256_DH_ecdsa_sign_p256_sha512(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

u64 Hacl_P256_DH_ecdsa_sign_p256_without_hash(u8 *result, u32 mLen, u8 *m, u8 *privKey, u8 *k);

bool Hacl_P256_DH_ecdsa_verif_p256_sha2(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_P256_DH_ecdsa_verif_p256_sha384(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_P256_DH_ecdsa_verif_p256_sha512(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_P256_DH_ecdsa_verif_without_hash(u32 mLen, u8 *m, u8 *pubKey, u8 *r, u8 *s);

bool Hacl_P256_DH_verify_q(u8 *pubKey);

bool Hacl_P256_DH_decompression_not_compressed_form(u8 *b, u8 *result);

bool Hacl_P256_DH_decompression_compressed_form(u8 *b, u8 *result);

void Hacl_P256_DH_compression_not_compressed_form(u8 *b, u8 *result);

void Hacl_P256_DH_compression_compressed_form(u8 *b, u8 *result);

void Hacl_P256_DH_reduction_8_32(u8 *x, u8 *result);

#define __Hacl_P256_DH_H_DEFINED
#endif
