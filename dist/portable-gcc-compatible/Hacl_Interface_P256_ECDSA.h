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

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_Interface_P256_ECDSA_H
#define __Hacl_Interface_P256_ECDSA_H

#include "Hacl_Kremlib.h"
#include "Hacl_P256.h"
#include "Hacl_Hash.h"
#include "Hacl_Spec.h"


/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha2 */

uint64_t
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha2(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha2 */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha384 */

uint64_t
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha384(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha384 */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha512 */

uint64_t
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha512(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_sha512 */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_without_hash */

uint64_t
Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_without_hash(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_sign_p256_without_hash */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha2 */

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha2(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha2 */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha384 */

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha384(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha384 */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha512 */

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha512(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_verif_p256_sha512 */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_ecdsa_verif_without_hash */

bool
Hacl_Interface_P256_ECDSA_ecdsa_verif_without_hash(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_ecdsa_verif_without_hash */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_verify_q */

bool Hacl_Interface_P256_ECDSA_verify_q(uint8_t *pubKey);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_verify_q */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_decompression_not_compressed_form */

bool Hacl_Interface_P256_ECDSA_decompression_not_compressed_form(uint8_t *b, uint8_t *result);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_decompression_not_compressed_form */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_decompression_compressed_form */

bool Hacl_Interface_P256_ECDSA_decompression_compressed_form(uint8_t *b, uint8_t *result);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_decompression_compressed_form */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_compression_not_compressed_form */

void Hacl_Interface_P256_ECDSA_compression_not_compressed_form(uint8_t *b, uint8_t *result);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_compression_not_compressed_form */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_compression_compressed_form */

void Hacl_Interface_P256_ECDSA_compression_compressed_form(uint8_t *b, uint8_t *result);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_compression_compressed_form */

/* SNIPPET_START: Hacl_Interface_P256_ECDSA_reduction_8_32 */

void Hacl_Interface_P256_ECDSA_reduction_8_32(uint8_t *x, uint8_t *result);

/* SNIPPET_END: Hacl_Interface_P256_ECDSA_reduction_8_32 */

#define __Hacl_Interface_P256_ECDSA_H_DEFINED
#endif
