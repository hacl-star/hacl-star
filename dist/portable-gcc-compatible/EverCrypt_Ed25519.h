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


#ifndef __EverCrypt_Ed25519_H
#define __EverCrypt_Ed25519_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Ed25519.h"

/* SNIPPET_START: EverCrypt_Ed25519_secret_to_public */

void EverCrypt_Ed25519_secret_to_public(uint8_t *public_key, uint8_t *private_key);

/* SNIPPET_END: EverCrypt_Ed25519_secret_to_public */

/* SNIPPET_START: EverCrypt_Ed25519_expand_keys */

void EverCrypt_Ed25519_expand_keys(uint8_t *expanded_keys, uint8_t *private_key);

/* SNIPPET_END: EverCrypt_Ed25519_expand_keys */

/* SNIPPET_START: EverCrypt_Ed25519_sign_expanded */

void
EverCrypt_Ed25519_sign_expanded(
  uint8_t *signature,
  uint8_t *expanded_keys,
  uint32_t msg_len,
  uint8_t *msg
);

/* SNIPPET_END: EverCrypt_Ed25519_sign_expanded */

/* SNIPPET_START: EverCrypt_Ed25519_sign */

void
EverCrypt_Ed25519_sign(
  uint8_t *signature,
  uint8_t *private_key,
  uint32_t msg_len,
  uint8_t *msg
);

/* SNIPPET_END: EverCrypt_Ed25519_sign */

/* SNIPPET_START: EverCrypt_Ed25519_verify */

bool
EverCrypt_Ed25519_verify(
  uint8_t *public_key,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *signature
);

/* SNIPPET_END: EverCrypt_Ed25519_verify */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Ed25519_H_DEFINED
#endif
