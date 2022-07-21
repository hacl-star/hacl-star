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


#ifndef __Hacl_HKDF_H
#define __Hacl_HKDF_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_HMAC.h"
#include "evercrypt_targetconfig.h"
/* SNIPPET_START: Hacl_HKDF_expand_sha2_256 */

void
Hacl_HKDF_expand_sha2_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: Hacl_HKDF_expand_sha2_256 */

/* SNIPPET_START: Hacl_HKDF_extract_sha2_256 */

void
Hacl_HKDF_extract_sha2_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: Hacl_HKDF_extract_sha2_256 */

/* SNIPPET_START: Hacl_HKDF_expand_sha2_512 */

void
Hacl_HKDF_expand_sha2_512(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: Hacl_HKDF_expand_sha2_512 */

/* SNIPPET_START: Hacl_HKDF_extract_sha2_512 */

void
Hacl_HKDF_extract_sha2_512(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: Hacl_HKDF_extract_sha2_512 */

/* SNIPPET_START: Hacl_HKDF_expand_blake2s_32 */

void
Hacl_HKDF_expand_blake2s_32(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: Hacl_HKDF_expand_blake2s_32 */

/* SNIPPET_START: Hacl_HKDF_extract_blake2s_32 */

void
Hacl_HKDF_extract_blake2s_32(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: Hacl_HKDF_extract_blake2s_32 */

/* SNIPPET_START: Hacl_HKDF_expand_blake2b_32 */

void
Hacl_HKDF_expand_blake2b_32(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: Hacl_HKDF_expand_blake2b_32 */

/* SNIPPET_START: Hacl_HKDF_extract_blake2b_32 */

void
Hacl_HKDF_extract_blake2b_32(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: Hacl_HKDF_extract_blake2b_32 */

#if defined(__cplusplus)
}
#endif

#define __Hacl_HKDF_H_DEFINED
#endif
