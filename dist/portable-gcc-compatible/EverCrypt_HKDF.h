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


#ifndef __EverCrypt_HKDF_H
#define __EverCrypt_HKDF_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "EverCrypt_HMAC.h"

/* SNIPPET_START: EverCrypt_HKDF_expand_sha1 */

void
EverCrypt_HKDF_expand_sha1(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand_sha1 */

/* SNIPPET_START: EverCrypt_HKDF_extract_sha1 */

void
EverCrypt_HKDF_extract_sha1(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract_sha1 */

/* SNIPPET_START: EverCrypt_HKDF_expand_sha2_256 */

void
EverCrypt_HKDF_expand_sha2_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand_sha2_256 */

/* SNIPPET_START: EverCrypt_HKDF_extract_sha2_256 */

void
EverCrypt_HKDF_extract_sha2_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract_sha2_256 */

/* SNIPPET_START: EverCrypt_HKDF_expand_sha2_384 */

void
EverCrypt_HKDF_expand_sha2_384(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand_sha2_384 */

/* SNIPPET_START: EverCrypt_HKDF_extract_sha2_384 */

void
EverCrypt_HKDF_extract_sha2_384(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract_sha2_384 */

/* SNIPPET_START: EverCrypt_HKDF_expand_sha2_512 */

void
EverCrypt_HKDF_expand_sha2_512(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand_sha2_512 */

/* SNIPPET_START: EverCrypt_HKDF_extract_sha2_512 */

void
EverCrypt_HKDF_extract_sha2_512(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract_sha2_512 */

/* SNIPPET_START: EverCrypt_HKDF_expand_blake2s */

void
EverCrypt_HKDF_expand_blake2s(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand_blake2s */

/* SNIPPET_START: EverCrypt_HKDF_extract_blake2s */

void
EverCrypt_HKDF_extract_blake2s(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract_blake2s */

/* SNIPPET_START: EverCrypt_HKDF_expand_blake2b */

void
EverCrypt_HKDF_expand_blake2b(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand_blake2b */

/* SNIPPET_START: EverCrypt_HKDF_extract_blake2b */

void
EverCrypt_HKDF_extract_blake2b(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract_blake2b */

/* SNIPPET_START: EverCrypt_HKDF_expand */

/**
Expand pseudorandom key to desired length.

@param a Hash function to use. Usually, the same as used in `EverCrypt_HKDF_extract`.
@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from.
@param infolen Length of context and application specific information. Can be 0.
@param len Length of output keying material.
*/
void
EverCrypt_HKDF_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

/* SNIPPET_END: EverCrypt_HKDF_expand */

/* SNIPPET_START: EverCrypt_HKDF_extract */

/**
Extract a fixed-length pseudorandom key from input keying material.

@param a Hash function to use. The allowed values are:
  * `Spec_Hash_Definitions_Blake2B` (`HashLen` = 64), 
  * `Spec_Hash_Definitions_Blake2S` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_256` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_384` (`HashLen` = 48), 
  * `Spec_Hash_Definitions_SHA2_512` (`HashLen` = 64), and
  * `Spec_Hash_Definitions_SHA1` (`HashLen` = 20).
@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
  `HashLen` depends on the used algorithm `a`. See above.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material.
*/
void
EverCrypt_HKDF_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

/* SNIPPET_END: EverCrypt_HKDF_extract */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_HKDF_H_DEFINED
#endif
