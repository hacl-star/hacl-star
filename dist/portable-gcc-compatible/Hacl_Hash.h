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

#ifndef __Hacl_Hash_H
#define __Hacl_Hash_H

#include "Hacl_Kremlib.h"


/* SNIPPET_START: Hacl_Hash_MD5_legacy_update_multi */

void Hacl_Hash_MD5_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_MD5_legacy_update_multi */

/* SNIPPET_START: Hacl_Hash_MD5_legacy_update_last */

void
Hacl_Hash_MD5_legacy_update_last(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_MD5_legacy_update_last */

/* SNIPPET_START: Hacl_Hash_MD5_legacy_hash */

void Hacl_Hash_MD5_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_MD5_legacy_hash */

/* SNIPPET_START: Hacl_Hash_Core_MD5_legacy_init */

void Hacl_Hash_Core_MD5_legacy_init(uint32_t *s);

/* SNIPPET_END: Hacl_Hash_Core_MD5_legacy_init */

/* SNIPPET_START: Hacl_Hash_Core_MD5_legacy_update */

void Hacl_Hash_Core_MD5_legacy_update(uint32_t *abcd, uint8_t *x);

/* SNIPPET_END: Hacl_Hash_Core_MD5_legacy_update */

/* SNIPPET_START: Hacl_Hash_Core_MD5_legacy_pad */

void Hacl_Hash_Core_MD5_legacy_pad(uint64_t len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_MD5_legacy_pad */

/* SNIPPET_START: Hacl_Hash_Core_MD5_legacy_finish */

void Hacl_Hash_Core_MD5_legacy_finish(uint32_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_MD5_legacy_finish */

/* SNIPPET_START: Hacl_Hash_SHA1_legacy_update_multi */

void Hacl_Hash_SHA1_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_SHA1_legacy_update_multi */

/* SNIPPET_START: Hacl_Hash_SHA1_legacy_update_last */

void
Hacl_Hash_SHA1_legacy_update_last(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_SHA1_legacy_update_last */

/* SNIPPET_START: Hacl_Hash_SHA1_legacy_hash */

void Hacl_Hash_SHA1_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_SHA1_legacy_hash */

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_init */

void Hacl_Hash_Core_SHA1_legacy_init(uint32_t *s);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_init */

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_update */

void Hacl_Hash_Core_SHA1_legacy_update(uint32_t *h, uint8_t *l);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_update */

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_pad */

void Hacl_Hash_Core_SHA1_legacy_pad(uint64_t len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_pad */

/* SNIPPET_START: Hacl_Hash_Core_SHA1_legacy_finish */

void Hacl_Hash_Core_SHA1_legacy_finish(uint32_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA1_legacy_finish */

/* SNIPPET_START: Hacl_Hash_SHA2_update_multi_224 */

void Hacl_Hash_SHA2_update_multi_224(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_SHA2_update_multi_224 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_multi_256 */

void Hacl_Hash_SHA2_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_SHA2_update_multi_256 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_multi_384 */

void Hacl_Hash_SHA2_update_multi_384(uint64_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_SHA2_update_multi_384 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_multi_512 */

void Hacl_Hash_SHA2_update_multi_512(uint64_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_SHA2_update_multi_512 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_last_224 */

void
Hacl_Hash_SHA2_update_last_224(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_SHA2_update_last_224 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_last_256 */

void
Hacl_Hash_SHA2_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_SHA2_update_last_256 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_last_384 */

void
Hacl_Hash_SHA2_update_last_384(
  uint64_t *s,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_SHA2_update_last_384 */

/* SNIPPET_START: Hacl_Hash_SHA2_update_last_512 */

void
Hacl_Hash_SHA2_update_last_512(
  uint64_t *s,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_SHA2_update_last_512 */

/* SNIPPET_START: Hacl_Hash_SHA2_hash_224 */

void Hacl_Hash_SHA2_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_SHA2_hash_224 */

/* SNIPPET_START: Hacl_Hash_SHA2_hash_256 */

void Hacl_Hash_SHA2_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_SHA2_hash_256 */

/* SNIPPET_START: Hacl_Hash_SHA2_hash_384 */

void Hacl_Hash_SHA2_hash_384(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_SHA2_hash_384 */

/* SNIPPET_START: Hacl_Hash_SHA2_hash_512 */

void Hacl_Hash_SHA2_hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_SHA2_hash_512 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_init_224 */

void Hacl_Hash_Core_SHA2_init_224(uint32_t *s);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_init_224 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_init_256 */

void Hacl_Hash_Core_SHA2_init_256(uint32_t *s);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_init_256 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_init_384 */

void Hacl_Hash_Core_SHA2_init_384(uint64_t *s);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_init_384 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_init_512 */

void Hacl_Hash_Core_SHA2_init_512(uint64_t *s);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_init_512 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_update_224 */

void Hacl_Hash_Core_SHA2_update_224(uint32_t *hash1, uint8_t *block);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_update_224 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_update_256 */

void Hacl_Hash_Core_SHA2_update_256(uint32_t *hash1, uint8_t *block);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_update_256 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_update_384 */

void Hacl_Hash_Core_SHA2_update_384(uint64_t *hash1, uint8_t *block);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_update_384 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_update_512 */

void Hacl_Hash_Core_SHA2_update_512(uint64_t *hash1, uint8_t *block);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_update_512 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_pad_224 */

void Hacl_Hash_Core_SHA2_pad_224(uint64_t len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_pad_224 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_pad_256 */

void Hacl_Hash_Core_SHA2_pad_256(uint64_t len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_pad_256 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_pad_384 */

void Hacl_Hash_Core_SHA2_pad_384(FStar_UInt128_uint128 len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_pad_384 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_pad_512 */

void Hacl_Hash_Core_SHA2_pad_512(FStar_UInt128_uint128 len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_pad_512 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_finish_224 */

void Hacl_Hash_Core_SHA2_finish_224(uint32_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_finish_224 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_finish_256 */

void Hacl_Hash_Core_SHA2_finish_256(uint32_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_finish_256 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_finish_384 */

void Hacl_Hash_Core_SHA2_finish_384(uint64_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_finish_384 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_finish_512 */

void Hacl_Hash_Core_SHA2_finish_512(uint64_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Core_SHA2_finish_512 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_Constants_k224_256 */

extern uint32_t Hacl_Hash_Core_SHA2_Constants_k224_256[64U];

/* SNIPPET_END: Hacl_Hash_Core_SHA2_Constants_k224_256 */

/* SNIPPET_START: Hacl_Hash_Core_SHA2_Constants_k384_512 */

extern uint64_t Hacl_Hash_Core_SHA2_Constants_k384_512[80U];

/* SNIPPET_END: Hacl_Hash_Core_SHA2_Constants_k384_512 */

#define __Hacl_Hash_H_DEFINED
#endif
