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
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_Hash_H
#define __Hacl_Hash_H

#include "Hacl_Kremlib.h"


void Hacl_Hash_MD5_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

void
Hacl_Hash_MD5_legacy_update_last(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void Hacl_Hash_MD5_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_Core_MD5_legacy_init(uint32_t *s);

void Hacl_Hash_Core_MD5_legacy_update(uint32_t *abcd, uint8_t *x);

void Hacl_Hash_Core_MD5_legacy_pad(uint64_t len, uint8_t *dst);

void Hacl_Hash_Core_MD5_legacy_finish(uint32_t *s, uint8_t *dst);

void Hacl_Hash_SHA1_legacy_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

void
Hacl_Hash_SHA1_legacy_update_last(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void Hacl_Hash_SHA1_legacy_hash(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_Core_SHA1_legacy_init(uint32_t *s);

void Hacl_Hash_Core_SHA1_legacy_update(uint32_t *h, uint8_t *l);

void Hacl_Hash_Core_SHA1_legacy_pad(uint64_t len, uint8_t *dst);

void Hacl_Hash_Core_SHA1_legacy_finish(uint32_t *s, uint8_t *dst);

void Hacl_Hash_SHA2_update_multi_224(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

void Hacl_Hash_SHA2_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

void Hacl_Hash_SHA2_update_multi_384(uint64_t *s, uint8_t *blocks, uint32_t n_blocks);

void Hacl_Hash_SHA2_update_multi_512(uint64_t *s, uint8_t *blocks, uint32_t n_blocks);

void
Hacl_Hash_SHA2_update_last_224(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void
Hacl_Hash_SHA2_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void
Hacl_Hash_SHA2_update_last_384(
  uint64_t *s,
  uint128_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void
Hacl_Hash_SHA2_update_last_512(
  uint64_t *s,
  uint128_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void Hacl_Hash_SHA2_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_SHA2_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_SHA2_hash_384(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_SHA2_hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_Core_SHA2_init_224(uint32_t *s);

void Hacl_Hash_Core_SHA2_init_256(uint32_t *s);

void Hacl_Hash_Core_SHA2_init_384(uint64_t *s);

void Hacl_Hash_Core_SHA2_init_512(uint64_t *s);

void Hacl_Hash_Core_SHA2_update_224(uint32_t *hash1, uint8_t *block);

void Hacl_Hash_Core_SHA2_update_256(uint32_t *hash1, uint8_t *block);

void Hacl_Hash_Core_SHA2_update_384(uint64_t *hash1, uint8_t *block);

void Hacl_Hash_Core_SHA2_update_512(uint64_t *hash1, uint8_t *block);

void Hacl_Hash_Core_SHA2_pad_224(uint64_t len, uint8_t *dst);

void Hacl_Hash_Core_SHA2_pad_256(uint64_t len, uint8_t *dst);

void Hacl_Hash_Core_SHA2_pad_384(uint128_t len, uint8_t *dst);

void Hacl_Hash_Core_SHA2_pad_512(uint128_t len, uint8_t *dst);

void Hacl_Hash_Core_SHA2_finish_224(uint32_t *s, uint8_t *dst);

void Hacl_Hash_Core_SHA2_finish_256(uint32_t *s, uint8_t *dst);

void Hacl_Hash_Core_SHA2_finish_384(uint64_t *s, uint8_t *dst);

void Hacl_Hash_Core_SHA2_finish_512(uint64_t *s, uint8_t *dst);

extern uint32_t Hacl_Hash_Core_SHA2_Constants_k224_256[64U];

extern uint64_t Hacl_Hash_Core_SHA2_Constants_k384_512[80U];

#define __Hacl_Hash_H_DEFINED
#endif
