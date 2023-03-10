/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#ifndef __Hacl_Hash_Blake2s_128_H
#define __Hacl_Hash_Blake2s_128_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Lib_Memzero0.h"
#include "libintvector.h"

/* SNIPPET_START: Hacl_Blake2s_128_init */

void Hacl_Blake2s_128_init(Lib_IntVector_Intrinsics_vec128 *hash, uint32_t kk, uint32_t nn);

/* SNIPPET_END: Hacl_Blake2s_128_init */

/* SNIPPET_START: Hacl_Blake2s_128_update_key */

void
Hacl_Blake2s_128_update_key(
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t ll
);

/* SNIPPET_END: Hacl_Blake2s_128_update_key */

/* SNIPPET_START: Hacl_Blake2s_128_update_multi */

void
Hacl_Blake2s_128_update_multi(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  uint64_t prev,
  uint8_t *blocks,
  uint32_t nb
);

/* SNIPPET_END: Hacl_Blake2s_128_update_multi */

/* SNIPPET_START: Hacl_Blake2s_128_update_last */

void
Hacl_Blake2s_128_update_last(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  uint64_t prev,
  uint32_t rem,
  uint8_t *d
);

/* SNIPPET_END: Hacl_Blake2s_128_update_last */

/* SNIPPET_START: Hacl_Blake2s_128_finish */

void
Hacl_Blake2s_128_finish(uint32_t nn, uint8_t *output, Lib_IntVector_Intrinsics_vec128 *hash);

/* SNIPPET_END: Hacl_Blake2s_128_finish */

/* SNIPPET_START: Hacl_Blake2s_128_hash_with_key */

/**
Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 32.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0.
*/
void
Hacl_Blake2s_128_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);

/* SNIPPET_END: Hacl_Blake2s_128_hash_with_key */

/* SNIPPET_START: Hacl_Blake2s_128_store_state128s_to_state32 */

void
Hacl_Blake2s_128_store_state128s_to_state32(
  uint32_t *st32,
  Lib_IntVector_Intrinsics_vec128 *st
);

/* SNIPPET_END: Hacl_Blake2s_128_store_state128s_to_state32 */

/* SNIPPET_START: Hacl_Blake2s_128_load_state128s_from_state32 */

void
Hacl_Blake2s_128_load_state128s_from_state32(
  Lib_IntVector_Intrinsics_vec128 *st,
  uint32_t *st32
);

/* SNIPPET_END: Hacl_Blake2s_128_load_state128s_from_state32 */

/* SNIPPET_START: Hacl_Blake2s_128_malloc_with_key */

Lib_IntVector_Intrinsics_vec128 *Hacl_Blake2s_128_malloc_with_key(void);

/* SNIPPET_END: Hacl_Blake2s_128_malloc_with_key */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_Blake2s_128_H_DEFINED
#endif
