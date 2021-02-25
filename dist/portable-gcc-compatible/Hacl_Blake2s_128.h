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


#ifndef __Hacl_Blake2s_128_H
#define __Hacl_Blake2s_128_H

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
#include "Hacl_Blake2s_32.h"
#include "Lib_Memzero0.h"
#include "Hacl_Impl_Blake2_Constants.h"
#include "Hacl_Hash.h"

/* SNIPPET_START: Hacl_Hash_Blake2s_128_finish_blake2s_128 */

void
Hacl_Hash_Blake2s_128_finish_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t ev,
  uint8_t *dst
);

/* SNIPPET_END: Hacl_Hash_Blake2s_128_finish_blake2s_128 */

/* SNIPPET_START: Hacl_Hash_Blake2s_128_update_multi_blake2s_128 */

uint64_t
Hacl_Hash_Blake2s_128_update_multi_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

/* SNIPPET_END: Hacl_Hash_Blake2s_128_update_multi_blake2s_128 */

/* SNIPPET_START: Hacl_Hash_Blake2s_128_update_last_blake2s_128 */

uint64_t
Hacl_Hash_Blake2s_128_update_last_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t ev,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_Blake2s_128_update_last_blake2s_128 */

/* SNIPPET_START: Hacl_Hash_Blake2s_128_hash_blake2s_128 */

void Hacl_Hash_Blake2s_128_hash_blake2s_128(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Blake2s_128_hash_blake2s_128 */

/* SNIPPET_START: Hacl_Blake2s_128_blake2s_init */

void
Hacl_Blake2s_128_blake2s_init(
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t nn
);

/* SNIPPET_END: Hacl_Blake2s_128_blake2s_init */

/* SNIPPET_START: Hacl_Blake2s_128_blake2s_update_multi */

void
Hacl_Blake2s_128_blake2s_update_multi(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  uint64_t prev,
  uint8_t *blocks,
  uint32_t nb
);

/* SNIPPET_END: Hacl_Blake2s_128_blake2s_update_multi */

/* SNIPPET_START: Hacl_Blake2s_128_blake2s_update_last */

void
Hacl_Blake2s_128_blake2s_update_last(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec128 *wv,
  Lib_IntVector_Intrinsics_vec128 *hash,
  uint64_t prev,
  uint32_t rem,
  uint8_t *d
);

/* SNIPPET_END: Hacl_Blake2s_128_blake2s_update_last */

/* SNIPPET_START: Hacl_Blake2s_128_blake2s_finish */

void
Hacl_Blake2s_128_blake2s_finish(
  uint32_t nn,
  uint8_t *output,
  Lib_IntVector_Intrinsics_vec128 *hash
);

/* SNIPPET_END: Hacl_Blake2s_128_blake2s_finish */

/* SNIPPET_START: Hacl_Blake2s_128_blake2s */

void
Hacl_Blake2s_128_blake2s(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Blake2s_128_blake2s */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Blake2s_128_H_DEFINED
#endif
