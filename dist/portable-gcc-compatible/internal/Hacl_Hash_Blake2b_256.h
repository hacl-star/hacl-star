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


#ifndef __internal_Hacl_Hash_Blake2b_256_H
#define __internal_Hacl_Hash_Blake2b_256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Hash_Blake2.h"
#include "../Hacl_Hash_Blake2b_256.h"
#include "libintvector.h"
/* SNIPPET_START: Hacl_Hash_Blake2b_256_init_blake2b_256 */

FStar_UInt128_uint128
Hacl_Hash_Blake2b_256_init_blake2b_256(Lib_IntVector_Intrinsics_vec256 *s);

/* SNIPPET_END: Hacl_Hash_Blake2b_256_init_blake2b_256 */

/* SNIPPET_START: Hacl_Hash_Blake2b_256_update_blake2b_256 */

FStar_UInt128_uint128
Hacl_Hash_Blake2b_256_update_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 totlen,
  uint8_t *block
);

/* SNIPPET_END: Hacl_Hash_Blake2b_256_update_blake2b_256 */

/* SNIPPET_START: Hacl_Hash_Blake2b_256_finish_blake2b_256 */

void
Hacl_Hash_Blake2b_256_finish_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 ev,
  uint8_t *dst
);

/* SNIPPET_END: Hacl_Hash_Blake2b_256_finish_blake2b_256 */

/* SNIPPET_START: Hacl_Hash_Blake2b_256_update_multi_blake2b_256 */

FStar_UInt128_uint128
Hacl_Hash_Blake2b_256_update_multi_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

/* SNIPPET_END: Hacl_Hash_Blake2b_256_update_multi_blake2b_256 */

/* SNIPPET_START: Hacl_Hash_Blake2b_256_update_last_blake2b_256 */

FStar_UInt128_uint128
Hacl_Hash_Blake2b_256_update_last_blake2b_256(
  Lib_IntVector_Intrinsics_vec256 *s,
  FStar_UInt128_uint128 ev,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: Hacl_Hash_Blake2b_256_update_last_blake2b_256 */

/* SNIPPET_START: Hacl_Hash_Blake2b_256_hash_blake2b_256 */

void Hacl_Hash_Blake2b_256_hash_blake2b_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_Blake2b_256_hash_blake2b_256 */

/* SNIPPET_START: Hacl_Hash_Blake2b_256_malloc_blake2b_256 */

Lib_IntVector_Intrinsics_vec256 *Hacl_Hash_Blake2b_256_malloc_blake2b_256();

/* SNIPPET_END: Hacl_Hash_Blake2b_256_malloc_blake2b_256 */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Hash_Blake2b_256_H_DEFINED
#endif
