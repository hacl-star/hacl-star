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


#ifndef __internal_Hacl_Hash_Blake2s_128_H
#define __internal_Hacl_Hash_Blake2s_128_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Hash_Blake2.h"
#include "../Hacl_Hash_Blake2s_128.h"
#include "libintvector.h"
uint64_t Hacl_Hash_Blake2s_128_init_blake2s_128(Lib_IntVector_Intrinsics_vec128 *s);

uint64_t
Hacl_Hash_Blake2s_128_update_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t totlen,
  uint8_t *block
);

void
Hacl_Hash_Blake2s_128_finish_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t ev,
  uint8_t *dst
);

uint64_t
Hacl_Hash_Blake2s_128_update_multi_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

uint64_t
Hacl_Hash_Blake2s_128_update_last_blake2s_128(
  Lib_IntVector_Intrinsics_vec128 *s,
  uint64_t ev,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

void Hacl_Hash_Blake2s_128_hash_blake2s_128(uint8_t *input, uint32_t input_len, uint8_t *dst);

Lib_IntVector_Intrinsics_vec128 *Hacl_Hash_Blake2s_128_malloc_blake2s_128();

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Hash_Blake2s_128_H_DEFINED
#endif
