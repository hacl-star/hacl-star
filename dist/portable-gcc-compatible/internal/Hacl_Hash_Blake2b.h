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


#ifndef __internal_Hacl_Hash_Blake2b_H
#define __internal_Hacl_Hash_Blake2b_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_Impl_Blake2_Constants.h"
#include "../Hacl_Hash_Blake2b.h"

/* SNIPPET_START: Hacl_Hash_Blake2s_blake2_params */

typedef struct Hacl_Hash_Blake2s_blake2_params_s
{
  uint8_t digest_length;
  uint8_t key_length;
  uint8_t fanout;
  uint8_t depth;
  uint32_t leaf_length;
  uint64_t node_offset;
  uint8_t node_depth;
  uint8_t inner_length;
  uint8_t *salt;
  uint8_t *personal;
}
Hacl_Hash_Blake2s_blake2_params;

/* SNIPPET_END: Hacl_Hash_Blake2s_blake2_params */

/* SNIPPET_START: Hacl_Hash_Blake2b_init */

void Hacl_Hash_Blake2b_init(uint64_t *hash, uint32_t kk, uint32_t nn);

/* SNIPPET_END: Hacl_Hash_Blake2b_init */

/* SNIPPET_START: Hacl_Hash_Blake2b_update_multi */

void
Hacl_Hash_Blake2b_update_multi(
  uint32_t len,
  uint64_t *wv,
  uint64_t *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks,
  uint32_t nb
);

/* SNIPPET_END: Hacl_Hash_Blake2b_update_multi */

/* SNIPPET_START: Hacl_Hash_Blake2b_update_last */

void
Hacl_Hash_Blake2b_update_last(
  uint32_t len,
  uint64_t *wv,
  uint64_t *hash,
  FStar_UInt128_uint128 prev,
  uint32_t rem,
  uint8_t *d
);

/* SNIPPET_END: Hacl_Hash_Blake2b_update_last */

/* SNIPPET_START: Hacl_Hash_Blake2b_finish */

void Hacl_Hash_Blake2b_finish(uint32_t nn, uint8_t *output, uint64_t *hash);

/* SNIPPET_END: Hacl_Hash_Blake2b_finish */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Hash_Blake2b_H_DEFINED
#endif
