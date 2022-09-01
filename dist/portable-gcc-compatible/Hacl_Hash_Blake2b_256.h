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


#ifndef __Hacl_Hash_Blake2b_256_H
#define __Hacl_Hash_Blake2b_256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Lib_Memzero0.h"
#include "Hacl_Krmllib.h"
#include "Hacl_Impl_Blake2_Constants.h"
#include "evercrypt_targetconfig.h"
#include "libintvector.h"
/* SNIPPET_START: Hacl_Blake2b_256_blake2b_init */

void
Hacl_Blake2b_256_blake2b_init(Lib_IntVector_Intrinsics_vec256 *hash, uint32_t kk, uint32_t nn);

/* SNIPPET_END: Hacl_Blake2b_256_blake2b_init */

/* SNIPPET_START: Hacl_Blake2b_256_blake2b_update_key */

void
Hacl_Blake2b_256_blake2b_update_key(
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t ll
);

/* SNIPPET_END: Hacl_Blake2b_256_blake2b_update_key */

/* SNIPPET_START: Hacl_Blake2b_256_blake2b_update_multi */

void
Hacl_Blake2b_256_blake2b_update_multi(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint8_t *blocks,
  uint32_t nb
);

/* SNIPPET_END: Hacl_Blake2b_256_blake2b_update_multi */

/* SNIPPET_START: Hacl_Blake2b_256_blake2b_update_last */

void
Hacl_Blake2b_256_blake2b_update_last(
  uint32_t len,
  Lib_IntVector_Intrinsics_vec256 *wv,
  Lib_IntVector_Intrinsics_vec256 *hash,
  FStar_UInt128_uint128 prev,
  uint32_t rem,
  uint8_t *d
);

/* SNIPPET_END: Hacl_Blake2b_256_blake2b_update_last */

/* SNIPPET_START: Hacl_Blake2b_256_blake2b_finish */

void
Hacl_Blake2b_256_blake2b_finish(
  uint32_t nn,
  uint8_t *output,
  Lib_IntVector_Intrinsics_vec256 *hash
);

/* SNIPPET_END: Hacl_Blake2b_256_blake2b_finish */

/* SNIPPET_START: Hacl_Blake2b_256_blake2b */

void
Hacl_Blake2b_256_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Blake2b_256_blake2b */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_Blake2b_256_H_DEFINED
#endif
