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


#ifndef __Hacl_Blake2s_32_H
#define __Hacl_Blake2s_32_H

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
#include "Lib_Memzero0.h"
#include "Hacl_Impl_Blake2_Constants.h"

/* SNIPPET_START: Hacl_Blake2s_32_blake2s_init */

void
Hacl_Blake2s_32_blake2s_init(
  uint32_t *wv,
  uint32_t *hash,
  uint32_t kk,
  uint8_t *k,
  uint32_t nn
);

/* SNIPPET_END: Hacl_Blake2s_32_blake2s_init */

/* SNIPPET_START: Hacl_Blake2s_32_blake2s_update_multi */

void
Hacl_Blake2s_32_blake2s_update_multi(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint8_t *blocks,
  uint32_t nb
);

/* SNIPPET_END: Hacl_Blake2s_32_blake2s_update_multi */

/* SNIPPET_START: Hacl_Blake2s_32_blake2s_update_last */

void
Hacl_Blake2s_32_blake2s_update_last(
  uint32_t len,
  uint32_t *wv,
  uint32_t *hash,
  uint64_t prev,
  uint32_t rem,
  uint8_t *d
);

/* SNIPPET_END: Hacl_Blake2s_32_blake2s_update_last */

/* SNIPPET_START: K___uint32_t_uint32_t */

typedef struct K___uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
}
K___uint32_t_uint32_t;

/* SNIPPET_END: K___uint32_t_uint32_t */

/* SNIPPET_START: Hacl_Blake2s_32_blake2s_finish */

void Hacl_Blake2s_32_blake2s_finish(uint32_t nn, uint8_t *output, uint32_t *hash);

/* SNIPPET_END: Hacl_Blake2s_32_blake2s_finish */

/* SNIPPET_START: Hacl_Blake2s_32_blake2s */

void
Hacl_Blake2s_32_blake2s(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Blake2s_32_blake2s */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Blake2s_32_H_DEFINED
#endif
