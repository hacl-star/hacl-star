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


#ifndef __Hacl_Hash_SHA1_H
#define __Hacl_Hash_SHA1_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Streaming_Types.h"

/* SNIPPET_START: Hacl_Streaming_SHA1_state */

typedef Hacl_Streaming_MD_state_32 Hacl_Streaming_SHA1_state;

/* SNIPPET_END: Hacl_Streaming_SHA1_state */

/* SNIPPET_START: Hacl_Streaming_SHA1_malloc */

Hacl_Streaming_MD_state_32 *Hacl_Streaming_SHA1_malloc(void);

/* SNIPPET_END: Hacl_Streaming_SHA1_malloc */

/* SNIPPET_START: Hacl_Streaming_SHA1_reset */

void Hacl_Streaming_SHA1_reset(Hacl_Streaming_MD_state_32 *state1);

/* SNIPPET_END: Hacl_Streaming_SHA1_reset */

/* SNIPPET_START: Hacl_Streaming_SHA1_update */

/**
0 = success, 1 = max length exceeded
*/
uint32_t
Hacl_Streaming_SHA1_update(
  Hacl_Streaming_MD_state_32 *state1,
  uint8_t *chunk,
  uint32_t chunk_len
);

/* SNIPPET_END: Hacl_Streaming_SHA1_update */

/* SNIPPET_START: Hacl_Streaming_SHA1_digest */

void Hacl_Streaming_SHA1_digest(Hacl_Streaming_MD_state_32 *state1, uint8_t *output);

/* SNIPPET_END: Hacl_Streaming_SHA1_digest */

/* SNIPPET_START: Hacl_Streaming_SHA1_free */

void Hacl_Streaming_SHA1_free(Hacl_Streaming_MD_state_32 *state1);

/* SNIPPET_END: Hacl_Streaming_SHA1_free */

/* SNIPPET_START: Hacl_Streaming_SHA1_copy */

Hacl_Streaming_MD_state_32 *Hacl_Streaming_SHA1_copy(Hacl_Streaming_MD_state_32 *s0);

/* SNIPPET_END: Hacl_Streaming_SHA1_copy */

/* SNIPPET_START: Hacl_Streaming_SHA1_hash */

void Hacl_Streaming_SHA1_hash(uint8_t *output, uint8_t *input, uint32_t input_len);

/* SNIPPET_END: Hacl_Streaming_SHA1_hash */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_SHA1_H_DEFINED
#endif
