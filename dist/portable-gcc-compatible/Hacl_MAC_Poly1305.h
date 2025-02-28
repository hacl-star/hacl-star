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


#ifndef __Hacl_MAC_Poly1305_H
#define __Hacl_MAC_Poly1305_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Streaming_Types.h"

/* SNIPPET_START: Hacl_MAC_Poly1305_state_t */

typedef struct Hacl_MAC_Poly1305_state_t_s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
  uint8_t *p_key;
}
Hacl_MAC_Poly1305_state_t;

/* SNIPPET_END: Hacl_MAC_Poly1305_state_t */

/* SNIPPET_START: Hacl_MAC_Poly1305_malloc */

Hacl_MAC_Poly1305_state_t *Hacl_MAC_Poly1305_malloc(uint8_t *key);

/* SNIPPET_END: Hacl_MAC_Poly1305_malloc */

/* SNIPPET_START: Hacl_MAC_Poly1305_reset */

void Hacl_MAC_Poly1305_reset(Hacl_MAC_Poly1305_state_t *state, uint8_t *key);

/* SNIPPET_END: Hacl_MAC_Poly1305_reset */

/* SNIPPET_START: Hacl_MAC_Poly1305_update */

/**
0 = success, 1 = max length exceeded
*/
Hacl_Streaming_Types_error_code
Hacl_MAC_Poly1305_update(Hacl_MAC_Poly1305_state_t *state, uint8_t *chunk, uint32_t chunk_len);

/* SNIPPET_END: Hacl_MAC_Poly1305_update */

/* SNIPPET_START: Hacl_MAC_Poly1305_digest */

void Hacl_MAC_Poly1305_digest(Hacl_MAC_Poly1305_state_t *state, uint8_t *output);

/* SNIPPET_END: Hacl_MAC_Poly1305_digest */

/* SNIPPET_START: Hacl_MAC_Poly1305_free */

void Hacl_MAC_Poly1305_free(Hacl_MAC_Poly1305_state_t *state);

/* SNIPPET_END: Hacl_MAC_Poly1305_free */

/* SNIPPET_START: Hacl_MAC_Poly1305_mac */

void Hacl_MAC_Poly1305_mac(uint8_t *output, uint8_t *input, uint32_t input_len, uint8_t *key);

/* SNIPPET_END: Hacl_MAC_Poly1305_mac */

#if defined(__cplusplus)
}
#endif

#define __Hacl_MAC_Poly1305_H_DEFINED
#endif
