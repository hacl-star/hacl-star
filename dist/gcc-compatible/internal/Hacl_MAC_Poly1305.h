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


#ifndef __internal_Hacl_MAC_Poly1305_H
#define __internal_Hacl_MAC_Poly1305_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_Streaming_Types.h"
#include "../Hacl_MAC_Poly1305.h"

void Hacl_MAC_Poly1305_poly1305_init(uint64_t *ctx, uint8_t *key);

void Hacl_MAC_Poly1305_poly1305_finish(uint8_t *tag, uint8_t *key, uint64_t *ctx);

typedef struct Hacl_MAC_Poly1305_state_t_s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
  uint8_t *p_key;
}
Hacl_MAC_Poly1305_state_t;

typedef struct FStar_Pervasives_Native_option___uint8_t__s
{
  Hacl_Streaming_Types_optional tag;
  uint8_t *v;
}
FStar_Pervasives_Native_option___uint8_t_;

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_MAC_Poly1305_H_DEFINED
#endif
