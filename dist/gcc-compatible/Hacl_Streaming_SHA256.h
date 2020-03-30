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

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __Hacl_Streaming_SHA256_H
#define __Hacl_Streaming_SHA256_H

#include "Hacl_Hash.h"


typedef uint32_t *Hacl_Streaming_SHA256_t;

typedef struct Hacl_Streaming_Functor_state_s___uint32_t__s
Hacl_Streaming_Functor_state_s___uint32_t_;

Hacl_Streaming_Functor_state_s___uint32_t_ *Hacl_Streaming_SHA256_create_in();

void Hacl_Streaming_SHA256_init(Hacl_Streaming_Functor_state_s___uint32_t_ *s);

void
Hacl_Streaming_SHA256_update(
  Hacl_Streaming_Functor_state_s___uint32_t_ *p,
  uint8_t *data,
  uint32_t len
);

void Hacl_Streaming_SHA256_finish(Hacl_Streaming_Functor_state_s___uint32_t_ *p, uint8_t *dst);

void Hacl_Streaming_SHA256_free(Hacl_Streaming_Functor_state_s___uint32_t_ *s);

#define __Hacl_Streaming_SHA256_H_DEFINED
#endif
