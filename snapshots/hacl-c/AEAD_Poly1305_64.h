/* MIT License
 *
 * Copyright (c) 2016-2017 INRIA and Microsoft Corporation
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


#include "kremlib.h"
#ifndef __AEAD_Poly1305_64_H
#define __AEAD_Poly1305_64_H




typedef struct Hacl_Impl_Poly1305_64_State_poly1305_state_s
{
  uint64_t *r;
  uint64_t *h;
}
Hacl_Impl_Poly1305_64_State_poly1305_state;

typedef uint8_t *AEAD_Poly1305_64_uint8_p;

typedef uint8_t *AEAD_Poly1305_64_key;

typedef Hacl_Impl_Poly1305_64_State_poly1305_state AEAD_Poly1305_64_state;

Hacl_Impl_Poly1305_64_State_poly1305_state
AEAD_Poly1305_64_mk_state(uint64_t *r, uint64_t *acc);

void
AEAD_Poly1305_64_poly1305_blocks_init(
  Hacl_Impl_Poly1305_64_State_poly1305_state st,
  uint8_t *input,
  uint32_t len1,
  uint8_t *k1
);

void
AEAD_Poly1305_64_poly1305_blocks_continue(
  Hacl_Impl_Poly1305_64_State_poly1305_state st,
  uint8_t *input,
  uint32_t len1
);

void
AEAD_Poly1305_64_poly1305_blocks_finish(
  Hacl_Impl_Poly1305_64_State_poly1305_state st,
  uint8_t *input,
  uint8_t *mac,
  uint8_t *key_s
);

#define __AEAD_Poly1305_64_H_DEFINED
#endif
