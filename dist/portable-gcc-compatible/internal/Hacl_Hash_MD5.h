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


#ifndef __internal_Hacl_Hash_MD5_H
#define __internal_Hacl_Hash_MD5_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_Hash_Blake2b.h"
#include "../Hacl_Hash_MD5.h"

/* SNIPPET_START: Hacl_Hash_MD5_init */

void Hacl_Hash_MD5_init(uint32_t *s);

/* SNIPPET_END: Hacl_Hash_MD5_init */

/* SNIPPET_START: Hacl_Hash_MD5_finish */

void Hacl_Hash_MD5_finish(uint32_t *s, uint8_t *dst);

/* SNIPPET_END: Hacl_Hash_MD5_finish */

/* SNIPPET_START: Hacl_Hash_MD5_update_multi */

void Hacl_Hash_MD5_update_multi(uint32_t *s, uint8_t *blocks, uint32_t n_blocks);

/* SNIPPET_END: Hacl_Hash_MD5_update_multi */

/* SNIPPET_START: Hacl_Hash_MD5_update_last */

void
Hacl_Hash_MD5_update_last(uint32_t *s, uint64_t prev_len, uint8_t *input, uint32_t input_len);

/* SNIPPET_END: Hacl_Hash_MD5_update_last */

/* SNIPPET_START: Hacl_Hash_MD5_hash_oneshot */

void Hacl_Hash_MD5_hash_oneshot(uint8_t *output, uint8_t *input, uint32_t input_len);

/* SNIPPET_END: Hacl_Hash_MD5_hash_oneshot */

/* SNIPPET_START: FStar_Pervasives_Native_option___uint32_t_ */

typedef struct FStar_Pervasives_Native_option___uint32_t__s
{
  FStar_Pervasives_Native_option___uint8_t___uint8_t___bool_____uint64_t_____uint64_t____tags
  tag;
  uint32_t *v;
}
FStar_Pervasives_Native_option___uint32_t_;

/* SNIPPET_END: FStar_Pervasives_Native_option___uint32_t_ */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Hash_MD5_H_DEFINED
#endif
