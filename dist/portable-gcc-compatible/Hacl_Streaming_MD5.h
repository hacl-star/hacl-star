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


#ifndef __Hacl_Streaming_MD5_H
#define __Hacl_Streaming_MD5_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Streaming_SHA2.h"
#include "Hacl_Hash_MD5.h"

/* SNIPPET_START: Hacl_Streaming_MD5_state_md5 */

typedef Hacl_Streaming_SHA2_state_sha2_224 Hacl_Streaming_MD5_state_md5;

/* SNIPPET_END: Hacl_Streaming_MD5_state_md5 */

/* SNIPPET_START: Hacl_Streaming_MD5_legacy_create_in_md5 */

Hacl_Streaming_SHA2_state_sha2_224 *Hacl_Streaming_MD5_legacy_create_in_md5();

/* SNIPPET_END: Hacl_Streaming_MD5_legacy_create_in_md5 */

/* SNIPPET_START: Hacl_Streaming_MD5_legacy_init_md5 */

void Hacl_Streaming_MD5_legacy_init_md5(Hacl_Streaming_SHA2_state_sha2_224 *s);

/* SNIPPET_END: Hacl_Streaming_MD5_legacy_init_md5 */

/* SNIPPET_START: Hacl_Streaming_MD5_legacy_update_md5 */

/**
0 = success, 1 = max length exceeded
*/
uint32_t
Hacl_Streaming_MD5_legacy_update_md5(
  Hacl_Streaming_SHA2_state_sha2_224 *p,
  uint8_t *data,
  uint32_t len
);

/* SNIPPET_END: Hacl_Streaming_MD5_legacy_update_md5 */

/* SNIPPET_START: Hacl_Streaming_MD5_legacy_finish_md5 */

void Hacl_Streaming_MD5_legacy_finish_md5(Hacl_Streaming_SHA2_state_sha2_224 *p, uint8_t *dst);

/* SNIPPET_END: Hacl_Streaming_MD5_legacy_finish_md5 */

/* SNIPPET_START: Hacl_Streaming_MD5_legacy_free_md5 */

void Hacl_Streaming_MD5_legacy_free_md5(Hacl_Streaming_SHA2_state_sha2_224 *s);

/* SNIPPET_END: Hacl_Streaming_MD5_legacy_free_md5 */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Streaming_MD5_H_DEFINED
#endif
