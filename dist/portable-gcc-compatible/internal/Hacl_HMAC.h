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


#ifndef __internal_Hacl_HMAC_H
#define __internal_Hacl_HMAC_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_Blake2.h"
#include "../Hacl_HMAC.h"

/* SNIPPET_START: K____uint32_t__uint64_t */

typedef struct K____uint32_t__uint64_t_s
{
  uint32_t *fst;
  uint64_t snd;
}
K____uint32_t__uint64_t;

/* SNIPPET_END: K____uint32_t__uint64_t */

/* SNIPPET_START: K____uint64_t__FStar_UInt128_uint128 */

typedef struct K____uint64_t__FStar_UInt128_uint128_s
{
  uint64_t *fst;
  FStar_UInt128_uint128 snd;
}
K____uint64_t__FStar_UInt128_uint128;

/* SNIPPET_END: K____uint64_t__FStar_UInt128_uint128 */

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_HMAC_H_DEFINED
#endif
