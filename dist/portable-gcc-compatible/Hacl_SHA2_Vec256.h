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


#ifndef __Hacl_SHA2_Vec256_H
#define __Hacl_SHA2_Vec256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_SHA2_Generic.h"
#include "Hacl_Krmllib.h"

/* SNIPPET_START: Hacl_SHA2_Vec256_sha224_8 */

void
Hacl_SHA2_Vec256_sha224_8(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint8_t *dst4,
  uint8_t *dst5,
  uint8_t *dst6,
  uint8_t *dst7,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *input4,
  uint8_t *input5,
  uint8_t *input6,
  uint8_t *input7
);

/* SNIPPET_END: Hacl_SHA2_Vec256_sha224_8 */

/* SNIPPET_START: Hacl_SHA2_Vec256_sha256_8 */

void
Hacl_SHA2_Vec256_sha256_8(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint8_t *dst4,
  uint8_t *dst5,
  uint8_t *dst6,
  uint8_t *dst7,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *input4,
  uint8_t *input5,
  uint8_t *input6,
  uint8_t *input7
);

/* SNIPPET_END: Hacl_SHA2_Vec256_sha256_8 */

/* SNIPPET_START: Hacl_SHA2_Vec256_sha384_4 */

void
Hacl_SHA2_Vec256_sha384_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
);

/* SNIPPET_END: Hacl_SHA2_Vec256_sha384_4 */

/* SNIPPET_START: Hacl_SHA2_Vec256_sha512_4 */

void
Hacl_SHA2_Vec256_sha512_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
);

/* SNIPPET_END: Hacl_SHA2_Vec256_sha512_4 */

#if defined(__cplusplus)
}
#endif

#define __Hacl_SHA2_Vec256_H_DEFINED
#endif
