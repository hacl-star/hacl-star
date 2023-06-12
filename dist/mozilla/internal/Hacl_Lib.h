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


#ifndef __internal_Hacl_Lib_H
#define __internal_Hacl_Lib_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

typedef struct Lib_Transposition64x8_uint64x2_s
{
  uint64_t fst;
  uint64_t snd;
}
Lib_Transposition64x8_uint64x2;

typedef struct Lib_Transposition64x8_uint64x4_s
{
  Lib_Transposition64x8_uint64x2 fst;
  Lib_Transposition64x8_uint64x2 snd;
}
Lib_Transposition64x8_uint64x4;

typedef struct Lib_Transposition64x8_uint64x8_s
{
  Lib_Transposition64x8_uint64x4 fst;
  Lib_Transposition64x8_uint64x4 snd;
}
Lib_Transposition64x8_uint64x8;

uint64_t Lib_Transposition64x8_transpose_bits64(uint64_t x);

Lib_Transposition64x8_uint64x8
Lib_Transposition64x8_transpose_bits64x8(Lib_Transposition64x8_uint64x8 a);

Lib_Transposition64x8_uint64x8
Lib_Transposition64x8_transpose_bits64x8_inv(Lib_Transposition64x8_uint64x8 a);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Lib_H_DEFINED
#endif
