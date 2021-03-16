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


#ifndef __Hacl_Impl_P521_Exponent_H
#define __Hacl_Impl_P521_Exponent_H
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "lib_intrinsics.h"




typedef uint64_t *Hacl_Impl_P521_Exponent_felem_521;

extern void
Hacl_Impl_P521_Exponent_montgomery_multiplication_buffer(
  uint64_t *a,
  uint64_t *b,
  uint64_t *result
);

extern void Hacl_Impl_P521_Exponent_montgomery_square_buffer(uint64_t *a, uint64_t *result);

extern void Hacl_Impl_P521_Exponent_fsquarePowN(uint32_t n, uint64_t *a);

void
Hacl_Impl_P521_Exponent_exponent_p521(uint64_t *t, uint64_t *result, uint64_t *tempBuffer);


#define __Hacl_Impl_P521_Exponent_H_DEFINED
#endif
