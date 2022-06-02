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


#ifndef __Hacl_Impl_Blake2_Constants_H
#define __Hacl_Impl_Blake2_Constants_H
#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"



#include "lib_intrinsics.h"
extern const uint32_t Hacl_Impl_Blake2_Constants_sigmaTable[160U];

extern const uint32_t Hacl_Impl_Blake2_Constants_ivTable_S[8U];

extern const uint64_t Hacl_Impl_Blake2_Constants_ivTable_B[8U];

extern const uint32_t Hacl_Impl_Blake2_Constants_rTable_B[4U];


#define __Hacl_Impl_Blake2_Constants_H_DEFINED
#endif
