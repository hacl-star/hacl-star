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


#ifndef __Hacl_Blake2s_32_H
#define __Hacl_Blake2s_32_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_Kremlib.h"
#include "Lib_Memzero0.h"
#include "Hacl_Impl_Blake2_Constants.h"

void Hacl_Blake2s_32_blake2s_init(u32 *wv, u32 *hash, u32 kk, u8 *k, u32 nn);

void
Hacl_Blake2s_32_blake2s_update_multi(u32 len, u32 *wv, u32 *hash, u64 prev, u8 *blocks, u32 nb);

void
Hacl_Blake2s_32_blake2s_update_last(u32 len, u32 *wv, u32 *hash, u64 prev, u32 rem, u8 *d);

typedef struct K___u32_u32_s
{
  u32 fst;
  u32 snd;
}
K___u32_u32;

void Hacl_Blake2s_32_blake2s_finish(u32 nn, u8 *output, u32 *hash);

void Hacl_Blake2s_32_blake2s(u32 nn, u8 *output, u32 ll, u8 *d, u32 kk, u8 *k);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Blake2s_32_H_DEFINED
#endif
