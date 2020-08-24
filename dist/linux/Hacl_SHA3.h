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


#ifndef __Hacl_SHA3_H
#define __Hacl_SHA3_H

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

extern const u32 Hacl_Impl_SHA3_keccak_rotc[24U];

extern const u32 Hacl_Impl_SHA3_keccak_piln[24U];

extern const u64 Hacl_Impl_SHA3_keccak_rndc[24U];

u64 Hacl_Impl_SHA3_rotl(u64 a, u32 b);

void Hacl_Impl_SHA3_state_permute(u64 *s);

void Hacl_Impl_SHA3_loadState(u32 rateInBytes, u8 *input, u64 *s);

void Hacl_Impl_SHA3_storeState(u32 rateInBytes, u64 *s, u8 *res);

void
Hacl_Impl_SHA3_absorb(u64 *s, u32 rateInBytes, u32 inputByteLen, u8 *input, u8 delimitedSuffix);

void Hacl_Impl_SHA3_squeeze(u64 *s, u32 rateInBytes, u32 outputByteLen, u8 *output);

void
Hacl_Impl_SHA3_keccak(
  u32 rate,
  u32 capacity,
  u32 inputByteLen,
  u8 *input,
  u8 delimitedSuffix,
  u32 outputByteLen,
  u8 *output
);

void Hacl_SHA3_shake128_hacl(u32 inputByteLen, u8 *input, u32 outputByteLen, u8 *output);

void Hacl_SHA3_shake256_hacl(u32 inputByteLen, u8 *input, u32 outputByteLen, u8 *output);

void Hacl_SHA3_sha3_224(u32 inputByteLen, u8 *input, u8 *output);

void Hacl_SHA3_sha3_256(u32 inputByteLen, u8 *input, u8 *output);

void Hacl_SHA3_sha3_384(u32 inputByteLen, u8 *input, u8 *output);

void Hacl_SHA3_sha3_512(u32 inputByteLen, u8 *input, u8 *output);

#if defined(__cplusplus)
}
#endif

#define __Hacl_SHA3_H_DEFINED
#endif
