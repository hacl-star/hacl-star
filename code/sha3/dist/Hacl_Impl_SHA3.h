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


#ifndef __Hacl_Impl_SHA3_H
#define __Hacl_Impl_SHA3_H
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "lib_intrinsics.h"


#include "Hacl_Lib.h"

extern const uint32_t Hacl_Impl_SHA3_keccak_rotc[24U];

extern const uint32_t Hacl_Impl_SHA3_keccak_piln[24U];

extern const uint64_t Hacl_Impl_SHA3_keccak_rndc[24U];

uint64_t Hacl_Impl_SHA3_rotl(uint64_t a, uint32_t b);

void Hacl_Impl_SHA3_state_permute(uint64_t *s);

void Hacl_Impl_SHA3_loadState(uint32_t rateInBytes, uint8_t *input, uint64_t *s);

void Hacl_Impl_SHA3_storeState(uint32_t rateInBytes, uint64_t *s, uint8_t *res);

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__uint8_t_tags;

typedef struct FStar_Pervasives_Native_option__uint8_t_s
{
  FStar_Pervasives_Native_option__uint8_t_tags tag;
  uint8_t v;
}
FStar_Pervasives_Native_option__uint8_t;

#define Hacl_Impl_SHA3_SHA3_224 0
#define Hacl_Impl_SHA3_Generic 1

typedef uint8_t Hacl_Impl_SHA3_version_tags;

typedef struct Hacl_Impl_SHA3_version_s
{
  Hacl_Impl_SHA3_version_tags tag;
  FStar_Pervasives_Native_option__uint8_t _0;
}
Hacl_Impl_SHA3_version;

bool Hacl_Impl_SHA3_uu___is_SHA3_224(Hacl_Impl_SHA3_version projectee);

bool Hacl_Impl_SHA3_uu___is_Generic(Hacl_Impl_SHA3_version projectee);

FStar_Pervasives_Native_option__uint8_t
Hacl_Impl_SHA3___proj__Generic__item___0(Hacl_Impl_SHA3_version projectee);

void
Hacl_Impl_SHA3_absorb_last_224(
  uint8_t delimitedSuffix,
  uint32_t rem,
  uint8_t *input,
  uint64_t *s
);

void Hacl_Impl_SHA3_absorb_inner(uint32_t rateInBytes, uint8_t *block, uint64_t *s);

void
Hacl_Impl_SHA3_squeeze(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t outputByteLen,
  uint8_t *output
);

void
Hacl_Impl_SHA3_keccak(
  uint32_t rate,
  uint32_t capacity,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix,
  uint32_t outputByteLen,
  uint8_t *output
);


#define __Hacl_Impl_SHA3_H_DEFINED
#endif
