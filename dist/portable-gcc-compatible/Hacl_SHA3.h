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

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Lib_Memzero0.h"
#include "Hacl_Krmllib.h"

/* SNIPPET_START: Hacl_Impl_SHA3_keccak_rotc */

extern const uint32_t Hacl_Impl_SHA3_keccak_rotc[24U];

/* SNIPPET_END: Hacl_Impl_SHA3_keccak_rotc */

/* SNIPPET_START: Hacl_Impl_SHA3_keccak_piln */

extern const uint32_t Hacl_Impl_SHA3_keccak_piln[24U];

/* SNIPPET_END: Hacl_Impl_SHA3_keccak_piln */

/* SNIPPET_START: Hacl_Impl_SHA3_keccak_rndc */

extern const uint64_t Hacl_Impl_SHA3_keccak_rndc[24U];

/* SNIPPET_END: Hacl_Impl_SHA3_keccak_rndc */

/* SNIPPET_START: Hacl_Impl_SHA3_rotl */

uint64_t Hacl_Impl_SHA3_rotl(uint64_t a, uint32_t b);

/* SNIPPET_END: Hacl_Impl_SHA3_rotl */

/* SNIPPET_START: Hacl_Impl_SHA3_state_permute */

void Hacl_Impl_SHA3_state_permute(uint64_t *s);

/* SNIPPET_END: Hacl_Impl_SHA3_state_permute */

/* SNIPPET_START: Hacl_Impl_SHA3_loadState */

void Hacl_Impl_SHA3_loadState(uint32_t rateInBytes, uint8_t *input, uint64_t *s);

/* SNIPPET_END: Hacl_Impl_SHA3_loadState */

/* SNIPPET_START: Hacl_Impl_SHA3_storeState */

void Hacl_Impl_SHA3_storeState(uint32_t rateInBytes, uint64_t *s, uint8_t *res);

/* SNIPPET_END: Hacl_Impl_SHA3_storeState */

/* SNIPPET_START: Hacl_Impl_SHA3_absorb */

void
Hacl_Impl_SHA3_absorb(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t inputByteLen,
  uint8_t *input,
  uint8_t delimitedSuffix
);

/* SNIPPET_END: Hacl_Impl_SHA3_absorb */

/* SNIPPET_START: Hacl_Impl_SHA3_squeeze */

void
Hacl_Impl_SHA3_squeeze(
  uint64_t *s,
  uint32_t rateInBytes,
  uint32_t outputByteLen,
  uint8_t *output
);

/* SNIPPET_END: Hacl_Impl_SHA3_squeeze */

/* SNIPPET_START: Hacl_Impl_SHA3_keccak */

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

/* SNIPPET_END: Hacl_Impl_SHA3_keccak */

/* SNIPPET_START: Hacl_SHA3_shake128_hacl */

void
Hacl_SHA3_shake128_hacl(
  uint32_t inputByteLen,
  uint8_t *input,
  uint32_t outputByteLen,
  uint8_t *output
);

/* SNIPPET_END: Hacl_SHA3_shake128_hacl */

/* SNIPPET_START: Hacl_SHA3_shake256_hacl */

void
Hacl_SHA3_shake256_hacl(
  uint32_t inputByteLen,
  uint8_t *input,
  uint32_t outputByteLen,
  uint8_t *output
);

/* SNIPPET_END: Hacl_SHA3_shake256_hacl */

/* SNIPPET_START: Hacl_SHA3_sha3_224 */

void Hacl_SHA3_sha3_224(uint32_t inputByteLen, uint8_t *input, uint8_t *output);

/* SNIPPET_END: Hacl_SHA3_sha3_224 */

/* SNIPPET_START: Hacl_SHA3_sha3_256 */

void Hacl_SHA3_sha3_256(uint32_t inputByteLen, uint8_t *input, uint8_t *output);

/* SNIPPET_END: Hacl_SHA3_sha3_256 */

/* SNIPPET_START: Hacl_SHA3_sha3_384 */

void Hacl_SHA3_sha3_384(uint32_t inputByteLen, uint8_t *input, uint8_t *output);

/* SNIPPET_END: Hacl_SHA3_sha3_384 */

/* SNIPPET_START: Hacl_SHA3_sha3_512 */

void Hacl_SHA3_sha3_512(uint32_t inputByteLen, uint8_t *input, uint8_t *output);

/* SNIPPET_END: Hacl_SHA3_sha3_512 */

#if defined(__cplusplus)
}
#endif

#define __Hacl_SHA3_H_DEFINED
#endif
