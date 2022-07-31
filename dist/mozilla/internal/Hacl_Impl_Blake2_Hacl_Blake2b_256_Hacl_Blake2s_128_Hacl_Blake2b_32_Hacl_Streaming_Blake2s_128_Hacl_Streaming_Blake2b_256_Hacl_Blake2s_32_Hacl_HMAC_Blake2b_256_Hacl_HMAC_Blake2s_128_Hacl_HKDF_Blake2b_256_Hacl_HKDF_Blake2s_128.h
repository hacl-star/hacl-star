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


#ifndef __internal_Hacl_Impl_Blake2_Hacl_Blake2b_256_Hacl_Blake2s_128_Hacl_Blake2b_32_Hacl_Streaming_Blake2s_128_Hacl_Streaming_Blake2b_256_Hacl_Blake2s_32_Hacl_HMAC_Blake2b_256_Hacl_HMAC_Blake2s_128_Hacl_HKDF_Blake2b_256_Hacl_HKDF_Blake2s_128_H
#define __internal_Hacl_Impl_Blake2_Hacl_Blake2b_256_Hacl_Blake2s_128_Hacl_Blake2b_32_Hacl_Streaming_Blake2s_128_Hacl_Streaming_Blake2b_256_Hacl_Blake2s_32_Hacl_HMAC_Blake2b_256_Hacl_HMAC_Blake2s_128_Hacl_HKDF_Blake2b_256_Hacl_HKDF_Blake2s_128_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include <stdbool.h>


#include "internal/Hacl_Lib.h"
#include "Hacl_Krmllib.h"

extern const uint32_t Hacl_Impl_Blake2_Constants_sigmaTable[160U];

extern const uint32_t Hacl_Impl_Blake2_Constants_ivTable_S[8U];

extern const uint64_t Hacl_Impl_Blake2_Constants_ivTable_B[8U];

void
Hacl_Blake2b_32_blake2b(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
);

void
Hacl_Blake2s_32_blake2s(
  uint32_t nn,
  uint8_t *output,
  uint32_t ll,
  uint8_t *d,
  uint32_t kk,
  uint8_t *k
);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Impl_Blake2_Hacl_Blake2b_256_Hacl_Blake2s_128_Hacl_Blake2b_32_Hacl_Streaming_Blake2s_128_Hacl_Streaming_Blake2b_256_Hacl_Blake2s_32_Hacl_HMAC_Blake2b_256_Hacl_HMAC_Blake2s_128_Hacl_HKDF_Blake2b_256_Hacl_HKDF_Blake2s_128_H_DEFINED
#endif
