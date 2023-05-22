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


#ifndef __internal_Hacl_Streaming_SHA2_H
#define __internal_Hacl_Streaming_SHA2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_SHA2_Generic.h"
#include "internal/Hacl_Krmllib.h"
#include "../Hacl_Streaming_SHA2.h"

void Hacl_SHA2_Scalar32_sha256_init(uint32_t *hash);

void Hacl_SHA2_Scalar32_sha256_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st);

void
Hacl_SHA2_Scalar32_sha256_update_last(
  uint64_t totlen,
  uint32_t len,
  uint8_t *b,
  uint32_t *hash
);

void Hacl_SHA2_Scalar32_sha256_finish(uint32_t *st, uint8_t *h);

void Hacl_SHA2_Scalar32_sha224_init(uint32_t *hash);

void Hacl_SHA2_Scalar32_sha224_finish(uint32_t *st, uint8_t *h);

void Hacl_SHA2_Scalar32_sha512_init(uint64_t *hash);

void Hacl_SHA2_Scalar32_sha512_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st);

void
Hacl_SHA2_Scalar32_sha512_update_last(
  FStar_UInt128_uint128 totlen,
  uint32_t len,
  uint8_t *b,
  uint64_t *hash
);

void Hacl_SHA2_Scalar32_sha512_finish(uint64_t *st, uint8_t *h);

void Hacl_SHA2_Scalar32_sha384_init(uint64_t *hash);

void Hacl_SHA2_Scalar32_sha384_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st);

void
Hacl_SHA2_Scalar32_sha384_update_last(
  FStar_UInt128_uint128 totlen,
  uint32_t len,
  uint8_t *b,
  uint64_t *st
);

void Hacl_SHA2_Scalar32_sha384_finish(uint64_t *st, uint8_t *h);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Streaming_SHA2_H_DEFINED
#endif
