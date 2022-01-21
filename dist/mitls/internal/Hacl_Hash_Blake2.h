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


#ifndef __internal_Hacl_Hash_Blake2_H
#define __internal_Hacl_Hash_Blake2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "internal/Hacl_Kremlib.h"
#include "../Hacl_Hash_Blake2.h"

uint64_t Hacl_Hash_Core_Blake2_update_blake2s_32(uint32_t *s, uint64_t totlen, uint8_t *block);

void Hacl_Hash_Core_Blake2_finish_blake2s_32(uint32_t *s, uint64_t ev, uint8_t *dst);

FStar_UInt128_uint128
Hacl_Hash_Core_Blake2_update_blake2b_32(
  uint64_t *s,
  FStar_UInt128_uint128 totlen,
  uint8_t *block
);

void
Hacl_Hash_Core_Blake2_finish_blake2b_32(uint64_t *s, FStar_UInt128_uint128 ev, uint8_t *dst);

uint64_t
Hacl_Hash_Blake2_update_multi_blake2s_32(
  uint32_t *s,
  uint64_t ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

FStar_UInt128_uint128
Hacl_Hash_Blake2_update_multi_blake2b_32(
  uint64_t *s,
  FStar_UInt128_uint128 ev,
  uint8_t *blocks,
  uint32_t n_blocks
);

typedef struct K___uint32_t_uint32_t_uint32_t__uint8_t___uint8_t__s
{
  uint32_t fst;
  uint32_t snd;
  uint32_t thd;
  uint8_t *f3;
  uint8_t *f4;
}
K___uint32_t_uint32_t_uint32_t__uint8_t___uint8_t_;

typedef struct K___uint32_t_uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
  uint32_t thd;
}
K___uint32_t_uint32_t_uint32_t;

uint64_t
Hacl_Hash_Blake2_update_last_blake2s_32(
  uint32_t *s,
  uint64_t ev,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

FStar_UInt128_uint128
Hacl_Hash_Blake2_update_last_blake2b_32(
  uint64_t *s,
  FStar_UInt128_uint128 ev,
  FStar_UInt128_uint128 prev_len,
  uint8_t *input,
  uint32_t input_len
);

void Hacl_Hash_Blake2_hash_blake2s_32(uint8_t *input, uint32_t input_len, uint8_t *dst);

void Hacl_Hash_Blake2_hash_blake2b_32(uint8_t *input, uint32_t input_len, uint8_t *dst);

typedef struct K___uint32_t_uint32_t_s
{
  uint32_t fst;
  uint32_t snd;
}
K___uint32_t_uint32_t;

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Hash_Blake2_H_DEFINED
#endif
