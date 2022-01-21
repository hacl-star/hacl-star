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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "../Hacl_Hash_Blake2.h"

void Hacl_Hash_Core_Blake2_finish_blake2s_32(u32 *s, u64 ev, u8 *dst);

void Hacl_Hash_Core_Blake2_finish_blake2b_32(u64 *s, uint128_t ev, u8 *dst);

u64 Hacl_Hash_Blake2_update_multi_blake2s_32(u32 *s, u64 ev, u8 *blocks, u32 n_blocks);

uint128_t
Hacl_Hash_Blake2_update_multi_blake2b_32(u64 *s, uint128_t ev, u8 *blocks, u32 n_blocks);

typedef struct K___u32_u32_u32__u8___u8__s
{
  u32 fst;
  u32 snd;
  u32 thd;
  u8 *f3;
  u8 *f4;
}
K___u32_u32_u32__u8___u8_;

typedef struct K___u32_u32_u32_s
{
  u32 fst;
  u32 snd;
  u32 thd;
}
K___u32_u32_u32;

u64
Hacl_Hash_Blake2_update_last_blake2s_32(u32 *s, u64 ev, u64 prev_len, u8 *input, u32 input_len);

uint128_t
Hacl_Hash_Blake2_update_last_blake2b_32(
  u64 *s,
  uint128_t ev,
  uint128_t prev_len,
  u8 *input,
  u32 input_len
);

void Hacl_Hash_Blake2_hash_blake2s_32(u8 *input, u32 input_len, u8 *dst);

void Hacl_Hash_Blake2_hash_blake2b_32(u8 *input, u32 input_len, u8 *dst);

typedef struct K___u32_u32_s
{
  u32 fst;
  u32 snd;
}
K___u32_u32;

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_Hash_Blake2_H_DEFINED
#endif
