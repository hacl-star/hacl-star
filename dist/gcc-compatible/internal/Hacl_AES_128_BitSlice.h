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


#ifndef __internal_Hacl_AES_128_BitSlice_H
#define __internal_Hacl_AES_128_BitSlice_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_Lib.h"
#include "../Hacl_AES_128_BitSlice.h"

void Hacl_Impl_AES_CoreBitSlice_store_block0(uint8_t *out, uint64_t *inp);

void Hacl_Impl_AES_CoreBitSlice_load_key1(uint64_t *out, uint8_t *k);

void Hacl_Impl_AES_CoreBitSlice_load_nonce(uint64_t *out, uint8_t *nonce1);

void Hacl_Impl_AES_CoreBitSlice_load_state(uint64_t *out, uint64_t *nonce1, uint32_t counter);

void Hacl_Impl_AES_CoreBitSlice_xor_state_key1(uint64_t *st, uint64_t *ost);

void Hacl_Impl_AES_CoreBitSlice_aes_enc(uint64_t *st, uint64_t *key);

void Hacl_Impl_AES_CoreBitSlice_aes_enc_last(uint64_t *st, uint64_t *key);

void
Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist(uint64_t *next, uint64_t *prev, uint8_t rcon1);

void Hacl_Impl_AES_CoreBitSlice_key_expansion_step(uint64_t *next, uint64_t *prev);

void
Hacl_Impl_AES_Generic_aes128_ctr_bitslice(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t counter
);

void
Hacl_Impl_AES_Generic_aes256_ctr_bitslice(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t counter
);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_AES_128_BitSlice_H_DEFINED
#endif
