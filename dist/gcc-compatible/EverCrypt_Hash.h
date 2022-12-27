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


#ifndef __EverCrypt_Hash_H
#define __EverCrypt_Hash_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Lib_Memzero0.h"
#include "Hacl_Spec.h"
#include "Hacl_SHA3.h"
#include "Hacl_Krmllib.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Hash_SHA1.h"
#include "Hacl_Hash_MD5.h"
#include "Hacl_Hash_Blake2s_128.h"
#include "Hacl_Hash_Blake2b_256.h"
#include "Hacl_Hash_Blake2.h"
#include "EverCrypt_Error.h"
#include "EverCrypt_AutoConfig2.h"

typedef struct EverCrypt_Hash_state_s_s EverCrypt_Hash_state_s;

uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a);

typedef struct EverCrypt_Hash_Incremental_hash_state_s
{
  EverCrypt_Hash_state_s *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
EverCrypt_Hash_Incremental_hash_state;

EverCrypt_Hash_Incremental_hash_state
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a);

void EverCrypt_Hash_Incremental_init(EverCrypt_Hash_Incremental_hash_state *s);

EverCrypt_Error_error_code
EverCrypt_Hash_Incremental_update(
  EverCrypt_Hash_Incremental_hash_state *s,
  uint8_t *data,
  uint32_t len
);

Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_hash_state *s);

void EverCrypt_Hash_Incremental_finish(EverCrypt_Hash_Incremental_hash_state *s, uint8_t *dst);

void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_hash_state *s);

void
EverCrypt_Hash_Incremental_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t *input,
  uint32_t len
);

#define MD5_HASH_LEN ((uint32_t)16U)

#define SHA1_HASH_LEN ((uint32_t)20U)

#define SHA2_224_HASH_LEN ((uint32_t)28U)

#define SHA2_256_HASH_LEN ((uint32_t)32U)

#define SHA2_384_HASH_LEN ((uint32_t)48U)

#define SHA2_512_HASH_LEN ((uint32_t)64U)

#define SHA3_256_HASH_LEN ((uint32_t)32U)

#define BLAKE2S_HASH_LEN ((uint32_t)32U)

#define BLAKE2B_HASH_LEN ((uint32_t)64U)

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Hash_H_DEFINED
#endif
