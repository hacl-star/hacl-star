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


#ifndef __EverCrypt_Hash_H
#define __EverCrypt_Hash_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Streaming_Types.h"
#include "EverCrypt_Error.h"

/* SNIPPET_START: EverCrypt_Hash_state_s */

typedef struct EverCrypt_Hash_state_s_s EverCrypt_Hash_state_s;

/* SNIPPET_END: EverCrypt_Hash_state_s */

/* SNIPPET_START: EverCrypt_Hash_Incremental_hash_len */

uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_Incremental_hash_len */

/* SNIPPET_START: EverCrypt_Hash_Incremental_state_t */

typedef struct EverCrypt_Hash_Incremental_state_t_s
{
  EverCrypt_Hash_state_s *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
EverCrypt_Hash_Incremental_state_t;

/* SNIPPET_END: EverCrypt_Hash_Incremental_state_t */

/* SNIPPET_START: EverCrypt_Hash_Incremental_malloc */

/**
Allocate initial state for the agile hash. The argument `a` stands for the
choice of algorithm (see Hacl_Spec.h). This API will automatically pick the most
efficient implementation, provided you have called EverCrypt_AutoConfig2_init()
before. The state is to be freed by calling `free`.
*/
EverCrypt_Hash_Incremental_state_t
*EverCrypt_Hash_Incremental_malloc(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_Hash_Incremental_malloc */

/* SNIPPET_START: EverCrypt_Hash_Incremental_reset */

/**
Reset an existing state to the initial hash state with empty data.
*/
void EverCrypt_Hash_Incremental_reset(EverCrypt_Hash_Incremental_state_t *state);

/* SNIPPET_END: EverCrypt_Hash_Incremental_reset */

/* SNIPPET_START: EverCrypt_Hash_Incremental_update */

/**
Feed an arbitrary amount of data into the hash. This function returns
EverCrypt_Error_Success for success, or EverCrypt_Error_MaximumLengthExceeded if
the combined length of all of the data passed to `update` (since the last call
to `init`) exceeds 2^61-1 bytes or 2^64-1 bytes, depending on the choice of
algorithm. Both limits are unlikely to be attained in practice.
*/
EverCrypt_Error_error_code
EverCrypt_Hash_Incremental_update(
  EverCrypt_Hash_Incremental_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_update */

/* SNIPPET_START: EverCrypt_Hash_Incremental_alg_of_state */

/**
Perform a run-time test to determine which algorithm was chosen for the given piece of state.
*/
Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_state_t *s);

/* SNIPPET_END: EverCrypt_Hash_Incremental_alg_of_state */

/* SNIPPET_START: EverCrypt_Hash_Incremental_digest */

/**
Write the resulting hash into `output`, an array whose length is
algorithm-specific. You can use the macros defined earlier in this file to
allocate a destination buffer of the right length. The state remains valid after
a call to `digest`, meaning the user may feed more data into the hash via
`update`. (The finish function operates on an internal copy of the state and
therefore does not invalidate the client-held state.)
*/
void
EverCrypt_Hash_Incremental_digest(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output);

/* SNIPPET_END: EverCrypt_Hash_Incremental_digest */

/* SNIPPET_START: EverCrypt_Hash_Incremental_free */

/**
Free a state previously allocated with `create_in`.
*/
void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_state_t *state);

/* SNIPPET_END: EverCrypt_Hash_Incremental_free */

/* SNIPPET_START: EverCrypt_Hash_Incremental_hash */

/**
Hash `input`, of len `input_len`, into `output`, an array whose length is determined by
your choice of algorithm `a` (see Hacl_Spec.h). You can use the macros defined
earlier in this file to allocate a destination buffer of the right length. This
API will automatically pick the most efficient implementation, provided you have
called EverCrypt_AutoConfig2_init() before. 
*/
void
EverCrypt_Hash_Incremental_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len
);

/* SNIPPET_END: EverCrypt_Hash_Incremental_hash */

/* SNIPPET_START: MD5_HASH_LEN */

#define MD5_HASH_LEN (16U)

/* SNIPPET_END: MD5_HASH_LEN */

/* SNIPPET_START: SHA1_HASH_LEN */

#define SHA1_HASH_LEN (20U)

/* SNIPPET_END: SHA1_HASH_LEN */

/* SNIPPET_START: SHA2_224_HASH_LEN */

#define SHA2_224_HASH_LEN (28U)

/* SNIPPET_END: SHA2_224_HASH_LEN */

/* SNIPPET_START: SHA2_256_HASH_LEN */

#define SHA2_256_HASH_LEN (32U)

/* SNIPPET_END: SHA2_256_HASH_LEN */

/* SNIPPET_START: SHA2_384_HASH_LEN */

#define SHA2_384_HASH_LEN (48U)

/* SNIPPET_END: SHA2_384_HASH_LEN */

/* SNIPPET_START: SHA2_512_HASH_LEN */

#define SHA2_512_HASH_LEN (64U)

/* SNIPPET_END: SHA2_512_HASH_LEN */

/* SNIPPET_START: SHA3_224_HASH_LEN */

#define SHA3_224_HASH_LEN (28U)

/* SNIPPET_END: SHA3_224_HASH_LEN */

/* SNIPPET_START: SHA3_256_HASH_LEN */

#define SHA3_256_HASH_LEN (32U)

/* SNIPPET_END: SHA3_256_HASH_LEN */

/* SNIPPET_START: SHA3_384_HASH_LEN */

#define SHA3_384_HASH_LEN (48U)

/* SNIPPET_END: SHA3_384_HASH_LEN */

/* SNIPPET_START: SHA3_512_HASH_LEN */

#define SHA3_512_HASH_LEN (64U)

/* SNIPPET_END: SHA3_512_HASH_LEN */

/* SNIPPET_START: BLAKE2S_HASH_LEN */

#define BLAKE2S_HASH_LEN (32U)

/* SNIPPET_END: BLAKE2S_HASH_LEN */

/* SNIPPET_START: BLAKE2B_HASH_LEN */

#define BLAKE2B_HASH_LEN (64U)

/* SNIPPET_END: BLAKE2B_HASH_LEN */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_Hash_H_DEFINED
#endif
