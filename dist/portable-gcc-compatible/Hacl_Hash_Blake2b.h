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


#ifndef __Hacl_Hash_Blake2b_H
#define __Hacl_Hash_Blake2b_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Streaming_Types.h"
#include "Hacl_Krmllib.h"

/* SNIPPET_START: Hacl_Hash_Blake2b_blake2_params */

typedef struct Hacl_Hash_Blake2b_blake2_params_s
{
  uint8_t digest_length;
  uint8_t key_length;
  uint8_t fanout;
  uint8_t depth;
  uint32_t leaf_length;
  uint64_t node_offset;
  uint8_t node_depth;
  uint8_t inner_length;
  uint8_t *salt;
  uint8_t *personal;
}
Hacl_Hash_Blake2b_blake2_params;

/* SNIPPET_END: Hacl_Hash_Blake2b_blake2_params */

/* SNIPPET_START: K____uint64_t___uint64_t_ */

typedef struct K____uint64_t___uint64_t__s
{
  uint64_t *fst;
  uint64_t *snd;
}
K____uint64_t___uint64_t_;

/* SNIPPET_END: K____uint64_t___uint64_t_ */

/* SNIPPET_START: Hacl_Hash_Blake2b_block_state_t */

typedef struct Hacl_Hash_Blake2b_block_state_t_s
{
  uint8_t fst;
  uint8_t snd;
  K____uint64_t___uint64_t_ thd;
}
Hacl_Hash_Blake2b_block_state_t;

/* SNIPPET_END: Hacl_Hash_Blake2b_block_state_t */

/* SNIPPET_START: Hacl_Hash_Blake2b_state_t */

typedef struct Hacl_Hash_Blake2b_state_t_s
{
  Hacl_Hash_Blake2b_block_state_t block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Hash_Blake2b_state_t;

/* SNIPPET_END: Hacl_Hash_Blake2b_state_t */

/* SNIPPET_START: Hacl_Hash_Blake2b_malloc_with_params_and_key */

/**
 General-purpose allocation function that gives control over all
Blake2 parameters, including the key. Further resettings of the state SHALL be
done with `reset_with_params_and_key`, and SHALL feature the exact same values
for the `key_length` and `digest_length` fields as passed here. In other words,
once you commit to a digest and key length, the only way to change these
parameters is to allocate a new object.

The caller must satisfy the following requirements.
- The length of the key k MUST match the value of the field key_length in the
  parameters.
- The key_length must not exceed 32 for S, 64 for B.
- The digest_length must not exceed 32 for S, 64 for B.

*/
Hacl_Hash_Blake2b_state_t
*Hacl_Hash_Blake2b_malloc_with_params_and_key(Hacl_Hash_Blake2b_blake2_params *p, uint8_t *k);

/* SNIPPET_END: Hacl_Hash_Blake2b_malloc_with_params_and_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_malloc_with_key */

/**
 Specialized allocation function that picks default values for all
parameters, except for the key_length. Further resettings of the state SHALL be
done with `reset_with_key`, and SHALL feature the exact same key length `kk` as
passed here. In other words, once you commit to a key length, the only way to
change this parameter is to allocate a new object.

The caller must satisfy the following requirements.
- The key_length must not exceed 32 for S, 64 for B.

*/
Hacl_Hash_Blake2b_state_t *Hacl_Hash_Blake2b_malloc_with_key(uint8_t *k, uint8_t kk);

/* SNIPPET_END: Hacl_Hash_Blake2b_malloc_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_malloc */

/**
 Specialized allocation function that picks default values for all
parameters, and has no key. Effectively, this is what you want if you intend to
use Blake2 as a hash function. Further resettings of the state SHALL be done with `reset`.
*/
Hacl_Hash_Blake2b_state_t *Hacl_Hash_Blake2b_malloc(void);

/* SNIPPET_END: Hacl_Hash_Blake2b_malloc */

/* SNIPPET_START: Hacl_Hash_Blake2b_reset_with_key_and_params */

/**
 General-purpose re-initialization function with parameters and
key. You cannot change digest_length or key_length, meaning those values in
the parameters object must be the same as originally decided via one of the
malloc functions. All other values of the parameter can be changed. The behavior
is unspecified if you violate this precondition.
*/
void
Hacl_Hash_Blake2b_reset_with_key_and_params(
  Hacl_Hash_Blake2b_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Hash_Blake2b_reset_with_key_and_params */

/* SNIPPET_START: Hacl_Hash_Blake2b_reset_with_key */

/**
 Specialized-purpose re-initialization function with no parameters,
and a key. The key length must be the same as originally decided via your choice
of malloc function. All other parameters are reset to their default values. The
original call to malloc MUST have set digest_length to the default value. The
behavior is unspecified if you violate this precondition.
*/
void Hacl_Hash_Blake2b_reset_with_key(Hacl_Hash_Blake2b_state_t *s, uint8_t *k);

/* SNIPPET_END: Hacl_Hash_Blake2b_reset_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_reset */

/**
 Specialized-purpose re-initialization function with no parameters
and no key. This is what you want if you intend to use Blake2 as a hash
function. The key length and digest length must have been set to their
respective default values via your choice of malloc function (always true if you
used `malloc`). All other parameters are reset to their default values. The
behavior is unspecified if you violate this precondition.
*/
void Hacl_Hash_Blake2b_reset(Hacl_Hash_Blake2b_state_t *s);

/* SNIPPET_END: Hacl_Hash_Blake2b_reset */

/* SNIPPET_START: Hacl_Hash_Blake2b_update */

/**
  Update function; 0 = success, 1 = max length exceeded
*/
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2b_update(Hacl_Hash_Blake2b_state_t *state, uint8_t *chunk, uint32_t chunk_len);

/* SNIPPET_END: Hacl_Hash_Blake2b_update */

/* SNIPPET_START: Hacl_Hash_Blake2b_digest */

/**
 Digest function. This function expects the `output` array to hold
at least `digest_length` bytes, where `digest_length` was determined by your
choice of `malloc` function. Concretely, if you used `malloc` or
`malloc_with_key`, then the expected length is 32 for S, or 64 for B (default
digest length). If you used `malloc_with_params_and_key`, then the expected
length is whatever you chose for the `digest_length` field of your
parameters.
*/
void Hacl_Hash_Blake2b_digest(Hacl_Hash_Blake2b_state_t *state, uint8_t *output);

/* SNIPPET_END: Hacl_Hash_Blake2b_digest */

/* SNIPPET_START: Hacl_Hash_Blake2b_free */

/**
  Free state function when there is no key
*/
void Hacl_Hash_Blake2b_free(Hacl_Hash_Blake2b_state_t *state);

/* SNIPPET_END: Hacl_Hash_Blake2b_free */

/* SNIPPET_START: Hacl_Hash_Blake2b_copy */

/**
  Copying. This preserves all parameters.
*/
Hacl_Hash_Blake2b_state_t *Hacl_Hash_Blake2b_copy(Hacl_Hash_Blake2b_state_t *state);

/* SNIPPET_END: Hacl_Hash_Blake2b_copy */

/* SNIPPET_START: Hacl_Hash_Blake2b_hash_with_key */

/**
Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0.
*/
void
Hacl_Hash_Blake2b_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);

/* SNIPPET_END: Hacl_Hash_Blake2b_hash_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2b_hash_with_key_and_paramas */

/**
Write the BLAKE2b digest of message `input` using key `key` and
parameters `params` into `output`. The `key` array must be of length
`params.key_length`. The `output` array must be of length
`params.digest_length`. 
*/
void
Hacl_Hash_Blake2b_hash_with_key_and_paramas(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
);

/* SNIPPET_END: Hacl_Hash_Blake2b_hash_with_key_and_paramas */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_Blake2b_H_DEFINED
#endif
