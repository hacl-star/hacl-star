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


#ifndef __Hacl_Hash_Blake2s_H
#define __Hacl_Hash_Blake2s_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Streaming_Types.h"
#include "Hacl_Hash_Blake2b.h"

/* SNIPPET_START: K____uint32_t___uint32_t_ */

typedef struct K____uint32_t___uint32_t__s
{
  uint32_t *fst;
  uint32_t *snd;
}
K____uint32_t___uint32_t_;

/* SNIPPET_END: K____uint32_t___uint32_t_ */

/* SNIPPET_START: Hacl_Hash_Blake2s_block_state_t */

typedef struct Hacl_Hash_Blake2s_block_state_t_s
{
  uint8_t fst;
  uint8_t snd;
  K____uint32_t___uint32_t_ thd;
}
Hacl_Hash_Blake2s_block_state_t;

/* SNIPPET_END: Hacl_Hash_Blake2s_block_state_t */

/* SNIPPET_START: Hacl_Hash_Blake2s_state_t */

typedef struct Hacl_Hash_Blake2s_state_t_s
{
  Hacl_Hash_Blake2s_block_state_t block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Hash_Blake2s_state_t;

/* SNIPPET_END: Hacl_Hash_Blake2s_state_t */

/* SNIPPET_START: Hacl_Hash_Blake2s_malloc_with_params_and_key */

/**
 State allocation function when there are parameters and a key. The
length of the key k MUST match the value of the field key_length in the
parameters. Furthermore, there is a static (not dynamically checked) requirement
that key_length does not exceed max_key (32 for S, 64 for B).)
*/
Hacl_Hash_Blake2s_state_t
*Hacl_Hash_Blake2s_malloc_with_params_and_key(Hacl_Hash_Blake2b_blake2_params *p, uint8_t *k);

/* SNIPPET_END: Hacl_Hash_Blake2s_malloc_with_params_and_key */

/* SNIPPET_START: Hacl_Hash_Blake2s_malloc_with_key */

/**
 State allocation function when there is just a custom key. All
other parameters are set to their respective default values, meaning the output
length is the maximum allowed output (32 for S, 64 for B).
*/
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_malloc_with_key(uint8_t *k, uint8_t kk);

/* SNIPPET_END: Hacl_Hash_Blake2s_malloc_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2s_malloc */

/**
  State allocation function when there is no key
*/
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_malloc(void);

/* SNIPPET_END: Hacl_Hash_Blake2s_malloc */

/* SNIPPET_START: Hacl_Hash_Blake2s_reset_with_key_and_params */

/**
 Re-initialization function. The reinitialization API is tricky --
you MUST reuse the same original parameters for digest (output) length and key
length.
*/
void
Hacl_Hash_Blake2s_reset_with_key_and_params(
  Hacl_Hash_Blake2s_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
);

/* SNIPPET_END: Hacl_Hash_Blake2s_reset_with_key_and_params */

/* SNIPPET_START: Hacl_Hash_Blake2s_reset_with_key */

/**
 Re-initialization function when there is a key. Note that the key
size is not allowed to change, which is why this function does not take a key
length -- the key has to be same key size that was originally passed to
`malloc_with_key`
*/
void Hacl_Hash_Blake2s_reset_with_key(Hacl_Hash_Blake2s_state_t *s, uint8_t *k);

/* SNIPPET_END: Hacl_Hash_Blake2s_reset_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2s_reset */

/**
  Re-initialization function when there is no key
*/
void Hacl_Hash_Blake2s_reset(Hacl_Hash_Blake2s_state_t *s);

/* SNIPPET_END: Hacl_Hash_Blake2s_reset */

/* SNIPPET_START: Hacl_Hash_Blake2s_update */

/**
  Update function when there is no key; 0 = success, 1 = max length exceeded
*/
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2s_update(Hacl_Hash_Blake2s_state_t *state, uint8_t *chunk, uint32_t chunk_len);

/* SNIPPET_END: Hacl_Hash_Blake2s_update */

/* SNIPPET_START: Hacl_Hash_Blake2s_digest */

/**
  Finish function when there is no key
*/
void Hacl_Hash_Blake2s_digest(Hacl_Hash_Blake2s_state_t *state, uint8_t *output);

/* SNIPPET_END: Hacl_Hash_Blake2s_digest */

/* SNIPPET_START: Hacl_Hash_Blake2s_free */

/**
  Free state function when there is no key
*/
void Hacl_Hash_Blake2s_free(Hacl_Hash_Blake2s_state_t *state);

/* SNIPPET_END: Hacl_Hash_Blake2s_free */

/* SNIPPET_START: Hacl_Hash_Blake2s_copy */

/**
  Copying. The key length (or absence thereof) must match between source and destination.
*/
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_copy(Hacl_Hash_Blake2s_state_t *state);

/* SNIPPET_END: Hacl_Hash_Blake2s_copy */

/* SNIPPET_START: Hacl_Hash_Blake2s_hash_with_key */

/**
Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0.
*/
void
Hacl_Hash_Blake2s_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);

/* SNIPPET_END: Hacl_Hash_Blake2s_hash_with_key */

/* SNIPPET_START: Hacl_Hash_Blake2s_hash_with_key_and_paramas */

void
Hacl_Hash_Blake2s_hash_with_key_and_paramas(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
);

/* SNIPPET_END: Hacl_Hash_Blake2s_hash_with_key_and_paramas */

#if defined(__cplusplus)
}
#endif

#define __Hacl_Hash_Blake2s_H_DEFINED
#endif
