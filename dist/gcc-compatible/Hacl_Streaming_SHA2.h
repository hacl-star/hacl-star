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


#ifndef __Hacl_Streaming_SHA2_H
#define __Hacl_Streaming_SHA2_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_SHA2_Generic.h"
#include "Hacl_Krmllib.h"

typedef struct Hacl_Streaming_SHA2_state_sha2_224_s
{
  uint32_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_SHA2_state_sha2_224;

typedef Hacl_Streaming_SHA2_state_sha2_224 Hacl_Streaming_SHA2_state_sha2_256;

typedef struct Hacl_Streaming_SHA2_state_sha2_384_s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_SHA2_state_sha2_384;

typedef Hacl_Streaming_SHA2_state_sha2_384 Hacl_Streaming_SHA2_state_sha2_512;

/**
Allocate initial state for the SHA2_256 hash. The state is to be freed by
calling `free_256`.
*/
Hacl_Streaming_SHA2_state_sha2_224 *Hacl_Streaming_SHA2_create_in_256();

/**
Reset an existing state to the initial hash state with empty data.
*/
void Hacl_Streaming_SHA2_init_256(Hacl_Streaming_SHA2_state_sha2_224 *s);

/**
Feed an arbitrary amount of data into the hash. This function returns 0 for
success, or 1 if the combined length of all of the data passed to `update_256`
(since the last call to `init_256`) exceeds 2^61-1 bytes.

This function is identical to the update function for SHA2_224.
*/
uint32_t
Hacl_Streaming_SHA2_update_256(
  Hacl_Streaming_SHA2_state_sha2_224 *p,
  uint8_t *input,
  uint32_t input_len
);

/**
Write the resulting hash into `dst`, an array of 32 bytes. The state remains
valid after a call to `finish_256`, meaning the user may feed more data into
the hash via `update_256`. (The finish_256 function operates on an internal copy of
the state and therefore does not invalidate the client-held state `p`.)
*/
void Hacl_Streaming_SHA2_finish_256(Hacl_Streaming_SHA2_state_sha2_224 *p, uint8_t *dst);

/**
Free a state allocated with `create_in_256`.

This function is identical to the free function for SHA2_224.
*/
void Hacl_Streaming_SHA2_free_256(Hacl_Streaming_SHA2_state_sha2_224 *s);

/**
Hash `input`, of len `input_len`, into `dst`, an array of 32 bytes.
*/
void Hacl_Streaming_SHA2_sha256(uint8_t *dst, uint32_t input_len, uint8_t *input);

Hacl_Streaming_SHA2_state_sha2_224 *Hacl_Streaming_SHA2_create_in_224();

void Hacl_Streaming_SHA2_init_224(Hacl_Streaming_SHA2_state_sha2_224 *s);

uint32_t
Hacl_Streaming_SHA2_update_224(
  Hacl_Streaming_SHA2_state_sha2_224 *p,
  uint8_t *input,
  uint32_t input_len
);

/**
Write the resulting hash into `dst`, an array of 28 bytes. The state remains
valid after a call to `finish_224`, meaning the user may feed more data into
the hash via `update_224`.
*/
void Hacl_Streaming_SHA2_finish_224(Hacl_Streaming_SHA2_state_sha2_224 *p, uint8_t *dst);

void Hacl_Streaming_SHA2_free_224(Hacl_Streaming_SHA2_state_sha2_224 *p);

/**
Hash `input`, of len `input_len`, into `dst`, an array of 28 bytes.
*/
void Hacl_Streaming_SHA2_sha224(uint8_t *dst, uint32_t input_len, uint8_t *input);

Hacl_Streaming_SHA2_state_sha2_384 *Hacl_Streaming_SHA2_create_in_512();

void Hacl_Streaming_SHA2_init_512(Hacl_Streaming_SHA2_state_sha2_384 *s);

/**
Feed an arbitrary amount of data into the hash. This function returns 0 for
success, or 1 if the combined length of all of the data passed to `update_512`
(since the last call to `init_512`) exceeds 2^125-1 bytes.

This function is identical to the update function for SHA2_384.
*/
uint32_t
Hacl_Streaming_SHA2_update_512(
  Hacl_Streaming_SHA2_state_sha2_384 *p,
  uint8_t *input,
  uint32_t input_len
);

/**
Write the resulting hash into `dst`, an array of 64 bytes. The state remains
valid after a call to `finish_512`, meaning the user may feed more data into
the hash via `update_512`. (The finish_512 function operates on an internal copy of
the state and therefore does not invalidate the client-held state `p`.)
*/
void Hacl_Streaming_SHA2_finish_512(Hacl_Streaming_SHA2_state_sha2_384 *p, uint8_t *dst);

/**
Free a state allocated with `create_in_512`.

This function is identical to the free function for SHA2_384.
*/
void Hacl_Streaming_SHA2_free_512(Hacl_Streaming_SHA2_state_sha2_384 *s);

/**
Hash `input`, of len `input_len`, into `dst`, an array of 64 bytes.
*/
void Hacl_Streaming_SHA2_sha512(uint8_t *dst, uint32_t input_len, uint8_t *input);

Hacl_Streaming_SHA2_state_sha2_384 *Hacl_Streaming_SHA2_create_in_384();

void Hacl_Streaming_SHA2_init_384(Hacl_Streaming_SHA2_state_sha2_384 *s);

uint32_t
Hacl_Streaming_SHA2_update_384(
  Hacl_Streaming_SHA2_state_sha2_384 *p,
  uint8_t *input,
  uint32_t input_len
);

/**
Write the resulting hash into `dst`, an array of 48 bytes. The state remains
valid after a call to `finish_384`, meaning the user may feed more data into
the hash via `update_384`.
*/
void Hacl_Streaming_SHA2_finish_384(Hacl_Streaming_SHA2_state_sha2_384 *p, uint8_t *dst);

void Hacl_Streaming_SHA2_free_384(Hacl_Streaming_SHA2_state_sha2_384 *p);

/**
Hash `input`, of len `input_len`, into `dst`, an array of 48 bytes.
*/
void Hacl_Streaming_SHA2_sha384(uint8_t *dst, uint32_t input_len, uint8_t *input);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Streaming_SHA2_H_DEFINED
#endif
