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


#ifndef __EverCrypt_DRBG_H
#define __EverCrypt_DRBG_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Lib_RandomBuffer_System.h"
#include "Hacl_Streaming_Types.h"
#include "Hacl_HMAC_DRBG.h"

typedef Spec_Hash_Definitions_hash_alg EverCrypt_DRBG_supported_alg;

extern uint32_t EverCrypt_DRBG_reseed_interval;

extern uint32_t EverCrypt_DRBG_max_output_length;

extern uint32_t EverCrypt_DRBG_max_length;

extern uint32_t EverCrypt_DRBG_max_personalization_string_length;

extern uint32_t EverCrypt_DRBG_max_additional_input_length;

uint32_t EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a);

typedef struct EverCrypt_DRBG_state_s_s EverCrypt_DRBG_state_s;

bool
EverCrypt_DRBG_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

bool
EverCrypt_DRBG_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

bool
EverCrypt_DRBG_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

bool
EverCrypt_DRBG_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create_in(Spec_Hash_Definitions_hash_alg a);

/**
Create a DRBG state.

@param a Hash algorithm to use. The possible instantiations are ...
  * `Spec_Hash_Definitions_SHA2_256`,
  * `Spec_Hash_Definitions_SHA2_384`,
  * `Spec_Hash_Definitions_SHA2_512`, and
  * `Spec_Hash_Definitions_SHA1`.

@return DRBG state. Needs to be freed via `EverCrypt_DRBG_uninstantiate`.
*/
EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a);

/**
Instantiate the DRBG.

@param st Pointer to DRBG state.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from.
@param personalization_string_len Length of personalization string.

@return True if and only if instantiation was successful.
*/
bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

/**
Reseed the DRBG.

@param st Pointer to DRBG state.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
@param additional_input_input_len Length of additional input.

@return True if and only if reseed was successful.
*/
bool
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/**
Generate output.

@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
@param additional_input_input_len Length of additional input.

@return True if and only if generate was successful.
*/
bool
EverCrypt_DRBG_generate(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/**
Uninstantiate and free the DRBG.

@param st Pointer to DRBG state.
*/
void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_DRBG_H_DEFINED
#endif
