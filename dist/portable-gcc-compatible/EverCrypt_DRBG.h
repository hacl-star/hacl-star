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


#ifndef __EverCrypt_DRBG_H
#define __EverCrypt_DRBG_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "EverCrypt_HMAC.h"
#include "Lib_RandomBuffer_System.h"
#include "Hacl_Spec.h"
#include "Hacl_HMAC_DRBG.h"
#include "Hacl_Lib.h"

/* SNIPPET_START: EverCrypt_DRBG_supported_alg */

typedef Spec_Hash_Definitions_hash_alg EverCrypt_DRBG_supported_alg;

/* SNIPPET_END: EverCrypt_DRBG_supported_alg */

/* SNIPPET_START: EverCrypt_DRBG_reseed_interval */

extern uint32_t EverCrypt_DRBG_reseed_interval;

/* SNIPPET_END: EverCrypt_DRBG_reseed_interval */

/* SNIPPET_START: EverCrypt_DRBG_max_output_length */

extern uint32_t EverCrypt_DRBG_max_output_length;

/* SNIPPET_END: EverCrypt_DRBG_max_output_length */

/* SNIPPET_START: EverCrypt_DRBG_max_length */

extern uint32_t EverCrypt_DRBG_max_length;

/* SNIPPET_END: EverCrypt_DRBG_max_length */

/* SNIPPET_START: EverCrypt_DRBG_max_personalization_string_length */

extern uint32_t EverCrypt_DRBG_max_personalization_string_length;

/* SNIPPET_END: EverCrypt_DRBG_max_personalization_string_length */

/* SNIPPET_START: EverCrypt_DRBG_max_additional_input_length */

extern uint32_t EverCrypt_DRBG_max_additional_input_length;

/* SNIPPET_END: EverCrypt_DRBG_max_additional_input_length */

/* SNIPPET_START: EverCrypt_DRBG_min_length */

uint32_t EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_DRBG_min_length */

/* SNIPPET_START: EverCrypt_DRBG_state_s_tags */

#define EverCrypt_DRBG_SHA1_s 0
#define EverCrypt_DRBG_SHA2_256_s 1
#define EverCrypt_DRBG_SHA2_384_s 2
#define EverCrypt_DRBG_SHA2_512_s 3

/* SNIPPET_END: EverCrypt_DRBG_state_s_tags */

typedef uint8_t EverCrypt_DRBG_state_s_tags;

/* SNIPPET_START: EverCrypt_DRBG_state_s */

typedef struct EverCrypt_DRBG_state_s_s EverCrypt_DRBG_state_s;

/* SNIPPET_END: EverCrypt_DRBG_state_s */

/* SNIPPET_START: EverCrypt_DRBG_uu___is_SHA1_s */

bool
EverCrypt_DRBG_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG_uu___is_SHA1_s */

/* SNIPPET_START: EverCrypt_DRBG___proj__SHA1_s__item___0 */

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA1_s__item___0(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG___proj__SHA1_s__item___0 */

/* SNIPPET_START: EverCrypt_DRBG_uu___is_SHA2_256_s */

bool
EverCrypt_DRBG_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG_uu___is_SHA2_256_s */

/* SNIPPET_START: EverCrypt_DRBG___proj__SHA2_256_s__item___0 */

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_256_s__item___0(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG___proj__SHA2_256_s__item___0 */

/* SNIPPET_START: EverCrypt_DRBG_uu___is_SHA2_384_s */

bool
EverCrypt_DRBG_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG_uu___is_SHA2_384_s */

/* SNIPPET_START: EverCrypt_DRBG___proj__SHA2_384_s__item___0 */

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_384_s__item___0(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG___proj__SHA2_384_s__item___0 */

/* SNIPPET_START: EverCrypt_DRBG_uu___is_SHA2_512_s */

bool
EverCrypt_DRBG_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG_uu___is_SHA2_512_s */

/* SNIPPET_START: EverCrypt_DRBG___proj__SHA2_512_s__item___0 */

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_512_s__item___0(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_DRBG_state_s projectee
);

/* SNIPPET_END: EverCrypt_DRBG___proj__SHA2_512_s__item___0 */

/* SNIPPET_START: EverCrypt_DRBG_create */

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a);

/* SNIPPET_END: EverCrypt_DRBG_create */

/* SNIPPET_START: EverCrypt_DRBG_instantiate_sha1 */

bool
EverCrypt_DRBG_instantiate_sha1(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

/* SNIPPET_END: EverCrypt_DRBG_instantiate_sha1 */

/* SNIPPET_START: EverCrypt_DRBG_instantiate_sha2_256 */

bool
EverCrypt_DRBG_instantiate_sha2_256(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

/* SNIPPET_END: EverCrypt_DRBG_instantiate_sha2_256 */

/* SNIPPET_START: EverCrypt_DRBG_instantiate_sha2_384 */

bool
EverCrypt_DRBG_instantiate_sha2_384(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

/* SNIPPET_END: EverCrypt_DRBG_instantiate_sha2_384 */

/* SNIPPET_START: EverCrypt_DRBG_instantiate_sha2_512 */

bool
EverCrypt_DRBG_instantiate_sha2_512(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

/* SNIPPET_END: EverCrypt_DRBG_instantiate_sha2_512 */

/* SNIPPET_START: EverCrypt_DRBG_reseed_sha1 */

bool
EverCrypt_DRBG_reseed_sha1(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_reseed_sha1 */

/* SNIPPET_START: EverCrypt_DRBG_reseed_sha2_256 */

bool
EverCrypt_DRBG_reseed_sha2_256(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_reseed_sha2_256 */

/* SNIPPET_START: EverCrypt_DRBG_reseed_sha2_384 */

bool
EverCrypt_DRBG_reseed_sha2_384(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_reseed_sha2_384 */

/* SNIPPET_START: EverCrypt_DRBG_reseed_sha2_512 */

bool
EverCrypt_DRBG_reseed_sha2_512(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_reseed_sha2_512 */

/* SNIPPET_START: EverCrypt_DRBG_generate_sha1 */

bool
EverCrypt_DRBG_generate_sha1(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_generate_sha1 */

/* SNIPPET_START: EverCrypt_DRBG_generate_sha2_256 */

bool
EverCrypt_DRBG_generate_sha2_256(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_generate_sha2_256 */

/* SNIPPET_START: EverCrypt_DRBG_generate_sha2_384 */

bool
EverCrypt_DRBG_generate_sha2_384(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_generate_sha2_384 */

/* SNIPPET_START: EverCrypt_DRBG_generate_sha2_512 */

bool
EverCrypt_DRBG_generate_sha2_512(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_generate_sha2_512 */

/* SNIPPET_START: EverCrypt_DRBG_uninstantiate_sha1 */

void EverCrypt_DRBG_uninstantiate_sha1(EverCrypt_DRBG_state_s *st);

/* SNIPPET_END: EverCrypt_DRBG_uninstantiate_sha1 */

/* SNIPPET_START: EverCrypt_DRBG_uninstantiate_sha2_256 */

void EverCrypt_DRBG_uninstantiate_sha2_256(EverCrypt_DRBG_state_s *st);

/* SNIPPET_END: EverCrypt_DRBG_uninstantiate_sha2_256 */

/* SNIPPET_START: EverCrypt_DRBG_uninstantiate_sha2_384 */

void EverCrypt_DRBG_uninstantiate_sha2_384(EverCrypt_DRBG_state_s *st);

/* SNIPPET_END: EverCrypt_DRBG_uninstantiate_sha2_384 */

/* SNIPPET_START: EverCrypt_DRBG_uninstantiate_sha2_512 */

void EverCrypt_DRBG_uninstantiate_sha2_512(EverCrypt_DRBG_state_s *st);

/* SNIPPET_END: EverCrypt_DRBG_uninstantiate_sha2_512 */

/* SNIPPET_START: EverCrypt_DRBG_instantiate */

bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

/* SNIPPET_END: EverCrypt_DRBG_instantiate */

/* SNIPPET_START: EverCrypt_DRBG_reseed */

bool
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_reseed */

/* SNIPPET_START: EverCrypt_DRBG_generate */

bool
EverCrypt_DRBG_generate(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

/* SNIPPET_END: EverCrypt_DRBG_generate */

/* SNIPPET_START: EverCrypt_DRBG_uninstantiate */

void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st);

/* SNIPPET_END: EverCrypt_DRBG_uninstantiate */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_DRBG_H_DEFINED
#endif
