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

#include "evercrypt_targetconfig.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __EverCrypt_DRBG_H
#define __EverCrypt_DRBG_H

#include "EverCrypt_HMAC.h"
#include "Hacl_Leftovers.h"
#include "Lib_RandomBuffer_System.h"
#include "Hacl_Spec.h"
#include "Hacl_Lib.h"


typedef Spec_Hash_Definitions_hash_alg EverCrypt_DRBG_supported_alg;

extern uint32_t EverCrypt_DRBG_reseed_interval;

extern uint32_t EverCrypt_DRBG_max_output_length;

extern uint32_t EverCrypt_DRBG_max_length;

extern uint32_t EverCrypt_DRBG_max_personalization_string_length;

extern uint32_t EverCrypt_DRBG_max_additional_input_length;

uint32_t EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a);

#define EverCrypt_DRBG_SHA1_s 0
#define EverCrypt_DRBG_SHA2_256_s 1
#define EverCrypt_DRBG_SHA2_384_s 2
#define EverCrypt_DRBG_SHA2_512_s 3

typedef uint8_t EverCrypt_DRBG_state_s_tags;

typedef struct EverCrypt_DRBG_state_s_s EverCrypt_DRBG_state_s;

bool
EverCrypt_DRBG_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu____164,
  EverCrypt_DRBG_state_s projectee
);

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA1_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____207,
  EverCrypt_DRBG_state_s projectee
);

bool
EverCrypt_DRBG_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu____239,
  EverCrypt_DRBG_state_s projectee
);

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_256_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____282,
  EverCrypt_DRBG_state_s projectee
);

bool
EverCrypt_DRBG_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu____314,
  EverCrypt_DRBG_state_s projectee
);

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_384_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____357,
  EverCrypt_DRBG_state_s projectee
);

bool
EverCrypt_DRBG_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu____389,
  EverCrypt_DRBG_state_s projectee
);

Hacl_HMAC_DRBG_state
EverCrypt_DRBG___proj__SHA2_512_s__item___0(
  Spec_Hash_Definitions_hash_alg uu____432,
  EverCrypt_DRBG_state_s projectee
);

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a);

bool
EverCrypt_DRBG_instantiate_sha1(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

bool
EverCrypt_DRBG_instantiate_sha2_256(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

bool
EverCrypt_DRBG_instantiate_sha2_384(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

bool
EverCrypt_DRBG_instantiate_sha2_512(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

bool
EverCrypt_DRBG_reseed_sha1(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_reseed_sha2_256(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_reseed_sha2_384(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_reseed_sha2_512(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_generate_sha1(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_generate_sha2_256(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_generate_sha2_384(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_generate_sha2_512(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

void EverCrypt_DRBG_uninstantiate_sha1(EverCrypt_DRBG_state_s *st);

void EverCrypt_DRBG_uninstantiate_sha2_256(EverCrypt_DRBG_state_s *st);

void EverCrypt_DRBG_uninstantiate_sha2_384(EverCrypt_DRBG_state_s *st);

void EverCrypt_DRBG_uninstantiate_sha2_512(EverCrypt_DRBG_state_s *st);

bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

bool
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_generate(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n1,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st);

#define __EverCrypt_DRBG_H_DEFINED
#endif
