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


#ifndef __Hacl_HMAC_DRBG_H
#define __Hacl_HMAC_DRBG_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "Hacl_HMAC.h"
#include "Hacl_Spec.h"

typedef Spec_Hash_Definitions_hash_alg Hacl_HMAC_DRBG_supported_alg;

extern u32 Hacl_HMAC_DRBG_reseed_interval;

extern u32 Hacl_HMAC_DRBG_max_output_length;

extern u32 Hacl_HMAC_DRBG_max_length;

extern u32 Hacl_HMAC_DRBG_max_personalization_string_length;

extern u32 Hacl_HMAC_DRBG_max_additional_input_length;

u32 Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_hash_alg a);

typedef struct Hacl_HMAC_DRBG_state_s
{
  u8 *k;
  u8 *v;
  u32 *reseed_counter;
}
Hacl_HMAC_DRBG_state;

bool
Hacl_HMAC_DRBG_uu___is_State(Spec_Hash_Definitions_hash_alg a, Hacl_HMAC_DRBG_state projectee);

u8
*Hacl_HMAC_DRBG___proj__State__item__k(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
);

u8
*Hacl_HMAC_DRBG___proj__State__item__v(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
);

u32
*Hacl_HMAC_DRBG___proj__State__item__reseed_counter(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state projectee
);

Hacl_HMAC_DRBG_state Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_hash_alg a);

void
Hacl_HMAC_DRBG_instantiate(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  u32 entropy_input_len,
  u8 *entropy_input,
  u32 nonce_len,
  u8 *nonce,
  u32 personalization_string_len,
  u8 *personalization_string
);

void
Hacl_HMAC_DRBG_reseed(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  u32 entropy_input_len,
  u8 *entropy_input,
  u32 additional_input_input_len,
  u8 *additional_input_input
);

bool
Hacl_HMAC_DRBG_generate(
  Spec_Hash_Definitions_hash_alg a,
  u8 *output,
  Hacl_HMAC_DRBG_state st,
  u32 n,
  u32 additional_input_len,
  u8 *additional_input
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_HMAC_DRBG_H_DEFINED
#endif
