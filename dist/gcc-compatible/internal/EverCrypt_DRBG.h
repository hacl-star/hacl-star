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


#ifndef __internal_EverCrypt_DRBG_H
#define __internal_EverCrypt_DRBG_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "../EverCrypt_DRBG.h"
#include "evercrypt_targetconfig.h"
typedef struct EverCrypt_DRBG_state_s_s
{
  state_s_tags tag;
  union {
    Hacl_HMAC_DRBG_state case_SHA1_s;
    Hacl_HMAC_DRBG_state case_SHA2_256_s;
    Hacl_HMAC_DRBG_state case_SHA2_384_s;
    Hacl_HMAC_DRBG_state case_SHA2_512_s;
  }
  ;
}
EverCrypt_DRBG_state_s;

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

#if defined(__cplusplus)
}
#endif

#define __internal_EverCrypt_DRBG_H_DEFINED
#endif
