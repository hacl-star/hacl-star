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


#ifndef __EverCrypt_CTR_H
#define __EverCrypt_CTR_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "Hacl_Krmllib.h"
#include "EverCrypt_Error.h"
#include "EverCrypt_AutoConfig2.h"
#include "evercrypt_targetconfig.h"
/* SNIPPET_START: EverCrypt_CTR_state_s */

typedef struct EverCrypt_CTR_state_s_s EverCrypt_CTR_state_s;

/* SNIPPET_END: EverCrypt_CTR_state_s */

/* SNIPPET_START: EverCrypt_CTR_uu___is_State */

bool
EverCrypt_CTR_uu___is_State(Spec_Agile_Cipher_cipher_alg a, EverCrypt_CTR_state_s projectee);

/* SNIPPET_END: EverCrypt_CTR_uu___is_State */

/* SNIPPET_START: EverCrypt_CTR_state */

typedef EverCrypt_CTR_state_s *EverCrypt_CTR_state;

/* SNIPPET_END: EverCrypt_CTR_state */

/* SNIPPET_START: EverCrypt_CTR_uint8 */

typedef uint8_t EverCrypt_CTR_uint8;

/* SNIPPET_END: EverCrypt_CTR_uint8 */

/* SNIPPET_START: EverCrypt_CTR_xor8 */

uint8_t EverCrypt_CTR_xor8(uint8_t a, uint8_t b);

/* SNIPPET_END: EverCrypt_CTR_xor8 */

/* SNIPPET_START: EverCrypt_CTR_e_alg */

typedef void *EverCrypt_CTR_e_alg;

/* SNIPPET_END: EverCrypt_CTR_e_alg */

/* SNIPPET_START: EverCrypt_CTR_alg_of_state */

Spec_Agile_Cipher_cipher_alg EverCrypt_CTR_alg_of_state(EverCrypt_CTR_state_s *s);

/* SNIPPET_END: EverCrypt_CTR_alg_of_state */

/* SNIPPET_START: EverCrypt_CTR_create_in */

EverCrypt_Error_error_code
EverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s **dst,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
);

/* SNIPPET_END: EverCrypt_CTR_create_in */

/* SNIPPET_START: EverCrypt_CTR_init */

void
EverCrypt_CTR_init(
  EverCrypt_CTR_state_s *p,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
);

/* SNIPPET_END: EverCrypt_CTR_init */

/* SNIPPET_START: EverCrypt_CTR_update_block */

void EverCrypt_CTR_update_block(EverCrypt_CTR_state_s *p, uint8_t *dst, uint8_t *src);

/* SNIPPET_END: EverCrypt_CTR_update_block */

/* SNIPPET_START: EverCrypt_CTR_free */

void EverCrypt_CTR_free(EverCrypt_CTR_state_s *p);

/* SNIPPET_END: EverCrypt_CTR_free */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_CTR_H_DEFINED
#endif
