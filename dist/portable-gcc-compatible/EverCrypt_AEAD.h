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
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __EverCrypt_AEAD_H
#define __EverCrypt_AEAD_H

#include "Hacl_Kremlib.h"
#include "EverCrypt_Chacha20Poly1305.h"
#include "Vale.h"
#include "EverCrypt_AutoConfig2.h"
#include "EverCrypt_Error.h"
#include "Hacl_Spec.h"


/* SNIPPET_START: EverCrypt_AEAD_state_s */

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

/* SNIPPET_END: EverCrypt_AEAD_state_s */

/* SNIPPET_START: EverCrypt_AEAD_uu___is_Ek */

bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

/* SNIPPET_END: EverCrypt_AEAD_uu___is_Ek */

/* SNIPPET_START: EverCrypt_AEAD___proj__Ek__item__impl */

Spec_Cipher_Expansion_impl
EverCrypt_AEAD___proj__Ek__item__impl(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

/* SNIPPET_END: EverCrypt_AEAD___proj__Ek__item__impl */

/* SNIPPET_START: EverCrypt_AEAD___proj__Ek__item__ek */

uint8_t
*EverCrypt_AEAD___proj__Ek__item__ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

/* SNIPPET_END: EverCrypt_AEAD___proj__Ek__item__ek */

/* SNIPPET_START: EverCrypt_AEAD_alg_of_state */

Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_state(EverCrypt_AEAD_state_s *s);

/* SNIPPET_END: EverCrypt_AEAD_alg_of_state */

/* SNIPPET_START: EverCrypt_AEAD_create_in */

EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k1);

/* SNIPPET_END: EverCrypt_AEAD_create_in */

/* SNIPPET_START: EverCrypt_AEAD_encrypt */

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt */

/* SNIPPET_START: EverCrypt_AEAD_decrypt */

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt */

/* SNIPPET_START: EverCrypt_AEAD_free */

void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s);

/* SNIPPET_END: EverCrypt_AEAD_free */

#define __EverCrypt_AEAD_H_DEFINED
#endif
