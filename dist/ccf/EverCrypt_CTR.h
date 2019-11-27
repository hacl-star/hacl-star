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

#ifndef __EverCrypt_CTR_H
#define __EverCrypt_CTR_H

#include "Hacl_Chacha20.h"
#include "Hacl_Kremlib.h"
#include "Vale.h"
#include "EverCrypt_AutoConfig2.h"
#include "EverCrypt_Error.h"
#include "Hacl_Spec.h"


typedef struct EverCrypt_CTR_state_s_s EverCrypt_CTR_state_s;

bool
EverCrypt_CTR_uu___is_State(Spec_Agile_Cipher_cipher_alg a, EverCrypt_CTR_state_s projectee);

Spec_Cipher_Expansion_impl
EverCrypt_CTR___proj__State__item__i(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
);

uint8_t
*EverCrypt_CTR___proj__State__item__iv(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
);

uint32_t
EverCrypt_CTR___proj__State__item__iv_len(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
);

uint8_t
*EverCrypt_CTR___proj__State__item__xkey(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
);

uint32_t
EverCrypt_CTR___proj__State__item__ctr(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s projectee
);

typedef uint8_t EverCrypt_CTR_uint8;

uint8_t EverCrypt_CTR_xor8(uint8_t a, uint8_t b);

typedef void *EverCrypt_CTR_e_alg;

Spec_Agile_Cipher_cipher_alg EverCrypt_CTR_alg_of_state(EverCrypt_CTR_state_s *s);

EverCrypt_Error_error_code
EverCrypt_CTR_create_in(
  Spec_Agile_Cipher_cipher_alg a,
  EverCrypt_CTR_state_s **dst,
  uint8_t *k1,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
);

void
EverCrypt_CTR_init(
  EverCrypt_CTR_state_s *p,
  uint8_t *k1,
  uint8_t *iv,
  uint32_t iv_len,
  uint32_t c
);

void EverCrypt_CTR_update_block(EverCrypt_CTR_state_s *p, uint8_t *dst, uint8_t *src);

void EverCrypt_CTR_free(EverCrypt_CTR_state_s *p);

#define __EverCrypt_CTR_H_DEFINED
#endif
