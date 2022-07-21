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


#ifndef __EverCrypt_AEAD_H
#define __EverCrypt_AEAD_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "EverCrypt_Error.h"
#include "EverCrypt_Chacha20Poly1305.h"
#include "EverCrypt_AutoConfig2.h"
#include "evercrypt_targetconfig.h"
/* SNIPPET_START: EverCrypt_AEAD_state_s */

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

/* SNIPPET_END: EverCrypt_AEAD_state_s */

/* SNIPPET_START: EverCrypt_AEAD_uu___is_Ek */

bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

/* SNIPPET_END: EverCrypt_AEAD_uu___is_Ek */

/* SNIPPET_START: EverCrypt_AEAD_alg_of_state */

Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_state(EverCrypt_AEAD_state_s *s);

/* SNIPPET_END: EverCrypt_AEAD_alg_of_state */

/* SNIPPET_START: EverCrypt_AEAD_create_in */

EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k);

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

/* SNIPPET_START: EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check */

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check */

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_expand_aes128_gcm */

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes128_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt_expand_aes128_gcm */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_expand_aes256_gcm */

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes256_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt_expand_aes256_gcm */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_expand_chacha20_poly1305 */

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt_expand_chacha20_poly1305 */

/* SNIPPET_START: EverCrypt_AEAD_encrypt_expand */

EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand(
  Spec_Agile_AEAD_alg a,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);

/* SNIPPET_END: EverCrypt_AEAD_encrypt_expand */

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

/* SNIPPET_START: EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check */

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check */

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_expand_aes128_gcm */

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes128_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt_expand_aes128_gcm */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_expand_aes256_gcm */

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes256_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt_expand_aes256_gcm */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_expand_chacha20_poly1305 */

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt_expand_chacha20_poly1305 */

/* SNIPPET_START: EverCrypt_AEAD_decrypt_expand */

EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand(
  Spec_Agile_AEAD_alg a,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);

/* SNIPPET_END: EverCrypt_AEAD_decrypt_expand */

/* SNIPPET_START: EverCrypt_AEAD_free */

void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s);

/* SNIPPET_END: EverCrypt_AEAD_free */

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_AEAD_H_DEFINED
#endif
