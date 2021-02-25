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


#ifndef __EverCrypt_H
#define __EverCrypt_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"


#include "EverCrypt_Hacl.h"
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Chacha20Poly1305_32.h"
#include "EverCrypt_OpenSSL.h"
#include "EverCrypt_Vale.h"

uint32_t EverCrypt_random_init();

void EverCrypt_random_sample(uint32_t len, uint8_t *out);

void EverCrypt_random_cleanup();

#define EverCrypt_AES128_OPENSSL 0
#define EverCrypt_AES128_BCRYPT 1
#define EverCrypt_AES128_VALE 2
#define EverCrypt_AES128_HACL 3

typedef uint8_t EverCrypt_aes128_key_s_tags;

typedef struct EverCrypt_aes128_key_s_s EverCrypt_aes128_key_s;

bool EverCrypt_uu___is_AES128_OPENSSL(EverCrypt_aes128_key_s projectee);

FStar_Dyn_dyn EverCrypt___proj__AES128_OPENSSL__item__st(EverCrypt_aes128_key_s projectee);

bool EverCrypt_uu___is_AES128_BCRYPT(EverCrypt_aes128_key_s projectee);

FStar_Dyn_dyn EverCrypt___proj__AES128_BCRYPT__item__st(EverCrypt_aes128_key_s projectee);

bool EverCrypt_uu___is_AES128_VALE(EverCrypt_aes128_key_s projectee);

uint8_t *EverCrypt___proj__AES128_VALE__item__w(EverCrypt_aes128_key_s projectee);

uint8_t *EverCrypt___proj__AES128_VALE__item__sbox(EverCrypt_aes128_key_s projectee);

bool EverCrypt_uu___is_AES128_HACL(EverCrypt_aes128_key_s projectee);

uint8_t *EverCrypt___proj__AES128_HACL__item__w(EverCrypt_aes128_key_s projectee);

uint8_t *EverCrypt___proj__AES128_HACL__item__sbox(EverCrypt_aes128_key_s projectee);

typedef EverCrypt_aes128_key_s *EverCrypt_aes128_key;

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

EverCrypt_aes128_key_s *EverCrypt_aes128_create(uint8_t *k);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes128_compute(EverCrypt_aes128_key_s *k, uint8_t *plain, uint8_t *cipher);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes128_free(EverCrypt_aes128_key_s *pk);

#define EverCrypt_AES256_OPENSSL 0
#define EverCrypt_AES256_BCRYPT 1
#define EverCrypt_AES256_HACL 2

typedef uint8_t EverCrypt_aes256_key_s_tags;

typedef struct EverCrypt_aes256_key_s_s EverCrypt_aes256_key_s;

bool EverCrypt_uu___is_AES256_OPENSSL(EverCrypt_aes256_key_s projectee);

FStar_Dyn_dyn EverCrypt___proj__AES256_OPENSSL__item__st(EverCrypt_aes256_key_s projectee);

bool EverCrypt_uu___is_AES256_BCRYPT(EverCrypt_aes256_key_s projectee);

FStar_Dyn_dyn EverCrypt___proj__AES256_BCRYPT__item__st(EverCrypt_aes256_key_s projectee);

bool EverCrypt_uu___is_AES256_HACL(EverCrypt_aes256_key_s projectee);

uint8_t *EverCrypt___proj__AES256_HACL__item__w(EverCrypt_aes256_key_s projectee);

uint8_t *EverCrypt___proj__AES256_HACL__item__sbox(EverCrypt_aes256_key_s projectee);

typedef EverCrypt_aes256_key_s *EverCrypt_aes256_key;

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

EverCrypt_aes256_key_s *EverCrypt_aes256_create(uint8_t *k);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes256_compute(EverCrypt_aes256_key_s *k, uint8_t *plain, uint8_t *cipher);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

void EverCrypt_aes256_free(EverCrypt_aes256_key_s *pk);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void
EverCrypt_aes128_gcm_encrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

uint32_t
EverCrypt_aes128_gcm_decrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void
EverCrypt_aes256_gcm_encrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

uint32_t
EverCrypt_aes256_gcm_decrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

#define EverCrypt_AES128_CBC 0
#define EverCrypt_AES256_CBC 1
#define EverCrypt_TDES_EDE_CBC 2

typedef uint8_t EverCrypt_block_cipher_alg;

bool EverCrypt_uu___is_AES128_CBC(EverCrypt_block_cipher_alg projectee);

bool EverCrypt_uu___is_AES256_CBC(EverCrypt_block_cipher_alg projectee);

bool EverCrypt_uu___is_TDES_EDE_CBC(EverCrypt_block_cipher_alg projectee);

uint32_t EverCrypt_block_cipher_keyLen(EverCrypt_block_cipher_alg uu___);

uint32_t EverCrypt_block_cipher_blockLen(EverCrypt_block_cipher_alg uu___);

#define EverCrypt_RC4_128 0

typedef uint8_t EverCrypt_stream_cipher_alg;

bool EverCrypt_uu___is_RC4_128(EverCrypt_stream_cipher_alg projectee);

#define EverCrypt_AES128_GCM 0
#define EverCrypt_AES256_GCM 1
#define EverCrypt_CHACHA20_POLY1305 2
#define EverCrypt_AES128_CCM 3
#define EverCrypt_AES256_CCM 4
#define EverCrypt_AES128_CCM8 5
#define EverCrypt_AES256_CCM8 6

typedef uint8_t EverCrypt_aead_alg;

bool EverCrypt_uu___is_AES128_GCM(EverCrypt_aead_alg projectee);

bool EverCrypt_uu___is_AES256_GCM(EverCrypt_aead_alg projectee);

bool EverCrypt_uu___is_CHACHA20_POLY1305(EverCrypt_aead_alg projectee);

bool EverCrypt_uu___is_AES128_CCM(EverCrypt_aead_alg projectee);

bool EverCrypt_uu___is_AES256_CCM(EverCrypt_aead_alg projectee);

bool EverCrypt_uu___is_AES128_CCM8(EverCrypt_aead_alg projectee);

bool EverCrypt_uu___is_AES256_CCM8(EverCrypt_aead_alg projectee);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

uint32_t EverCrypt_aead_keyLen(EverCrypt_aead_alg uu___);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

uint32_t EverCrypt_aead_tagLen(EverCrypt_aead_alg uu___);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

uint32_t EverCrypt_aead_ivLen(EverCrypt_aead_alg a);

#define EverCrypt_AEAD_OPENSSL 0
#define EverCrypt_AEAD_BCRYPT 1
#define EverCrypt_AEAD_AES128_GCM_VALE 2
#define EverCrypt_AEAD_AES256_GCM_VALE 3
#define EverCrypt_AEAD_CHACHA20_POLY1305_HACL 4

typedef uint8_t EverCrypt__aead_state_tags;

typedef struct EverCrypt__aead_state_s EverCrypt__aead_state;

typedef EverCrypt__aead_state EverCrypt_aead_state_s;

typedef EverCrypt__aead_state *EverCrypt_aead_state;

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

EverCrypt__aead_state *EverCrypt_aead_create(EverCrypt_aead_alg alg, uint8_t *k);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void
EverCrypt_aead_encrypt(
  EverCrypt__aead_state *pkey,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

uint32_t
EverCrypt_aead_decrypt(
  EverCrypt__aead_state *pkey,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

void EverCrypt_aead_free(EverCrypt__aead_state *pk);

#define EverCrypt_DH_OPENSSL 0
#define EverCrypt_DH_DUMMY 1

typedef uint8_t EverCrypt__dh_state_tags;

typedef struct EverCrypt__dh_state_s EverCrypt__dh_state;

typedef EverCrypt__dh_state EverCrypt_dh_state_s;

typedef EverCrypt__dh_state *EverCrypt_dh_state;

EverCrypt__dh_state
*EverCrypt_dh_load_group(
  uint8_t *dh_p,
  uint32_t dh_p_len,
  uint8_t *dh_g,
  uint32_t dh_g_len,
  uint8_t *dh_q,
  uint32_t dh_q_len
);

void EverCrypt_dh_free_group(EverCrypt__dh_state *st);

uint32_t EverCrypt_dh_keygen(EverCrypt__dh_state *st, uint8_t *public);

uint32_t
EverCrypt_dh_compute(
  EverCrypt__dh_state *st,
  uint8_t *public,
  uint32_t public_len,
  uint8_t *out
);

#define EverCrypt_ECC_P256 0
#define EverCrypt_ECC_P384 1
#define EverCrypt_ECC_P521 2
#define EverCrypt_ECC_X25519 3
#define EverCrypt_ECC_X448 4

typedef uint8_t EverCrypt_ec_curve;

bool EverCrypt_uu___is_ECC_P256(EverCrypt_ec_curve projectee);

bool EverCrypt_uu___is_ECC_P384(EverCrypt_ec_curve projectee);

bool EverCrypt_uu___is_ECC_P521(EverCrypt_ec_curve projectee);

bool EverCrypt_uu___is_ECC_X25519(EverCrypt_ec_curve projectee);

bool EverCrypt_uu___is_ECC_X448(EverCrypt_ec_curve projectee);

#define EverCrypt_ECDH_OPENSSL 0
#define EverCrypt_ECDH_DUMMY 1

typedef uint8_t EverCrypt__ecdh_state_tags;

typedef struct EverCrypt__ecdh_state_s EverCrypt__ecdh_state;

typedef EverCrypt__ecdh_state EverCrypt_ecdh_state_s;

typedef EverCrypt__ecdh_state *EverCrypt_ecdh_state;

EverCrypt__ecdh_state *EverCrypt_ecdh_load_curve(EverCrypt_ec_curve g);

void EverCrypt_ecdh_free_curve(EverCrypt__ecdh_state *st);

void EverCrypt_ecdh_keygen(EverCrypt__ecdh_state *st, uint8_t *outx, uint8_t *outy);

uint32_t
EverCrypt_ecdh_compute(EverCrypt__ecdh_state *st, uint8_t *inx, uint8_t *iny, uint8_t *out);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_H_DEFINED
#endif
