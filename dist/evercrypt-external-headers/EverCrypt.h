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

#include <inttypes.h>
#include <stdbool.h>
#include <kremlin/internal/types.h>
#include <kremlin/internal/target.h>




#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
#define Spec_Hash_Definitions_SHA2_384 2
#define Spec_Hash_Definitions_SHA2_512 3
#define Spec_Hash_Definitions_SHA1 4
#define Spec_Hash_Definitions_MD5 5
#define Spec_Hash_Definitions_Blake2S 6
#define Spec_Hash_Definitions_Blake2B 7

typedef uint8_t Spec_Hash_Definitions_hash_alg;

#define Spec_Cipher_Expansion_Hacl_CHACHA20 0
#define Spec_Cipher_Expansion_Vale_AES128 1
#define Spec_Cipher_Expansion_Vale_AES256 2

typedef uint8_t Spec_Cipher_Expansion_impl;

#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6

typedef uint8_t Spec_Agile_AEAD_alg;

#define EverCrypt_Error_Success 0
#define EverCrypt_Error_UnsupportedAlgorithm 1
#define EverCrypt_Error_InvalidKey 2
#define EverCrypt_Error_AuthenticationFailure 3
#define EverCrypt_Error_InvalidIVLength 4
#define EverCrypt_Error_DecodeError 5

typedef uint8_t EverCrypt_Error_error_code;

extern uint32_t EverCrypt_random_init();

extern void EverCrypt_random_sample(uint32_t len, uint8_t *out);

extern void EverCrypt_random_cleanup();

#define EverCrypt_AES128_OPENSSL 0
#define EverCrypt_AES128_BCRYPT 1
#define EverCrypt_AES128_VALE 2
#define EverCrypt_AES128_HACL 3

typedef uint8_t EverCrypt_aes128_key_s_tags;

typedef struct EverCrypt_aes128_key_s_s EverCrypt_aes128_key_s;

extern bool EverCrypt_uu___is_AES128_OPENSSL(EverCrypt_aes128_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES128_OPENSSL__item__st(EverCrypt_aes128_key_s projectee);

extern bool EverCrypt_uu___is_AES128_BCRYPT(EverCrypt_aes128_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES128_BCRYPT__item__st(EverCrypt_aes128_key_s projectee);

extern bool EverCrypt_uu___is_AES128_VALE(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_VALE__item__w(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_VALE__item__sbox(EverCrypt_aes128_key_s projectee);

extern bool EverCrypt_uu___is_AES128_HACL(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_HACL__item__w(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_HACL__item__sbox(EverCrypt_aes128_key_s projectee);

typedef EverCrypt_aes128_key_s *EverCrypt_aes128_key;

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

extern EverCrypt_aes128_key_s *EverCrypt_aes128_create(uint8_t *k);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

extern void
EverCrypt_aes128_compute(EverCrypt_aes128_key_s *k, uint8_t *plain, uint8_t *cipher);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

extern void EverCrypt_aes128_free(EverCrypt_aes128_key_s *pk);

#define EverCrypt_AES256_OPENSSL 0
#define EverCrypt_AES256_BCRYPT 1
#define EverCrypt_AES256_HACL 2

typedef uint8_t EverCrypt_aes256_key_s_tags;

typedef struct EverCrypt_aes256_key_s_s EverCrypt_aes256_key_s;

extern bool EverCrypt_uu___is_AES256_OPENSSL(EverCrypt_aes256_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES256_OPENSSL__item__st(EverCrypt_aes256_key_s projectee);

extern bool EverCrypt_uu___is_AES256_BCRYPT(EverCrypt_aes256_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES256_BCRYPT__item__st(EverCrypt_aes256_key_s projectee);

extern bool EverCrypt_uu___is_AES256_HACL(EverCrypt_aes256_key_s projectee);

extern uint8_t *EverCrypt___proj__AES256_HACL__item__w(EverCrypt_aes256_key_s projectee);

extern uint8_t *EverCrypt___proj__AES256_HACL__item__sbox(EverCrypt_aes256_key_s projectee);

typedef EverCrypt_aes256_key_s *EverCrypt_aes256_key;

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

extern EverCrypt_aes256_key_s *EverCrypt_aes256_create(uint8_t *k);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

extern void
EverCrypt_aes256_compute(EverCrypt_aes256_key_s *k, uint8_t *plain, uint8_t *cipher);

KRML_DEPRECATED("Please use EverCrypt_CTR.h (from C) or EverCrypt.CTR.fsti (from F*) ")

extern void EverCrypt_aes256_free(EverCrypt_aes256_key_s *pk);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

extern void
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

extern uint32_t
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

extern void
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

extern uint32_t
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

extern bool EverCrypt_uu___is_AES128_CBC(EverCrypt_block_cipher_alg projectee);

extern bool EverCrypt_uu___is_AES256_CBC(EverCrypt_block_cipher_alg projectee);

extern bool EverCrypt_uu___is_TDES_EDE_CBC(EverCrypt_block_cipher_alg projectee);

extern uint32_t EverCrypt_block_cipher_keyLen(EverCrypt_block_cipher_alg uu___);

extern uint32_t EverCrypt_block_cipher_blockLen(EverCrypt_block_cipher_alg uu___);

#define EverCrypt_RC4_128 0

typedef uint8_t EverCrypt_stream_cipher_alg;

extern bool EverCrypt_uu___is_RC4_128(EverCrypt_stream_cipher_alg projectee);

#define EverCrypt_AES128_GCM 0
#define EverCrypt_AES256_GCM 1
#define EverCrypt_CHACHA20_POLY1305 2
#define EverCrypt_AES128_CCM 3
#define EverCrypt_AES256_CCM 4
#define EverCrypt_AES128_CCM8 5
#define EverCrypt_AES256_CCM8 6

typedef uint8_t EverCrypt_aead_alg;

extern bool EverCrypt_uu___is_AES128_GCM(EverCrypt_aead_alg projectee);

extern bool EverCrypt_uu___is_AES256_GCM(EverCrypt_aead_alg projectee);

extern bool EverCrypt_uu___is_CHACHA20_POLY1305(EverCrypt_aead_alg projectee);

extern bool EverCrypt_uu___is_AES128_CCM(EverCrypt_aead_alg projectee);

extern bool EverCrypt_uu___is_AES256_CCM(EverCrypt_aead_alg projectee);

extern bool EverCrypt_uu___is_AES128_CCM8(EverCrypt_aead_alg projectee);

extern bool EverCrypt_uu___is_AES256_CCM8(EverCrypt_aead_alg projectee);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

extern uint32_t EverCrypt_aead_keyLen(EverCrypt_aead_alg uu___);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

extern uint32_t EverCrypt_aead_tagLen(EverCrypt_aead_alg uu___);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

extern uint32_t EverCrypt_aead_ivLen(EverCrypt_aead_alg a);

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

extern EverCrypt__aead_state *EverCrypt_aead_create(EverCrypt_aead_alg alg, uint8_t *k);

KRML_DEPRECATED("Please use EverCrypt_AEAD.h (from C) or EverCrypt.AEAD.fsti (from F*) ")

extern void
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

extern uint32_t
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

extern void EverCrypt_aead_free(EverCrypt__aead_state *pk);

#define EverCrypt_DH_OPENSSL 0
#define EverCrypt_DH_DUMMY 1

typedef uint8_t EverCrypt__dh_state_tags;

typedef struct EverCrypt__dh_state_s EverCrypt__dh_state;

typedef EverCrypt__dh_state EverCrypt_dh_state_s;

typedef EverCrypt__dh_state *EverCrypt_dh_state;

extern EverCrypt__dh_state
*EverCrypt_dh_load_group(
  uint8_t *dh_p,
  uint32_t dh_p_len,
  uint8_t *dh_g,
  uint32_t dh_g_len,
  uint8_t *dh_q,
  uint32_t dh_q_len
);

extern void EverCrypt_dh_free_group(EverCrypt__dh_state *st);

extern uint32_t EverCrypt_dh_keygen(EverCrypt__dh_state *st, uint8_t *public);

extern uint32_t
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

extern bool EverCrypt_uu___is_ECC_P256(EverCrypt_ec_curve projectee);

extern bool EverCrypt_uu___is_ECC_P384(EverCrypt_ec_curve projectee);

extern bool EverCrypt_uu___is_ECC_P521(EverCrypt_ec_curve projectee);

extern bool EverCrypt_uu___is_ECC_X25519(EverCrypt_ec_curve projectee);

extern bool EverCrypt_uu___is_ECC_X448(EverCrypt_ec_curve projectee);

#define EverCrypt_ECDH_OPENSSL 0
#define EverCrypt_ECDH_DUMMY 1

typedef uint8_t EverCrypt__ecdh_state_tags;

typedef struct EverCrypt__ecdh_state_s EverCrypt__ecdh_state;

typedef EverCrypt__ecdh_state EverCrypt_ecdh_state_s;

typedef EverCrypt__ecdh_state *EverCrypt_ecdh_state;

extern EverCrypt__ecdh_state *EverCrypt_ecdh_load_curve(EverCrypt_ec_curve g);

extern void EverCrypt_ecdh_free_curve(EverCrypt__ecdh_state *st);

extern void EverCrypt_ecdh_keygen(EverCrypt__ecdh_state *st, uint8_t *outx, uint8_t *outy);

extern uint32_t
EverCrypt_ecdh_compute(EverCrypt__ecdh_state *st, uint8_t *inx, uint8_t *iny, uint8_t *out);

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

extern bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

extern Spec_Cipher_Expansion_impl
EverCrypt_AEAD___proj__Ek__item__impl(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

extern uint8_t
*EverCrypt_AEAD___proj__Ek__item__ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

extern Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_state(EverCrypt_AEAD_state_s *a);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **r, uint8_t *dst);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *a,
  uint8_t *s,
  uint32_t iv,
  uint8_t *iv_len,
  uint32_t ad,
  uint8_t *ad_len,
  uint32_t plain,
  uint8_t *plain_len,
  uint8_t *cipher
);

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *a,
  uint8_t *s,
  uint32_t iv,
  uint8_t *iv_len,
  uint32_t ad,
  uint8_t *ad_len,
  uint32_t cipher,
  uint8_t *cipher_len,
  uint8_t *tag
);

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
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

extern EverCrypt_Error_error_code
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

extern void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *a);

extern bool EverCrypt_AutoConfig2_has_shaext();

extern bool EverCrypt_AutoConfig2_has_aesni();

extern bool EverCrypt_AutoConfig2_has_pclmulqdq();

extern bool EverCrypt_AutoConfig2_has_avx2();

extern bool EverCrypt_AutoConfig2_has_avx();

extern bool EverCrypt_AutoConfig2_has_bmi2();

extern bool EverCrypt_AutoConfig2_has_adx();

extern bool EverCrypt_AutoConfig2_has_sse();

extern bool EverCrypt_AutoConfig2_has_movbe();

extern bool EverCrypt_AutoConfig2_has_rdrand();

extern bool EverCrypt_AutoConfig2_has_avx512();

extern bool EverCrypt_AutoConfig2_wants_vale();

extern bool EverCrypt_AutoConfig2_wants_hacl();

extern bool EverCrypt_AutoConfig2_wants_openssl();

extern bool EverCrypt_AutoConfig2_wants_bcrypt();

extern void EverCrypt_AutoConfig2_recall();

extern void EverCrypt_AutoConfig2_init();

typedef void (*EverCrypt_AutoConfig2_disabler)();

extern void EverCrypt_AutoConfig2_disable_avx2();

extern void EverCrypt_AutoConfig2_disable_avx();

extern void EverCrypt_AutoConfig2_disable_bmi2();

extern void EverCrypt_AutoConfig2_disable_adx();

extern void EverCrypt_AutoConfig2_disable_shaext();

extern void EverCrypt_AutoConfig2_disable_aesni();

extern void EverCrypt_AutoConfig2_disable_pclmulqdq();

extern void EverCrypt_AutoConfig2_disable_sse();

extern void EverCrypt_AutoConfig2_disable_movbe();

extern void EverCrypt_AutoConfig2_disable_rdrand();

extern void EverCrypt_AutoConfig2_disable_avx512();

extern void EverCrypt_AutoConfig2_disable_vale();

extern void EverCrypt_AutoConfig2_disable_hacl();

extern void EverCrypt_AutoConfig2_disable_openssl();

extern void EverCrypt_AutoConfig2_disable_bcrypt();

extern void
EverCrypt_HKDF_expand_sha1(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract_sha1(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HKDF_expand_sha2_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract_sha2_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HKDF_expand_sha2_384(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract_sha2_384(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HKDF_expand_sha2_512(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract_sha2_512(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HKDF_expand_blake2s(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract_blake2s(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HKDF_expand_blake2b(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract_blake2b(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HKDF_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

extern void
EverCrypt_HKDF_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

KRML_DEPRECATED("expand")

extern void
EverCrypt_HKDF_hkdf_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);

KRML_DEPRECATED("extract")

extern void
EverCrypt_HKDF_hkdf_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);

extern void
EverCrypt_HMAC_compute_sha1(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern void
EverCrypt_HMAC_compute_sha2_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern void
EverCrypt_HMAC_compute_sha2_384(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern void
EverCrypt_HMAC_compute_sha2_512(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern void
EverCrypt_HMAC_compute_blake2s(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern void
EverCrypt_HMAC_compute_blake2b(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);

extern bool EverCrypt_HMAC_is_supported_alg(Spec_Hash_Definitions_hash_alg uu___);

typedef Spec_Hash_Definitions_hash_alg EverCrypt_HMAC_supported_alg;

extern void
EverCrypt_HMAC_compute(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *mac,
  uint8_t *key,
  uint32_t keylen,
  uint8_t *data,
  uint32_t datalen
);

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg;

extern C_String_t EverCrypt_Hash_string_of_alg(Spec_Hash_Definitions_hash_alg uu___);

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_broken_alg;

typedef Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg13;

typedef void *EverCrypt_Hash_e_alg;

#define EverCrypt_Hash_MD5_s 0
#define EverCrypt_Hash_SHA1_s 1
#define EverCrypt_Hash_SHA2_224_s 2
#define EverCrypt_Hash_SHA2_256_s 3
#define EverCrypt_Hash_SHA2_384_s 4
#define EverCrypt_Hash_SHA2_512_s 5
#define EverCrypt_Hash_Blake2S_s 6
#define EverCrypt_Hash_Blake2B_s 7

typedef uint8_t EverCrypt_Hash_state_s_tags;

typedef struct EverCrypt_Hash_state_s_s
{
  EverCrypt_Hash_state_s_tags tag;
  union {
    uint32_t *case_MD5_s;
    uint32_t *case_SHA1_s;
    uint32_t *case_SHA2_224_s;
    uint32_t *case_SHA2_256_s;
    uint64_t *case_SHA2_384_s;
    uint64_t *case_SHA2_512_s;
    uint32_t *case_Blake2S_s;
    uint64_t *case_Blake2B_s;
  }
  ;
}
EverCrypt_Hash_state_s;

extern bool
EverCrypt_Hash_uu___is_MD5_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint32_t
*EverCrypt_Hash___proj__MD5_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_SHA1_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint32_t
*EverCrypt_Hash___proj__SHA1_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_SHA2_224_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint32_t
*EverCrypt_Hash___proj__SHA2_224_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_SHA2_256_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint32_t
*EverCrypt_Hash___proj__SHA2_256_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_SHA2_384_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint64_t
*EverCrypt_Hash___proj__SHA2_384_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_SHA2_512_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint64_t
*EverCrypt_Hash___proj__SHA2_512_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_Blake2S_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint32_t
*EverCrypt_Hash___proj__Blake2S_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern bool
EverCrypt_Hash_uu___is_Blake2B_s(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern uint64_t
*EverCrypt_Hash___proj__Blake2B_s__item__p(
  Spec_Hash_Definitions_hash_alg uu___,
  EverCrypt_Hash_state_s projectee
);

extern Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *a);

extern EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a);

extern EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a);

extern void EverCrypt_Hash_init(EverCrypt_Hash_state_s *a);

extern void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *ev, uint32_t blocks);

extern void EverCrypt_Hash_update2(EverCrypt_Hash_state_s *a, uint64_t s, uint8_t *prevlen);

KRML_DEPRECATED("Use update2 instead")

extern void EverCrypt_Hash_update(EverCrypt_Hash_state_s *a, uint8_t *s);

extern void
EverCrypt_Hash_update_multi2(
  EverCrypt_Hash_state_s *a,
  uint64_t s,
  uint8_t *prevlen,
  uint32_t blocks
);

KRML_DEPRECATED("Use update_multi2 instead")

extern void
EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *a, uint8_t *s, uint32_t blocks);

extern void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
);

extern void
EverCrypt_Hash_update_last2(
  EverCrypt_Hash_state_s *a,
  uint64_t s,
  uint8_t *prev_len,
  uint32_t last
);

KRML_DEPRECATED("Use update_last2 instead")

extern void EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *ga, uint8_t *s, uint64_t last);

extern void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *a, uint8_t *s);

extern void EverCrypt_Hash_free(EverCrypt_Hash_state_s *ea);

extern void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *a, EverCrypt_Hash_state_s *s_src);

extern void EverCrypt_Hash_hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst);

extern void EverCrypt_Hash_hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst);

extern void
EverCrypt_Hash_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t *input,
  uint32_t len
);

extern uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a);

extern uint32_t EverCrypt_Hash_Incremental_block_len(Spec_Hash_Definitions_hash_alg a);

typedef struct Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s_____s
{
  EverCrypt_Hash_state_s *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____;

extern Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
*EverCrypt_Hash_Incremental_create_in(Spec_Hash_Definitions_hash_alg a);

extern void
EverCrypt_Hash_Incremental_init(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *a);

extern void
EverCrypt_Hash_Incremental_update(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *i,
  uint8_t *p,
  uint32_t data
);

extern void
EverCrypt_Hash_Incremental_finish_md5(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_sha1(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_sha224(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_sha256(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_sha384(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_sha512(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_blake2s(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_finish_blake2b(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *dst
);

extern Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *a
);

extern void
EverCrypt_Hash_Incremental_finish(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *a,
  uint8_t *s
);

extern void
EverCrypt_Hash_Incremental_free(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *i);

extern void
EverCrypt_Cipher_chacha20(
  uint32_t len,
  uint8_t *dst,
  uint8_t *src,
  uint8_t *key,
  uint8_t *iv,
  uint32_t ctr
);

extern void
EverCrypt_Poly1305_poly1305(uint8_t *dst, uint8_t *src, uint32_t len, uint8_t *key);

extern void
EverCrypt_Chacha20Poly1305_aead_encrypt(
  uint8_t *k,
  uint8_t *n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *tag
);

extern uint32_t
EverCrypt_Chacha20Poly1305_aead_decrypt(
  uint8_t *k,
  uint8_t *n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *tag
);

extern void EverCrypt_Curve25519_secret_to_public(uint8_t *pub, uint8_t *priv);

extern void
EverCrypt_Curve25519_scalarmult(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub);

extern bool EverCrypt_Curve25519_ecdh(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_H_DEFINED
#endif
