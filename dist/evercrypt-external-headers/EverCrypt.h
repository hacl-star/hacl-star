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
#include <krml/internal/types.h>
#include <krml/internal/target.h>




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

typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;

extern bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

extern Spec_Cipher_Expansion_impl
EverCrypt_AEAD___proj__Ek__item__impl(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

extern uint8_t
*EverCrypt_AEAD___proj__Ek__item__ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);

extern Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_state(EverCrypt_AEAD_state_s *s);

extern EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k);

extern EverCrypt_Error_error_code
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

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
extern EverCrypt_Error_error_code
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

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
extern EverCrypt_Error_error_code
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

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
extern EverCrypt_Error_error_code
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

/*
WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit.
*/
extern EverCrypt_Error_error_code
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

extern void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s);

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

extern bool EverCrypt_AutoConfig2_has_vec128();

extern bool EverCrypt_AutoConfig2_has_vec256();

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

typedef EverCrypt_Hash_state_s *EverCrypt_Hash_state;

extern Spec_Hash_Definitions_hash_alg EverCrypt_Hash_alg_of_state(EverCrypt_Hash_state_s *s);

extern EverCrypt_Hash_state_s *EverCrypt_Hash_create_in(Spec_Hash_Definitions_hash_alg a);

extern EverCrypt_Hash_state_s *EverCrypt_Hash_create(Spec_Hash_Definitions_hash_alg a);

extern void EverCrypt_Hash_init(EverCrypt_Hash_state_s *s);

extern void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n);

extern void
EverCrypt_Hash_update2(EverCrypt_Hash_state_s *s, uint64_t prevlen, uint8_t *block);

KRML_DEPRECATED("Use update2 instead")

extern void EverCrypt_Hash_update(EverCrypt_Hash_state_s *s, uint8_t *block);

extern void
EverCrypt_Hash_update_multi2(
  EverCrypt_Hash_state_s *s,
  uint64_t prevlen,
  uint8_t *blocks,
  uint32_t len
);

KRML_DEPRECATED("Use update_multi2 instead")

extern void
EverCrypt_Hash_update_multi(EverCrypt_Hash_state_s *s, uint8_t *blocks, uint32_t len);

extern void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t input,
  uint8_t *input_len,
  uint32_t input_len1
);

extern void
EverCrypt_Hash_update_last2(
  EverCrypt_Hash_state_s *s,
  uint64_t prev_len,
  uint8_t *last,
  uint32_t last_len
);

KRML_DEPRECATED("Use update_last2 instead")

extern void
EverCrypt_Hash_update_last(EverCrypt_Hash_state_s *s, uint8_t *last, uint64_t total_len);

extern void EverCrypt_Hash_finish(EverCrypt_Hash_state_s *s, uint8_t *dst);

extern void EverCrypt_Hash_free(EverCrypt_Hash_state_s *s);

extern void EverCrypt_Hash_copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst);

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
EverCrypt_Hash_Incremental_init(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s);

extern void
EverCrypt_Hash_Incremental_update(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *p,
  uint8_t *data,
  uint32_t len
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
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s
);

extern void
EverCrypt_Hash_Incremental_finish(
  Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s,
  uint8_t *dst
);

extern void
EverCrypt_Hash_Incremental_free(Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____ *s);

typedef Hacl_Streaming_Functor_state_s___EverCrypt_Hash_state_s____
*EverCrypt_Hash_Incremental_state;

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
