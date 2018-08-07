
#ifndef __EverCrypt_Lib_H
#define __EverCrypt_Lib_H

#include <stdint.h>

extern void EverCrypt_x25519(uint8_t *dst, uint8_t *secret, uint8_t *base);

#define EverCrypt_AES128_OPENSSL 0
#define EverCrypt_AES128_BCRYPT 1
#define EverCrypt_AES128_VALE 2
#define EverCrypt_AES128_HACL 3

typedef uint8_t EverCrypt_aes128_key_s_tags;

typedef struct EverCrypt_aes128_key_s_s EverCrypt_aes128_key_s;

typedef EverCrypt_aes128_key_s *EverCrypt_aes128_key;

extern EverCrypt_aes128_key_s *EverCrypt_aes128_create(uint8_t *k);

extern void EverCrypt_aes128_compute(EverCrypt_aes128_key_s *k, uint8_t *plain, uint8_t *cipher);

extern void EverCrypt_aes128_free(EverCrypt_aes128_key_s *pk);

#define EverCrypt_AES256_OPENSSL 0
#define EverCrypt_AES256_BCRYPT 1
#define EverCrypt_AES256_HACL 2

typedef uint8_t EverCrypt_aes256_key_s_tags;

typedef struct EverCrypt_aes256_key_s_s EverCrypt_aes256_key_s;

typedef EverCrypt_aes256_key_s *EverCrypt_aes256_key;

extern EverCrypt_aes256_key_s *EverCrypt_aes256_create(uint8_t *k);

extern void EverCrypt_aes256_compute(EverCrypt_aes256_key_s *k, uint8_t *plain, uint8_t *cipher);

extern void EverCrypt_aes256_free(EverCrypt_aes256_key_s *pk);

extern void
EverCrypt_chacha20(
  uint8_t *key,
  uint8_t *iv,
  uint32_t ctr,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher
);

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

extern void
EverCrypt_chacha20_poly1305_encrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

extern uint32_t
EverCrypt_chacha20_poly1305_decrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plaintext,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

#define EverCrypt_AES128_GCM 0
#define EverCrypt_AES256_GCM 1
#define EverCrypt_CHACHA20_POLY1305 2

typedef uint8_t EverCrypt_aead_alg;

#define EverCrypt_AEAD_OPENSSL 0
#define EverCrypt_AEAD_BCRYPT 1
#define EverCrypt_AEAD_AES128_GCM_VALE 2
#define EverCrypt_AEAD_AES256_GCM_VALE 3
#define EverCrypt_AEAD_CHACHA20_POLY1305_HACL 4

typedef uint8_t EverCrypt__aead_state_tags;

typedef struct EverCrypt__aead_state_s EverCrypt__aead_state;

typedef EverCrypt__aead_state EverCrypt_aead_state_s;

typedef EverCrypt__aead_state *EverCrypt_aead_state;

extern EverCrypt__aead_state *EverCrypt_aead_create(EverCrypt_aead_alg alg, uint8_t *k);

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

extern void EverCrypt_aead_free(EverCrypt__aead_state *pk);

#endif
