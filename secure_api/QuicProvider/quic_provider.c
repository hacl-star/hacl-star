#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "tmp/Crypto_Indexing.h"
#include "tmp/Crypto_Symmetric_Bytes.h"
#include "tmp/Crypto_Symmetric_MAC.h"
#include "tmp/Crypto_AEAD.h"
#include "tmp/Crypto_HMAC.h"
#include "tmp/Crypto_HKDF.h"
#include "mitlsffi.h"
#include "quic_provider.h"

typedef struct quic_key {
  Crypto_AEAD_Invariant_aead_state_______ st;
  Crypto_Indexing_id id;
  char static_iv[12];
} quic_key;

#define CONVERT_ALG(a) \
  (a == TLS_hash_SHA256 ? Crypto_HMAC_alg_SHA256 : \
    (a == TLS_hash_SHA384 ? Crypto_HMAC_alg_SHA384 : Crypto_HMAC_alg_SHA512))

int quic_crypto_hash(quic_hash a, /*out*/ char *hash, char *data, size_t len){
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HMAC_agile_hash(CONVERT_ALG(a), hash, data, len);
  return 1;
}

int quic_crypto_hmac(quic_hash a, char *mac,
                     char *key, uint32_t key_len,
                     char *data, uint32_t data_len) {
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HMAC_hmac(CONVERT_ALG(a), mac, key, key_len, data, data_len);
  return 1;
}

int quic_crypto_hkdf_extract(quic_hash a, char *prk,
                             char *salt, uint32_t salt_len,
                             char *ikm, uint32_t ikm_len)
{
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HKDF_hkdf_extract(CONVERT_ALG(a), prk, salt, salt_len, ikm, ikm_len);
  return 1;
}

int quic_crypto_hkdf_expand(quic_hash a, char *okm, uint32_t olen, char *prk, uint32_t prk_len, char *info, uint32_t info_len)
{
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HKDF_hkdf_expand(CONVERT_ALG(a), okm, prk, prk_len, info, info_len, olen);
  return 1;
}

int quic_crypto_derive_key(/*out*/quic_key **k, quic_secret *secret)
{
  quic_key *key = malloc(sizeof(quic_key));
  if(!(*k = key)) return 0;

  key->id = Crypto_Indexing_testId(secret->ae);
  char keyiv[76] = {0};
  uint32_t klen = (secret->ae == TLS_aead_AES_128_GCM ? 16 : 32);
  uint32_t slen = (secret->hash == TLS_hash_SHA256 ? 32 :
    (secret->hash == TLS_hash_SHA384 ? 48 : 64));
  quic_crypto_hkdf_extract(secret->hash, keyiv, secret->secret, slen, "key", 3);
  memcpy(key->static_iv, keyiv+klen, 12);

  key->st = Crypto_AEAD_coerce(key->id, FStar_HyperHeap_root, (uint8_t*)key);
  return 1;
}

int quic_crypto_encrypt(quic_key *key, char *cipher, uint64_t sn, char *ad, uint32_t ad_len, char *plain, uint32_t plain_len)
{
  char iv[12];
  memcpy(iv, key->static_iv, 12);
  FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128(12, iv);
  Crypto_AEAD_Encrypt_encrypt(key->id, key->st, n, ad_len, ad, plain_len, plain, cipher);
  return 1;
}

int quic_crypto_decrypt(quic_key *key, char *plain, uint64_t sn, char *ad, uint32_t ad_len, char *cipher, uint32_t cipher_len)
{
  char iv[12];
  memcpy(iv, key->static_iv, 12);
  FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128(12, iv);
  if(cipher_len < Crypto_Symmetric_MAC_taglen) return 0;
  uint32_t plain_len = cipher_len - Crypto_Symmetric_MAC_taglen;
  return Crypto_AEAD_Decrypt_decrypt(key->id, key->st, n, ad_len, ad, plain_len, plain, cipher);
}

int quic_crypto_free_key(quic_key *key)
{
  if(key) free(key);
}
