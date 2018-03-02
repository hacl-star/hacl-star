#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "kremlib.h"
#include "Crypto_HKDF_Crypto_HMAC.h"
#include "Crypto_AEAD_Main_Crypto_Indexing.h"
#include "Crypto_Symmetric_Bytes.h"
#include "quic_provider.h"

#define DEBUG 0

typedef struct quic_key {
  Crypto_AEAD_Invariant_aead_state st;
  Crypto_Indexing_id id;
  char static_iv[12];
} quic_key;

#if DEBUG
static void dump(char buffer[], size_t len)
{
  size_t i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

static void dump_secret(quic_secret *s)
{
  const char *ha =
    s->hash == TLS_hash_SHA256 ? "SHA256" :
    (s->hash == TLS_hash_SHA384 ? "SHA384" :
      (s->hash == TLS_hash_SHA512 ? "SHA512" : "BAD"));
  const char *ae =
    s->ae == TLS_aead_AES_128_GCM ? "AES-128-GCM" :
      (s->ae == TLS_aead_CHACHA20_POLY1305 ? "CHACHA20-POLY1305" :
        (s->ae == TLS_aead_AES_256_GCM ? "AES-256-GCM" : "BAD"));
  printf("SECRET %s %s\n", ha, ae);
  uint32_t hlen = (s->hash == TLS_hash_SHA256 ? 32 :
    (s->hash == TLS_hash_SHA384 ? 48 : 64));
  dump(s->secret, hlen);
}
#endif

#define CONVERT_ALG(a) \
  (a == TLS_hash_SHA256 ? Crypto_HMAC_SHA256 : \
    (a == TLS_hash_SHA384 ? Crypto_HMAC_SHA384 : Crypto_HMAC_SHA512))

int MITLS_CALLCONV quic_crypto_hash(quic_hash a, /*out*/ char *hash, const char *data, size_t len){
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HMAC_agile_hash(CONVERT_ALG(a), (uint8_t*) hash, (uint8_t*)data, len);
  return 1;
}

int MITLS_CALLCONV quic_crypto_hmac(quic_hash a, char *mac,
                     const char *key, uint32_t key_len,
                     const char *data, uint32_t data_len) {
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HMAC_hmac(CONVERT_ALG(a), (uint8_t*) mac, (uint8_t*)key, key_len, (uint8_t*)data, data_len);
  return 1;
}

int MITLS_CALLCONV quic_crypto_hkdf_extract(quic_hash a, char *prk,
                             const char *salt, uint32_t salt_len,
                             const char *ikm, uint32_t ikm_len)
{
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HKDF_hkdf_extract(CONVERT_ALG(a), (uint8_t*) prk, (uint8_t*)salt, salt_len, (uint8_t*)ikm, ikm_len);
  return 1;
}

int MITLS_CALLCONV quic_crypto_hkdf_expand(quic_hash a, char *okm, uint32_t olen, const char *prk, uint32_t prk_len, const char *info, uint32_t info_len)
{
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HKDF_hkdf_expand(CONVERT_ALG(a), (uint8_t*) okm, (uint8_t*)prk, prk_len, (uint8_t*)info, info_len, olen);
  return 1;
}

int MITLS_CALLCONV quic_crypto_hkdf_tls_label(quic_hash a, char *info, size_t *info_len, const char *label)
{
  size_t label_len = strlen(label);
  uint32_t hlen = (a == TLS_hash_SHA256 ? 32 : (a == TLS_hash_SHA384 ? 48 : 64));
  char *hash = alloca(hlen);

  if(a < TLS_hash_SHA256 || !info || !hash || label_len > 249)
    return 0;

  info[0] = 0;
  info[1] = (char)hlen;
  info[2] = (char)(label_len + 6);
  memcpy(info+3, "tls13 ", 6);
  memcpy(info+9, label, label_len);

  if(!quic_crypto_hash(a, hash, label, 0))
    return 0;

  info[9+label_len] = (char)hlen;
  memcpy(info + label_len + 10, hash, hlen);
  *info_len = label_len + 10 + hlen;

  return 1;
}

int MITLS_CALLCONV quic_crypto_hkdf_quic_label(quic_hash a, char *info, size_t *info_len, const char *label, uint16_t key_len)
{
  uint32_t hlen = (a == TLS_hash_SHA256 ? 32 :
    (a == TLS_hash_SHA384 ? 48 : 64));
  size_t label_len = strlen(label);

  if(a < TLS_hash_SHA256 || !info || label_len > 249)
    return 0;

  info[0] = key_len >> 8;
  info[1] = key_len & 255;
  info[2] = (char)(label_len + 5);
  memcpy(info+3, "QUIC ", 5);
  memcpy(info+8, label, label_len);
  info[8 + label_len] = 0;
  *info_len = label_len + 9;

  return 1;
}

int MITLS_CALLCONV quic_crypto_tls_derive_secret(quic_secret *derived, const quic_secret *secret, const char *label)
{
  uint32_t hlen = (secret->hash == TLS_hash_SHA256 ? 32 :
    (secret->hash == TLS_hash_SHA384 ? 48 : 64));
  char *tmp = alloca(hlen);
  char info[323] = {0};
  size_t info_len;

  if(!quic_crypto_hkdf_tls_label(secret->hash, info, &info_len, label))
    return 0;

  derived->hash = secret->hash;
  derived->ae = secret->ae;

#if DEBUG
  printf("Secret to expand <%s>:\n", label);
  dump_secret(secret);
#endif

  if(!quic_crypto_hkdf_expand(secret->hash, tmp, hlen,
        (const char*)secret->secret, hlen, info, info_len))
    return 0;

#if DEBUG
  printf("Intermediate:\n");
  dump(tmp, hlen);
#endif

  if(!quic_crypto_hkdf_tls_label(secret->hash, info, &info_len, "exporter"))
    return 0;

  if(!quic_crypto_hkdf_expand(secret->hash, (char*)derived->secret, hlen,
        tmp, hlen, info, info_len))
    return 0;

#if DEBUG
  printf("Derived:\n");
  dump_secret(derived);
#endif

  return 1;
}

int MITLS_CALLCONV quic_derive_handshake_secrets(quic_secret *client_hs, quic_secret *server_hs, const char *con_id, size_t con_id_len, const char *salt, size_t salt_len)
{
  quic_secret s0 = {
    .hash = TLS_hash_SHA256,
    .ae = TLS_aead_AES_128_GCM,
    .secret = {0}
  };
  char info[259] = {0};
  size_t info_len;

  if(!quic_crypto_hkdf_extract(s0.hash, (char*)s0.secret, salt, salt_len, con_id, con_id_len))
    return 0;

  client_hs->hash = s0.hash;
  client_hs->ae = s0.ae;
  if(!quic_crypto_hkdf_quic_label(s0.hash, info, &info_len, "client hs", 32))
    return 0;
  if(!quic_crypto_hkdf_expand(s0.hash, (char*)client_hs->secret, 32, (char*)s0.secret, 32, info, info_len))
    return 0;

  server_hs->hash = s0.hash;
  server_hs->ae = s0.ae;
  if(!quic_crypto_hkdf_quic_label(s0.hash, info, &info_len, "server hs", 32))
    return 0;
  if(!quic_crypto_hkdf_expand(s0.hash, (char*)server_hs->secret, 32, (char*)s0.secret, 32, info, info_len))
    return 0;

  return 1;
}

int MITLS_CALLCONV quic_crypto_derive_key(quic_key **k, const quic_secret *secret)
{
  quic_key *key = KRML_HOST_MALLOC(sizeof(quic_key));
  if(!key) return 0;

  key->id = Crypto_Indexing_testId((Crypto_Indexing_aeadAlg)secret->ae);

  uint32_t klen = (secret->ae == TLS_aead_AES_128_GCM ? 16 : 32);
  uint32_t slen = (secret->hash == TLS_hash_SHA256 ? 32 :
    (secret->hash == TLS_hash_SHA384 ? 48 : 64));

  char info[259] = {0};
  char dkey[32];
  size_t info_len;

  if(!quic_crypto_hkdf_quic_label(secret->hash, info, &info_len, "key", klen))
    return 0;
  if(!quic_crypto_hkdf_expand(secret->hash, dkey, klen, (char*)secret->secret, slen, info, info_len))
    return 0;

  if(!quic_crypto_hkdf_quic_label(secret->hash, info, &info_len, "iv", 12))
    return 0;
  if(!quic_crypto_hkdf_expand(secret->hash, key->static_iv, 12, (char*)secret->secret, slen, info, info_len))
    return 0;

#if DEBIG
   printf("KEY: "); dump(dkey, klen);
   printf("IV: "); dump(key->static_iv, 12);
#endif

  key->st = Crypto_AEAD_Main_coerce(key->id, (uint8_t*)dkey);
  *k = key;
  return 1;
}

static inline void sn_to_iv(char *iv, uint64_t sn)
{
  for(int i = 4; i < 12; i++)
    iv[i] ^= (sn >> (88-(i<<3))) & 255;
}

int MITLS_CALLCONV quic_crypto_create(quic_key **key, mitls_aead alg, const char *raw_key, const char *iv)
{
  quic_key *k = KRML_HOST_MALLOC(sizeof(quic_key));
  if(!k) return 0;
  k->id = Crypto_Indexing_testId((Crypto_Indexing_aeadAlg)alg);
  k->st = Crypto_AEAD_Main_coerce(k->id, (uint8_t*)raw_key);
  memcpy(k->static_iv, iv, 12);
  *key = k;
  return 1;
}

int MITLS_CALLCONV quic_crypto_encrypt(quic_key *key, char *cipher, uint64_t sn, const char *ad, uint32_t ad_len, const char *plain, uint32_t plain_len)
{
  char iv[12];
  memcpy(iv, key->static_iv, 12);
  sn_to_iv(iv, sn);

  FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128(12, (uint8_t*)iv);
  Crypto_AEAD_Main_encrypt(key->id, key->st, n, ad_len, (uint8_t*)ad, plain_len, (uint8_t*)plain, (uint8_t*)cipher);

#if DEBUG
  printf("ENCRYPT\nIV="); dump(iv, 12);
  printf("STATIC="); dump(key->static_iv, 12);
  printf("AD="); dump(ad, ad_len);
  printf("PLAIN="); dump(plain, plain_len);
  printf("CIPHER="); dump(cipher, plain_len + 16);
#endif

  return 1;
}

int MITLS_CALLCONV quic_crypto_decrypt(quic_key *key, char *plain, uint64_t sn, const char *ad, uint32_t ad_len, const char *cipher, uint32_t cipher_len)
{
  char iv[12];
  memcpy(iv, key->static_iv, 12);
  sn_to_iv(iv, sn);

  if(cipher_len < quic_crypto_tag_length(key))
    return 0;

  FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128(12, (uint8_t*)iv);
  uint32_t plain_len = cipher_len - quic_crypto_tag_length(key);
  int r = Crypto_AEAD_Main_decrypt(key->id, key->st, n, ad_len, (uint8_t*)ad, plain_len, (uint8_t*)plain, (uint8_t*)cipher);

#if DEBUG
  printf("DECRYPT %s\nIV=", r?"OK":"BAD"); dump(iv, 12);
  printf("STATIC="); dump(key->static_iv, 12);
  printf("AD="); dump(ad, ad_len);
  printf("CIPHER="); dump(cipher, cipher_len);
  printf("PLAIN="); dump(plain, plain_len);
#endif

  return r;
}

int MITLS_CALLCONV quic_crypto_free_key(quic_key *key)
{
  // ADL: the PRF stats is allocated with Buffer.screate
  // TODO switch to caller allocated style in Crypto.AEAD
  if(key != NULL)
  {
    KRML_HOST_FREE(key->st.prf.key);
    if(key->st.ak.tag) //  == FStar_Pervasives_Native_Some
      KRML_HOST_FREE(key->st.ak._0);
    KRML_HOST_FREE(key);
  }
  return 1;
}
