#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "Crypto_HKDF_Crypto_HMAC.h"
#include "Crypto_AEAD_Main_Crypto_Indexing.h"
#include "Crypto_Symmetric_Bytes.h"
#include "quic_provider.h"

#define DEBUG 0

// FIXME!!
#define Crypto_Symmetric_MAC_taglen 16

typedef struct quic_key {
  Crypto_AEAD_Invariant_aead_state st;
  Crypto_Indexing_id id;
  char static_iv[12];
} quic_key;

#if DEBUG
void dump(unsigned char buffer[], size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

void dump_secret(quic_secret *s)
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

int quic_crypto_hash(quic_hash a, /*out*/ char *hash, const char *data, size_t len){
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HMAC_agile_hash(CONVERT_ALG(a), hash, (char*)data, len);
  return 1;
}

int quic_crypto_hmac(quic_hash a, char *mac,
                     const char *key, uint32_t key_len,
                     const char *data, uint32_t data_len) {
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HMAC_hmac(CONVERT_ALG(a), mac, (uint8_t*)key, key_len, (uint8_t*)data, data_len);
  return 1;
}

int quic_crypto_hkdf_extract(quic_hash a, char *prk,
                             const char *salt, uint32_t salt_len,
                             const char *ikm, uint32_t ikm_len)
{
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HKDF_hkdf_extract(CONVERT_ALG(a), prk, (uint8_t*)salt, salt_len, (uint8_t*)ikm, ikm_len);
  return 1;
}

int quic_crypto_hkdf_expand(quic_hash a, char *okm, uint32_t olen, const char *prk, uint32_t prk_len, const char *info, uint32_t info_len)
{
  if(a < TLS_hash_SHA256) return 0;
  Crypto_HKDF_hkdf_expand(CONVERT_ALG(a), okm, (uint8_t*)prk, prk_len, (uint8_t*)info, info_len, olen);
  return 1;
}

// Use key_len = 0 for HASH("") context and hlen output
// Use key_len = k for no context and k length output
int quic_crypto_tls_label(quic_hash a, char *info, size_t *info_len, const char *label, uint16_t key_len)
{
  if(a < TLS_hash_SHA256) return 0;
  uint32_t hlen = (a == TLS_hash_SHA256 ? 32 :
    (a == TLS_hash_SHA384 ? 48 : 64));
  size_t label_len = strlen(label);
  if(label_len > 249) return 0;

  info[0] = key_len ? (key_len >> 8) : 0;
  info[1] = key_len ? (key_len & 255) : (char)hlen;
  info[2] = (char)(label_len + 6);
  memcpy(info+3, "tls13 ", 6);
  memcpy(info+9, label, label_len);

  if(key_len)
  {
    info[9 + label_len] = 0;
    *info_len = label_len + 10;
    return 1;
  }

  // Empty hash
  char *hash = alloca(hlen);
  if(!quic_crypto_hash(a, hash, label, 0)) return 0;

  info[9+label_len] = (char)hlen;
  memcpy(info + label_len + 10, hash, hlen);
  *info_len = label_len + 10 + hlen;
  return 1;
}

int quic_crypto_tls_derive_secret(quic_secret *derived, const quic_secret *secret, const char *label)
{
  uint32_t hlen = (secret->hash == TLS_hash_SHA256 ? 32 :
    (secret->hash == TLS_hash_SHA384 ? 48 : 64));
  char *tmp = alloca(hlen);
  char info[323] = {0};
  size_t info_len;

  if(!quic_crypto_tls_label(secret->hash, info, &info_len, label, 0))
    return 0;

  derived->hash = secret->hash;
  derived->ae = secret->ae;

#if DEBUG
  printf("Secret to expand <%s>:\n", label);
  dump_secret(secret);
#endif

  if(!quic_crypto_hkdf_expand(secret->hash, tmp, hlen,
        secret->secret, hlen, info, info_len))
    return 0;

#if DEBUG
  printf("Intermediate:\n");
  dump(tmp, hlen);
#endif

  if(!quic_crypto_tls_label(secret->hash, info, &info_len, "exporter", 0))
    return 0;

  if(!quic_crypto_hkdf_expand(secret->hash, derived->secret, hlen,
        tmp, hlen, info, info_len))
    return 0;

#if DEBUG
  printf("Derived:\n");
  dump_secret(derived);
#endif

  return 1;
}

int quic_derive_plaintext_secrets(quic_secret *client_cleartext, quic_secret *server_cleartext, const char *con_id, const char *salt)
{
  quic_secret s0;
  s0.hash = TLS_hash_SHA256;
  s0.ae = TLS_aead_AES_128_GCM;

  if(!quic_crypto_hkdf_extract(s0.hash, s0.secret, salt, 20, con_id, 8))
    return 0;

  quic_crypto_tls_derive_secret(client_cleartext, &s0, "QUIC client cleartext Secret");
  quic_crypto_tls_derive_secret(server_cleartext, &s0, "QUIC server cleartext Secret");

  return 1;
}

int quic_crypto_derive_key(/*out*/quic_key **k, const quic_secret *secret)
{
  quic_key *key = malloc(sizeof(quic_key));
  if(!(*k = key)) return 0;

  key->id = Crypto_Indexing_testId(secret->ae);

  uint32_t klen = (secret->ae == TLS_aead_AES_128_GCM ? 16 : 32);
  uint32_t slen = (secret->hash == TLS_hash_SHA256 ? 32 :
    (secret->hash == TLS_hash_SHA384 ? 48 : 64));

  char info[323] = {0};
  char dkey[32];
  size_t info_len;

  if(!quic_crypto_tls_label(secret->hash, info, &info_len, "key", klen))
    return 0;

  // HKDF-Expand-Label(Secret, "key", "", key_length)
  if(!quic_crypto_hkdf_expand(secret->hash, dkey, klen, secret->secret, slen, info, info_len))
    return 0;

  if(!quic_crypto_tls_label(secret->hash, info, &info_len, "iv", 12))
    return 0;

  if(!quic_crypto_hkdf_expand(secret->hash, key->static_iv, 12, secret->secret, slen, info, info_len))
    return 0;

#if DEBIG
   printf("KEY: "); dump(dkey, klen);
   printf("IV: "); dump(key->static_iv, 12);
#endif

  key->st = Crypto_AEAD_Main_coerce(key->id, (uint8_t*)dkey);
  return 1;
}

void sn_to_iv(char *iv, uint64_t sn)
{
  for(int i = 4; i < 12; i++)
    iv[i] ^= (sn >> (88-(i<<3))) & 255;
}

int quic_crypto_encrypt(quic_key *key, char *cipher, uint64_t sn, const char *ad, uint32_t ad_len, const char *plain, uint32_t plain_len)
{
  char iv[12];
  memcpy(iv, key->static_iv, 12);
  sn_to_iv(iv, sn);

  FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128(12, iv);
  Crypto_AEAD_Main_encrypt(key->id, key->st, n, ad_len, (uint8_t*)ad, plain_len, (uint8_t*)plain, cipher);

#if DEBUG
  printf("ENCRYPT\nIV="); dump(iv, 12);
  printf("STATIC="); dump(key->static_iv, 12);
  printf("AD="); dump(ad, ad_len);
  printf("PLAIN="); dump(plain, plain_len);
  printf("CIPHER="); dump(cipher, plain_len + 16);
#endif

  return 1;
}

int quic_crypto_decrypt(quic_key *key, char *plain, uint64_t sn, const char *ad, uint32_t ad_len, const char *cipher, uint32_t cipher_len)
{
  char iv[12];
  memcpy(iv, key->static_iv, 12);
  sn_to_iv(iv, sn);

  if(cipher_len < Crypto_Symmetric_MAC_taglen)
    return 0;

  FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128(12, iv);
  uint32_t plain_len = cipher_len - Crypto_Symmetric_MAC_taglen;
  int r = Crypto_AEAD_Main_decrypt(key->id, key->st, n, ad_len, (uint8_t*)ad, plain_len, plain, (uint8_t*)cipher);

#if DEBUG
  printf("DECRYPT %s\nIV=", r?"OK":"BAD"); dump(iv, 12);
  printf("STATIC="); dump(key->static_iv, 12);
  printf("AD="); dump(ad, ad_len);
  printf("CIPHER="); dump(cipher, cipher_len);
  printf("PLAIN="); dump(plain, plain_len);
#endif

  return r;
}

int quic_crypto_free_key(quic_key *key)
{
  // ADL: the PRF stats is allocated with Buffer.screate
  // TODO switch to caller allocated style in Crypto.AEAD
  if(key && key->st.prf.key)
    free(key->st.prf.key);

  free(key);
  return 1;
}

