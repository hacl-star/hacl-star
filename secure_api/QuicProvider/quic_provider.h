#ifndef __QUIC_PROVIDER
#define __QUIC_PROVIDER

#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "mitlsffi.h"

typedef struct quic_key quic_key;

int quic_crypto_hash(quic_hash a, /*out*/ char *hash, char *data, size_t len);
int quic_crypto_hmac(quic_hash a, /*out*/ char *mac, char *key, uint32_t key_len, char *data, uint32_t data_len);
int quic_crypto_hkdf_extract(quic_hash a, char *prk, char *salt, uint32_t salt_len, char *ikm, uint32_t ikm_len);
int quic_crypto_hkdf_expand(quic_hash a, char *okm, uint32_t olen, char *prk, uint32_t prk_len, char *info, uint32_t info_len);

int quic_crypto_derive_key(/*out*/quic_key **key, quic_secret *secret);
int quic_crypto_tls_derive_secet(quic_secret *derived, quic_secret *secret, char *label);
int quic_crypto_encrypt(quic_key *key, char *cipher, uint64_t sn, char *ad, uint32_t ad_len, char *plain, uint32_t plain_len);
int quic_crypto_decrypt(quic_key *key, char *plain, uint64_t sn, char *ad, uint32_t ad_len, char *cipher, uint32_t cipher_len);
int quic_crypto_free_key(quic_key *key);

#endif /* end of include guard:  */
