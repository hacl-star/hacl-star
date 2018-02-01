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

// mitlsffi defines quic_secret: the type of exported secrets

// Calling convention: all functions in this library return
// 1 on success and 0 on failure.

// Unlike secrets, AEAD keys are kept abstract; they hide the
// negotiated encryption algorithm and its expanded key materials;
// they are allocated internally by quic_crypto_derive_key and must be
// explicitly freed. Each key is used only for encrypting or only for
// decrypting.

typedef struct quic_key quic_key;

// Main functions for QUIC AEAD keying. Encryption keys for AEAD are
// derived as follows (see quic-tls#4 section 5)
//
// (1) get exporter secret from TLS (optional early, then main secret)
//
// (2) derive encryption secrets from the exporter secrets:
//
//     early_secret, "EXPORTER-QUIC 0-RTT Secret"
//     main_secret, "EXPORTER-QUIC client 1-RTT Secret"
//     main_secret, "EXPORTER-QUIC server 1-RTT Secret"
//
// (3) derive an encryption key from each encryption secret.
//
// (4) optionally derive the next encryption secret from the current
//     ones (to be use for later rekeying, resuming from step 3)
//
// (5) erase all secrets used for derivation.

// con_id must be 8 bytes, salt must be the version-specific 20 bytes initial salt
int quic_crypto_derive_plaintext_secrets(quic_secret *client_cleartext, quic_secret *server_cleartext, const char *con_id, const char *salt);
int quic_crypto_tls_derive_secret(/*out*/ quic_secret *derived, const quic_secret *secret, const char *label);
int quic_crypto_derive_key(/*out*/quic_key **key, const quic_secret *secret);

// AEAD-encrypts plain with additional data ad, using counter sn,
// writing plain_len + 16 bytes to the output cipher. The input and
// output buffer must not overlap.
//
// The packet number sn is internally combined with the static IV
// to form the 12-byte AEAD IV
//
// NB: NOT DOT ENCRYPT TWICE WITH THE SAME KEY AND SN
//
int quic_crypto_encrypt(quic_key *key, /*out*/ char *cipher, uint64_t sn, const char *ad, uint32_t ad_len, const char *plain, uint32_t plain_len);

// AEAD-decrypts cipher and authenticate additional data ad, using
// counter; when successful, writes cipher_len - 16 bytes to the
// output plain. The input and output buffers must not overlap.
//
int quic_crypto_decrypt(quic_key *key, /*out*/ char *plain, uint64_t sn, const char *ad, uint32_t ad_len, const char *cipher, uint32_t cipher_len);

// Keys allocated by quic_crypto_derive_key must be freed
int quic_crypto_free_key(quic_key *key);

// Auxiliary crypto functions, possibly useful elsewhere in QUIC.
// Hash, HMAC and HKDF only suport SHA256, SHA384, and SHA512
int quic_crypto_hash(quic_hash a, /*out*/ char *hash, const char *data, size_t data_len);
int quic_crypto_hmac(quic_hash a, /*out*/ char *mac, const char *key, uint32_t key_len, const char *data, uint32_t data_len);
int quic_crypto_hkdf_extract(quic_hash a, /*out*/ char *prk, const char *salt, uint32_t salt_len, const char *ikm, uint32_t ikm_len);
int quic_crypto_hkdf_expand(quic_hash a, /*out*/ char *okm, uint32_t okm_len, const char *prk, uint32_t prk_len, const char *info, uint32_t info_len);

#endif /* end of include guard:  */
