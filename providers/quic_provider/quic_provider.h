#ifndef __QUIC_PROVIDER
#define __QUIC_PROVIDER

#include <sys/types.h>
#include <stdlib.h>
#include <stdint.h>

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

// Helper function to determine the buffer overhead for encryption.
#define quic_crypto_tag_length(pKey) 16

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
int MITLS_CALLCONV quic_derive_initial_secrets(/*out*/ quic_secret *client_in, /*out*/ quic_secret *server_in, const unsigned char *con_id, size_t con_id_len, const unsigned char *salt, size_t salt_len);
int MITLS_CALLCONV quic_crypto_tls_derive_secret(/*out*/ quic_secret *derived, const quic_secret *secret, const char *label);
int MITLS_CALLCONV quic_crypto_derive_key(/*out*/quic_key **key, const quic_secret *secret);

// Low-level function to create an AEAD instance from a raw key and IV
// Note that iv is always 12 bytes and key is 16 bytes for AES-128
// and 32 bytes for AES-256 and ChaCha20.
// Using quic_crypto_derive_key is recommended over quic_crypto_create
// The created key must be freed with quic_crypto_free_key
int MITLS_CALLCONV quic_crypto_create(quic_key **key, mitls_aead alg, const unsigned char *raw_key, const unsigned char *iv, const unsigned char *pne_key);

// AEAD-encrypts plain with additional data ad, using counter sn,
// writing plain_len + 16 bytes to the output cipher. The input and
// output buffer must not overlap.
//
// The packet number sn is internally combined with the static IV
// to form the 12-byte AEAD IV
//
// NB: NOT DOT ENCRYPT TWICE WITH THE SAME KEY AND SN
int MITLS_CALLCONV quic_crypto_encrypt(quic_key *key, /*out*/ unsigned char *cipher, uint64_t sn, const unsigned char *ad, uint32_t ad_len, const unsigned char *plain, uint32_t plain_len);

// AEAD-decrypts cipher and authenticate additional data ad, using
// counter; when successful, writes cipher_len - 16 bytes to the
// output plain. The input and output buffers must not overlap.
int MITLS_CALLCONV quic_crypto_decrypt(quic_key *key, /*out*/ unsigned char *plain, uint64_t sn, const unsigned char *ad, uint32_t ad_len, const unsigned char *cipher, uint32_t cipher_len);

// Compute a one time pad to obfuscate the packet number from the encrypted packet contents
// *sample must point to the start of the encrypted packet payload
// 5 bytes will be written to *mask
int MITLS_CALLCONV quic_crypto_hp_mask(quic_key *key, const unsigned char *sample, unsigned char *mask);

// Keys allocated by quic_crypto_derive_key and quic_crypto_create must be freed
int MITLS_CALLCONV quic_crypto_free_key(quic_key *key);

// Auxiliary crypto functions, possibly useful elsewhere in QUIC.
// Hash, HMAC and HKDF only suport SHA256, SHA384, and SHA512
int MITLS_CALLCONV quic_crypto_hash(quic_hash a, /*out*/ unsigned char *hash, const unsigned char *data, size_t data_len);
int MITLS_CALLCONV quic_crypto_hmac(quic_hash a, /*out*/ unsigned char *mac, const unsigned char *key, uint32_t key_len, const unsigned char *data, uint32_t data_len);

int MITLS_CALLCONV quic_crypto_hkdf_extract(quic_hash a, /*out*/ unsigned char *prk, const unsigned char *salt, uint32_t salt_len, const unsigned char *ikm, uint32_t ikm_len);
int MITLS_CALLCONV quic_crypto_hkdf_expand(quic_hash a, /*out*/ unsigned char *okm, uint32_t okm_len, const unsigned char *prk, uint32_t prk_len, const unsigned char *info, uint32_t info_len);
int MITLS_CALLCONV quic_crypto_hkdf_label(quic_hash a, /*out*/ unsigned char *info, /*out*/ size_t *info_len, const char *label, uint16_t out_len);

#endif /* end of include guard:  */
