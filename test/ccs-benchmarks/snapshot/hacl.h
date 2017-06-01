#include "kremlib.h"

/* API file for HACL* cryptographic primitives */

/* X25519 ECDH computation primitive.
   Takes:
   - secret: a 32-bytes private key
   - point: a public value, either the X25519 basepoint (uint8_t basepoint[32] = {9}) or the other parties 32-bytes public key
   Returns:
   - stores the result of the computation in out */
void curve25519_scalarmult(uint8_t *out, uint8_t *secret, uint8_t *point);

/* Chacha20 cipher primitive.
   Takes:
   - plain: the plaintext
   - plain_len: the plaintext length
   - key: a 32-bytes private key
   - nonce: a 12-bytes nonce
   - ctr: a counter - WARNING the nonce/ctr combination must never be used more than once per key
   Stores:
   - output: the Chacha20 stream XORed with the content of plain */
void
chacha20(
         uint8_t *output,
         uint8_t *plain,
         uint32_t plain_len,
         uint8_t *key,
         uint8_t *nonce,
         uint32_t ctr
         );

/* Salsa20 cipher primitive.
   Takes:
   - plain: the plaintext
   - plain_len: the plaintext length
   - key: a 32-bytes private key
   - nonce: a 8-bytes nonce
   - ctr: a counter - WARNING the nonce/ctr combination must never be used more than once per key
   Stores:
   - output: the Salsa20 stream XORed with the content of plain
 */
void
salsa20(
        uint8_t *output,
        uint8_t *plain,
        uint32_t len,
        uint8_t *key,
        uint8_t *nonce,
        uint64_t ctr
        );


/* Poly1305 MAC primitive.
   Takes:
   - input: the input to be MACed
   - input_len: the length of the input
   - key: a private key
   Stores:
   - output: the 16-bytes of the MACed input
 */
void
poly1305_onetimeauth(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key);

/* IETF AEAD Chacha20 Poly1305 encrypt construction.
   Takes:
   - msg: the message to be encrypted then MACed
   - msg_len: the length of the message
   - aad: associated non-encrypted data
   - aad_len: associated non-encrypted data length
   - key:private key
   - nonce:nonce
   Stores:
   - cipher: the result of the encryption
   - mac: the result of the MAC */
uint32_t
aead_chacha20_poly1305_encrypt(
  uint8_t *cipher,
  uint8_t *mac,
  uint8_t *msg,
  uint32_t msg_len,
  uint8_t *aad,
  uint32_t aad_len,
  uint8_t *key,
  uint8_t *nonce
);

/* IETF AEAD Chacha20 Poly1305 encrypt construction.
   Takes:
   - cipher: the cipher to be decrypted
   - msg_len: the length of the message to retrieve
   - mac: the MAC to check the integrity
   - aad: associated non-encrypted data
   - aad_len: associated non-encrypted data length
   - key:private key
   - nonce:nonce
   Stores:
   - msg: the result of the decryption if the MAC verification succeeds */
uint32_t
aead_chacha20_poly1305__decrypt(
  uint8_t *msg,
  uint8_t *cipher,
  uint32_t msg_len,
  uint8_t *mac,
  uint8_t *aad,
  uint32_t aad_len,
  uint8_t *key,
  uint8_t *nonce
);

/* 
   Ed25519 Eddsa signature
   Takes:
   - secret: private key
   - msg: the message to sign
   - msg_len: the length of the message
   Stores:
   - signature: the signature of the message with the private key */
void ed25519_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t msg_len);

/* 
   Ed25519 Eddsa signature verification
   Takes:
   - public: other party public key
   - msg: the message that has been signed
   - msg_len: the length of the message
   - signature: the signature of the message
   Returns:
   - true: if the signature of the message is successfully verified
   - false otherwise */
bool ed25519_verify(uint8_t *public, uint8_t *msg, uint32_t msg_len, uint8_t *signature);

/*
  SHA2-512 Hash function
  Takes:
  - input: the data to be hashed
  - len: the length of the data to be hashed
  Stores:
  - hash: 64-bytes of the resulting hash
 */
void sha2_512_hash(uint8_t *hash, uint8_t *input, uint32_t len);


/* NaCl-like API */
int crypto_box_keypair(unsigned char *pk, unsigned char *sk);

int crypto_box_easy(unsigned char *c, const unsigned char *m,
                    unsigned long long mlen, const unsigned char *n,
                    const unsigned char *pk, const unsigned char *sk)
            __attribute__ ((warn_unused_result));

int crypto_box_open_easy(unsigned char *m, const unsigned char *c,
                         unsigned long long clen, const unsigned char *n,
                         const unsigned char *pk, const unsigned char *sk)
            __attribute__ ((warn_unused_result));

int crypto_box_beforenm(unsigned char *k, const unsigned char *pk,
                        const unsigned char *sk)
            __attribute__ ((warn_unused_result));

int crypto_box_easy_afternm(unsigned char *c, const unsigned char *m,
                            unsigned long long mlen, const unsigned char *n,
                            const unsigned char *k);

int crypto_box_open_easy_afternm(unsigned char *m, const unsigned char *c,
                                 unsigned long long clen, const unsigned char *n,
                                 const unsigned char *k)
            __attribute__ ((warn_unused_result));

int crypto_scalarmult_base(unsigned char *q, const unsigned char *n);

int crypto_scalarmult(unsigned char *q, const unsigned char *n,
                      const unsigned char *p)
            __attribute__ ((warn_unused_result));

uint32_t
crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
);

uint32_t
crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *k1
);

uint32_t
crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n1, uint8_t *k1);

uint32_t
crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t clen,
  uint8_t *n1,
  uint8_t *k1
);

uint32_t NaCl_crypto_box_beforenm(uint8_t *k1, uint8_t *pk, uint8_t *sk);

uint32_t
crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
);

uint32_t
crypto_box_detached(
  uint8_t *c,
  uint8_t *mac,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
crypto_box_easy_afternm(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n1, uint8_t *k1);

uint32_t
crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *pk,
  uint8_t *sk
);

uint32_t
crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *mac,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
);

uint32_t
crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint64_t mlen,
  uint8_t *n1,
  uint8_t *k1
);

/* 
   LibSodium specific AEAD curve25519xchacha20poly1305 construction
 */
crypto_box_curve25519xchacha20poly1305_beforenm
crypto_box_curve25519xchacha20poly1305_easy
crypto_box_curve25519xchacha20poly1305_easy_afternm
crypto_box_curve25519xchacha20poly1305_open_easy
crypto_box_curve25519xchacha20poly1305_open_easy_afternm
