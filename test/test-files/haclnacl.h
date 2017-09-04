#include <inttypes.h>

/* NaCl-like API */
int crypto_onetimeauth(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key);

int crypto_onetimeauth_verify(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key);

int crypto_box_keypair(unsigned char *pk, unsigned char *sk);

int crypto_box_beforenm(unsigned char *k, const unsigned char *pk,
                        const unsigned char *sk)
            __attribute__ ((warn_unused_result));

int crypto_scalarmult_base(unsigned char *q, const unsigned char *n);

int crypto_scalarmult(unsigned char *q, const unsigned char *n,
                      const unsigned char *p)
            __attribute__ ((warn_unused_result));

int crypto_sign(uint8_t *signed_msg, long long unsigned int *signed_len, uint8_t *msg, uint64_t msg_len,
            uint8_t *sk);

int crypto_sign_open(uint8_t *unsigned_msg, long long unsigned int *unsigned_msg_len,
                     uint8_t *msg, uint64_t msg_len, uint8_t *pk);

int crypto_sign_keypair(uint8_t pk[32], uint8_t sk[32]);

int crypto_sign_secret_to_public(uint8_t *pk, uint8_t *sk);

int crypto_box(uint8_t *cipher, uint8_t *message, uint64_t msg_len, uint8_t *nonce,  uint8_t *pk, uint8_t *sk);

int crypto_box_open(uint8_t *msg, uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *pk, uint8_t *sk);

int crypto_box_afternm(uint8_t *cipher, uint8_t *msg, uint64_t msg_len, uint8_t *nonce, uint8_t *key);

int crypto_box_open_afternm(uint8_t *msg, uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *key);

int crypto_secretbox(uint8_t *cipher, uint8_t *msg, uint64_t msg_len, uint8_t *nonce, uint8_t *key);

int crypto_secretbox_open(uint8_t *msg, uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *key);

int crypto_stream(uint8_t *cipher, uint64_t cipher_len, uint8_t *nonce, uint8_t *key);

int crypto_stream_xor(uint8_t *cipher, uint8_t *msg, uint64_t cipher_len, uint8_t *nonce, uint8_t *key);

void chacha20(uint8_t *output, uint8_t *plain, uint32_t plain_len, uint8_t *key, uint8_t *nonce, uint32_t ctr);

uint32_t aead_chacha20_poly1305_encrypt(uint8_t *cipher,  uint8_t *mac,  uint8_t *msg, uint32_t msg_len,  uint8_t *aad,  uint32_t aad_len,  uint8_t *key,  uint8_t *nonce);

uint32_t aead_chacha20_poly1305_decrypt(uint8_t *msg, uint8_t *cipher,  uint32_t msg_len,  uint8_t *mac,  uint8_t *aad,  uint32_t aad_len,  uint8_t *key,  uint8_t *nonce);

/* Other API (mix between NaCl's original API and LibSodium's API) */

/* int crypto_box_easy_afternm(unsigned char *c, const unsigned char *m, */
/*                             unsigned long long mlen, const unsigned char *n, */
/*                             const unsigned char *k); */

/* int crypto_box_open_easy_afternm(unsigned char *m, const unsigned char *c, */
/*                                  unsigned long long clen, const unsigned char *n, */
/*                                  const unsigned char *k) */
/*             __attribute__ ((warn_unused_result)); */

/* int crypto_box_easy(unsigned char *c, const unsigned char *m, */
/*                     unsigned long long mlen, const unsigned char *n, */
/*                     const unsigned char *pk, const unsigned char *sk) */
/*             __attribute__ ((warn_unused_result)); */

/* int crypto_box_open_easy(unsigned char *m, const unsigned char *c, */
/*                          unsigned long long clen, const unsigned char *n, */
/*                          const unsigned char *pk, const unsigned char *sk) */
/*             __attribute__ ((warn_unused_result)); */

/* uint32_t */
/* crypto_box_detached_afternm( */
/*   uint8_t *c, */
/*   uint8_t *mac, */
/*   uint8_t *m, */
/*   uint64_t mlen, */
/*   uint8_t *n1, */
/*   uint8_t *k1 */
/* ); */

/* uint32_t */
/* crypto_box_detached( */
/*   uint8_t *c, */
/*   uint8_t *mac, */
/*   uint8_t *m, */
/*   uint64_t mlen, */
/*   uint8_t *n1, */
/*   uint8_t *pk, */
/*   uint8_t *sk */
/* ); */

/* uint32_t */
/* crypto_box_open_detached( */
/*   uint8_t *m, */
/*   uint8_t *c, */
/*   uint8_t *mac, */
/*   uint64_t mlen, */
/*   uint8_t *n1, */
/*   uint8_t *pk, */
/*   uint8_t *sk */
/* ); */

/* uint32_t */
/* crypto_box_open_detached_afternm( */
/*   uint8_t *m, */
/*   uint8_t *c, */
/*   uint8_t *mac, */
/*   uint64_t mlen, */
/*   uint8_t *n1, */
/*   uint8_t *k1 */
/* ); */

/* uint32_t */
/* crypto_secretbox_detached( */
/*   uint8_t *c, */
/*   uint8_t *mac, */
/*   uint8_t *m, */
/*   uint64_t mlen, */
/*   uint8_t *n1, */
/*   uint8_t *k1 */
/* ); */

/* uint32_t */
/* crypto_secretbox_open_detached( */
/*   uint8_t *m, */
/*   uint8_t *c, */
/*   uint8_t *mac, */
/*   uint64_t clen, */
/*   uint8_t *n1, */
/*   uint8_t *k1 */
/* ); */

/* uint32_t */
/* crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n1, uint8_t *k1); */

/* uint32_t */
/* crypto_secretbox_open_easy( */
/*   uint8_t *m, */
/*   uint8_t *c, */
/*   uint64_t clen, */
/*   uint8_t *n1, */
/*   uint8_t *k1 */
/* ); */
