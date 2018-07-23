/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
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
/**************************************************************************
 * WARNING:
 * This file is handwritten and MUST be reviewed properly before use
 **************************************************************************/

#include <inttypes.h>

#define crypto_auth_BYTES 32
#define crypto_auth_KEYBYTES 32

#define crypto_box_PUBLICKEYBYTES 32
#define crypto_box_SECRETKEYBYTES 32
#define crypto_box_BEFORENMBYTES 32
#define crypto_box_NONCEBYTES 24
#define crypto_box_ZEROBYTES 32
#define crypto_box_BOXZEROBYTES 16

/* #define crypto_core_OUTPUTBYTES crypto_core_salsa20_OUTPUTBYTES */
/* #define crypto_core_INPUTBYTES crypto_core_salsa20_INPUTBYTES */
/* #define crypto_core_KEYBYTES crypto_core_salsa20_KEYBYTES */
/* #define crypto_core_CONSTBYTES crypto_core_salsa20_CONSTBYTES */

#define crypto_hash_BYTES 64

#define crypto_onetimeauth_BYTES 16
#define crypto_onetimeauth_KEYBYTES 32

#define crypto_scalarmult_BYTES 32
#define crypto_scalarmult_SCALARBYTES 32

#define crypto_secretbox_NONCEBYTES = 24
#define crypto_secretbox_KEYBYTES   = 32
#define crypto_secretbox_MACBYTES   = 16
#define crypto_secretbox_ZEROBYTES 32
#define crypto_secretbox_BOXZEROBYTES 16

#define crypto_sign_BYTES 64
#define crypto_sign_PUBLICKEYBYTES 32
#define crypto_sign_SECRETKEYBYTES 64

#define crypto_stream_KEYBYTES 32
#define crypto_stream_NONCEBYTES 24


/* Base primitives */

void chacha20(uint8_t *output, uint8_t *plain, uint32_t plain_len, uint8_t *key, uint8_t *nonce, uint32_t ctr);

uint32_t aead_chacha20_poly1305_encrypt(uint8_t *cipher,  uint8_t *mac,  uint8_t *msg, uint32_t msg_len,  uint8_t *aad,  uint32_t aad_len,  uint8_t *key,  uint8_t *nonce);

uint32_t aead_chacha20_poly1305_decrypt(uint8_t *msg, uint8_t *cipher,  uint32_t msg_len,  uint8_t *mac,  uint8_t *aad,  uint32_t aad_len,  uint8_t *key,  uint8_t *nonce);


/* NaCl-like API */

int crypto_auth(uint8_t *output, const uint8_t *input, uint64_t input_len,const uint8_t *key);

int crypto_auth_verify(const uint8_t *tag, const uint8_t *input, uint64_t input_len, const uint8_t *key);


int crypto_box(uint8_t *cipher, const uint8_t *message, uint64_t msg_len, const uint8_t *nonce,  const uint8_t *pk, const uint8_t *sk);

int crypto_box_open(uint8_t *msg, const uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *pk, const uint8_t *sk);

int crypto_box_keypair(uint8_t *pk, uint8_t *sk);

int crypto_box_beforenm(uint8_t *k, const uint8_t *pk, const uint8_t *sk) __attribute__ ((warn_unused_result));

int crypto_box_afternm(uint8_t *cipher, const uint8_t *msg, uint64_t msg_len, const uint8_t *nonce, const uint8_t *key);

int crypto_box_open_afternm(uint8_t *msg, const uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key);


// int crypto_core(uint8_t *, const uint8_t *, const uint8_t *, const uint8_t *);


int crypto_hash(uint8_t *output, const uint8_t *input, uint64_t input_len);


int crypto_onetimeauth(uint8_t *output, const uint8_t *input, uint64_t input_len, const uint8_t *key);

int crypto_onetimeauth_verify(const uint8_t *tag, const uint8_t *input, uint64_t input_len, const uint8_t *key);


int crypto_scalarmult_base(uint8_t *q, const uint8_t *n);

int crypto_scalarmult(uint8_t *q, const uint8_t *n, const uint8_t *p) __attribute__ ((warn_unused_result));


int crypto_secretbox(uint8_t *cipher, const uint8_t *msg, uint64_t msg_len, const uint8_t *nonce, const uint8_t *key);

int crypto_secretbox_open(uint8_t *msg, const uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key);


int crypto_sign(uint8_t *signed_msg, uint64_t *signed_len, const uint8_t *msg, uint64_t msg_len, const uint8_t *sk);

int crypto_sign_open(uint8_t *unsigned_msg, uint64_t *unsigned_msg_len, const uint8_t *msg, uint64_t msg_len, const uint8_t *pk);

int crypto_sign_keypair(uint8_t *pk, uint8_t *sk);

int crypto_sign_secret_to_public(uint8_t *pk, uint8_t *sk);


int crypto_stream(uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key);

int crypto_stream_xor(uint8_t *cipher, const uint8_t *msg, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key);


/* Other API (mix between NaCl's original API and LibSodium's API) */

/* int crypto_box_easy_afternm(uint8_t *c, const uint8_t *m, */
/*                             uint64_t mlen, const uint8_t *n, */
/*                             const uint8_t *k); */

/* int crypto_box_open_easy_afternm(uint8_t *m, const uint8_t *c, */
/*                                  uint64_t clen, const uint8_t *n, */
/*                                  const uint8_t *k) */
/*             __attribute__ ((warn_unused_result)); */

/* int crypto_box_easy(uint8_t *c, const uint8_t *m, */
/*                     uint64_t mlen, const uint8_t *n, */
/*                     const uint8_t *pk, const uint8_t *sk) */
/*             __attribute__ ((warn_unused_result)); */

/* int crypto_box_open_easy(uint8_t *m, const uint8_t *c, */
/*                          uint64_t clen, const uint8_t *n, */
/*                          const uint8_t *pk, const uint8_t *sk) */
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
