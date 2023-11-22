/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
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


#ifndef __Hacl_NaCl_H
#define __Hacl_NaCl_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "Hacl_Salsa20.h"
#include "Hacl_MAC_Poly1305.h"
#include "Hacl_Curve25519_51.h"

/**
Encrypt a message with a key and nonce.

Note: `c` and `m` can point to the same memory for in-place encryption.

@param c Pointer to `mlen` bytes where the ciphertext is written to.
@param tag Pointer to 16 (tag length) bytes where the authentication tag is written to.
@param m Pointer to `mlen` bytes where the message is read from.
@param mlen Length of message.
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
uint32_t
Hacl_NaCl_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

/**
Verify and decrypt a ciphertext produced with `Hacl_NaCl_crypto_secretbox_detached`.

Note: `m` and `c` can point to the same memory for in-place decryption.

@param m Pointer to `mlen` bytes where the message is written to.
@param c Pointer to `mlen` bytes where the ciphertext is read from.
@param tag Pointer to 16 (tag length) bytes where the authentication tag is read from.
@param mlen Length of message (and ciphertext).
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
uint32_t
Hacl_NaCl_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

/**
Encrypt a message with a key and nonce.

@param c Pointer to 16 (tag length) + `mlen` bytes where the ciphertext is written to.
@param m Pointer to `mlen` bytes where the message is read from.
@param mlen Length of message.
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
uint32_t
Hacl_NaCl_crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint32_t mlen, uint8_t *n, uint8_t *k);

/**
Verify and decrypt a ciphertext produced with `crypto_secretbox_easy`.

@param m Pointer to `mlen` bytes where the message is written to.
@param c Pointer to `clen` bytes where the ciphertext is read from. The authentication tag must be included.
@param clen Length of ciphertext.
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
uint32_t
Hacl_NaCl_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
);

/**
Compute a shared secret key given a public key and secret key.

@param k Pointer to 32 (`crypto_box_BEFORENMBYTES`) bytes of memory where the shared secret is written to.
@param pk Pointer to 32 bytes of memory where **their** public key is read from.
@param sk Pointer to 32 bytes of memory where **my** secret key is read from.
*/
uint32_t Hacl_NaCl_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk);

/**
See `crypto_box_detached`.
*/
uint32_t
Hacl_NaCl_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

/**
Encrypt a message using the recipient's public key, the sender's secret key, and a nonce.

@param c Pointer to `mlen` bytes of memory where the ciphertext is written to.
@param tag Pointer to 16 (tag length) bytes of memory where the authentication tag is written to.
@param m Pointer to `mlen` bytes of memory where the message is read from.
@param mlen Length of the message.
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where **their** public key is read from.
@param sk Pointer to 32 bytes of memory where **my** secret key is read from.
*/
uint32_t
Hacl_NaCl_crypto_box_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

/**
See `crypto_box_open_detached`.
*/
uint32_t
Hacl_NaCl_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

/**
Verify and decrypt a ciphertext produced by `crypto_box_detached`.

@param m Pointer to `mlen` bytes of memory where the decrypted message is written to.
@param c Pointer to `mlen` bytes of memory where the ciphertext is read from. Note: the ciphertext must include the tag.
@param tag Pointer to 16 (tag length) bytes of memory where the authentication tag is read from.
@param mlen Length of the message (and ciphertext).
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where the public key of the sender is read from.
@param sk Pointer to 32 bytes of memory where the secret key of the recipient is read from.
*/
uint32_t
Hacl_NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

/**
See `crypto_box_easy`.
*/
uint32_t
Hacl_NaCl_crypto_box_easy_afternm(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);

/**
Encrypt a message using the recipient's public key, the sender's secret key, and a nonce.

@param c Pointer to 16 (tag length) + `mlen` bytes of memory where the authentication tag and ciphertext is written to.
@param m Pointer to `mlen` bytes of memory where the message is read from.
@param mlen Length of the message.
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where the public key of the recipient is read from.
@param sk Pointer to 32 bytes of memory where the secret key of the sender is read from.
*/
uint32_t
Hacl_NaCl_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

/**
See `crypto_box_open_easy`.
*/
uint32_t
Hacl_NaCl_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
);

/**
Verify and decrypt a ciphertext produced by `crypto_box_easy`.

@param m Pointer to `clen` - 16 (tag length) bytes of memory where the decrypted message is written to.
@param c Pointer to `clen` bytes of memory where the ciphertext is read from. Note: the ciphertext must include the tag.
@param clen Length of the ciphertext.
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where the public key of the sender is read from.
@param sk Pointer to 32 bytes of memory where the secret key of the recipient is read from.
*/
uint32_t
Hacl_NaCl_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_NaCl_H_DEFINED
#endif
