/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
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


#ifndef __Hacl_P256_H
#define __Hacl_P256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "Hacl_Krmllib.h"
#include "Hacl_Hash_SHA2.h"
#include "evercrypt_targetconfig.h"
#include "lib_intrinsics.h"
#include "libintvector.h"

/*******************************************************************************

ECDSA and ECDH functions over the P-256 NIST curve.

This module implements signing and verification, key validation, conversions
between various point representations, and ECDH key agreement.

*******************************************************************************/

/**************/
/* Signatures */
/**************/

/*
  Per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/

/*
Hash the message with SHA2-256, then sign the resulting digest with the P256 signature function.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
Hash the message with SHA2-384, then sign the resulting digest with the P256 signature function.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
Hash the message with SHA2-512, then sign the resulting digest with the P256 signature function.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
P256 signature WITHOUT hashing first.

This function is intended to receive a hash of the input. For convenience, we
recommend using one of the hash-and-sign combined functions above.

The argument `m` MUST be at least 32 bytes (i.e. `mLen >= 32`).

NOTE: The equivalent functions in OpenSSL and Fiat-Crypto both accept inputs
smaller than 32 bytes. These libraries left-pad the input with enough zeroes to
reach the minimum 32 byte size. Clients who need behavior identical to OpenSSL
need to perform the left-padding themselves.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_sign_p256_without_hash(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);


/****************/
/* Verification */
/****************/

/*
  Verify a message signature. These functions internally validate the public key using validate_public_key.
*/


/*
 The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/*
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/*
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/*
 The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification.
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
bool
Hacl_P256_ecdsa_verif_without_hash(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);


/******************/
/* Key validation */
/******************/


/*
Validate a public key.

  
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: pub(lic)Key: uint8[64]. 
  
 Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:  
 Verify that the public key is not the “point at infinity”, represented as O. 
 Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field. 
 Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation. 
 Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  
 The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_validate_public_key(uint8_t *pubKey);

/*
Validate a private key, e.g. prior to signing.

Input: scalar: uint8[32].
  
 Output: bool, where true stands for the scalar to be more than 0 and less than order.
*/
bool Hacl_P256_validate_private_key(uint8_t *x);


/*****************************************/
/* Point representations and conversions */
/*****************************************/

/*
  Elliptic curve points have 2 32-byte coordinates (x, y) and can be represented in 3 ways:

  - "raw" form (64 bytes): the concatenation of the 2 coordinates, also known as "internal"
  - "compressed" form (33 bytes): first the sign byte of y (either 0x02 or 0x03), followed by x
  - "uncompressed" form (65 bytes): first a constant byte (always 0x04), followed by the "raw" form

  For all of the conversation functions below, the input and output MUST NOT overlap.
*/


/*
Convert 65-byte uncompressed to raw.

The function errors out if the first byte is incorrect, or if the resulting point is invalid.

  
 
 Input: a point in not compressed form (uint8[65]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_uncompressed_to_raw(uint8_t *b, uint8_t *result);

/*
Convert 33-byte compressed to raw.

The function errors out if the first byte is incorrect, or if the resulting point is invalid.

Input: a point in compressed form (uint8[33]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_compressed_to_raw(uint8_t *b, uint8_t *result);

/*
Convert raw to 65-byte uncompressed.

This function effectively prepends a 0x04 byte.

Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[65]).
*/
void Hacl_P256_raw_to_uncompressed(uint8_t *b, uint8_t *result);

/*
Convert raw to 33-byte compressed.

  Input: `b`, the pointer buffer in internal representation, of type `uint8[64]`
  Output: `result`, a point in compressed form, of type `uint8[33]`

*/
void Hacl_P256_raw_to_compressed(uint8_t *b, uint8_t *result);


/******************/
/* ECDH agreement */
/******************/

/*
Convert a private key into a raw public key.

This function performs no key validation.

  Input: `scalar`, the private key, of type `uint8[32]`.
  Output: `result`, the public key, of type `uint8[64]`.
  Returns:
  - `true`, for success, meaning the public key is not a point at infinity
  - `false`, otherwise.

  `scalar` and `result` MUST NOT overlap.
*/
bool Hacl_P256_dh_initiator(uint8_t *result, uint8_t *scalar);

/*
ECDH key agreement.

This function takes a 32-byte secret key, another party's 64-byte raw public
key, and computeds the 64-byte ECDH shared key.

This function ONLY validates the public key.

   The pub(lic)_key input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over this variable.
  
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: bool, where True stands for the correct key generation. False value means that an error has occurred (possibly the provided public key was incorrect or the result represents point at infinity). 
  
*/
bool Hacl_P256_dh_responder(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

#if defined(__cplusplus)
}
#endif

#define __Hacl_P256_H_DEFINED
#endif
