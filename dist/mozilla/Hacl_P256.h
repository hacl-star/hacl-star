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

#include "lib_intrinsics.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include <stdbool.h>

#ifndef __Hacl_P256_H
#define __Hacl_P256_H

#include "Hacl_Kremlib.h"
#include "Hacl_Hash_Hacl_HKDF_Hacl_HMAC_Hacl_HMAC_DRBG.h"
#include "Hacl_Spec.h"


/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
  priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
uint64_t
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
  priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
uint64_t
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
  priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order.
*/
uint64_t
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
 Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
  priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: uint64, where 0 stands for the correct signature generation. All the other values mean that an error has occurred. 
  
 The private key and the nonce are expected to be less than the curve order. 
  
 The message m is expected to be hashed by a strong hash function, the lenght of the message is expected to be 32 bytes and more.
*/
uint64_t
Hacl_P256_ecdsa_sign_p256_without_hash(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/*
This code is not side-channel resistant.
  
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
This code is not side-channel resistant.
  
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
This code is not side-channel resistant.
  
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
This code is not side-channel resistant.
  
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

/*
 Public key verification function. 
  
 Input: pub(lic)Key: uint8[64]. 
  
 Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A: 
  
 Verify that the public key is not the “point at infinity”, represented as O.
  
 Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field.
  
 Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation.
  
 Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  
 The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
 
*/
bool Hacl_P256_verify_q(uint8_t *pubKey);

/*
 There and further we introduce notions of compressed point and not compressed point. 
  
 We denote || as byte concatenation. 
  
 A compressed point is a point representaion as follows: (0x2 + y % 2) || x.
  
 A not Compressed point is a point representation as follows: 0x4 || x || y.

  
 
 
 

Input: a point in not compressed form (uint8[65]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_not_compressed_form(uint8_t *b, uint8_t *result);

/*
 Input: a point in compressed form (uint8[33]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_compressed_form(uint8_t *b, uint8_t *result);

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[65]).
*/
void Hacl_P256_compression_not_compressed_form(uint8_t *b, uint8_t *result);

/*
 Input: a point buffer (internal representation: uint8[64]),
  
 result: a point in not compressed form (uint8[33]).
*/
void Hacl_P256_compression_compressed_form(uint8_t *b, uint8_t *result);

/*
 The function takes an arbitraty 32 bytes buffer and reduces it to contain a value that is less than the curve order.
  
 Input: x: uint8[32],
  
 result: uint8[32], such that by the end of the function the value stored in the buffer result equal to the value stored in the buffer x modulo curveOrder.
*/
void Hacl_P256_reduction_8_32(uint8_t *x, uint8_t *result);

/*
 Input: result: uint8[64],
  
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_i(uint8_t *result, uint8_t *scalar);

/*
  This code is not side channel resistant on pub_key. 
  
 Input: result: uint8[64],
  
 pub(lic)Key: uint8[64],
  
 scalar: uint8[64].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

#define __Hacl_P256_H_DEFINED
#endif
