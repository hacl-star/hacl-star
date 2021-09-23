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
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "lib_intrinsics.h"


#include "Hacl_Kremlib.h"
#include "Hacl_Hash_SHA2.h"
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
  
 This code is not side-channel resistant.
  
 Input: pub(lic)Key: uint8[64]. 
  
 Output: bool, where 0 stands for the public key to be correct with respect to SP 800-56A:  
 Verify that the public key is not the “point at infinity”, represented as O. 
 Verify that the affine x and y coordinates of the point represented by the public key are in the range [0, p – 1] where p is the prime defining the finite field. 
 Verify that y2 = x3 + ax + b where a and b are the coefficients of the curve equation. 
 Verify that nQ = O (the point at infinity), where n is the order of the curve and Q is the public key point.
  
 The last extract is taken from : https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/
*/
bool Hacl_P256_verify_q_public(uint8_t *pubKey);

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
bool Hacl_P256_verify_q_private(uint8_t *pubKey);

/*
 There and further we introduce notions of compressed point and not compressed point. 
  
 We denote || as byte concatenation. 
  
 A compressed point is a point representaion as follows: (0x2 + y % 2) || x.
  
 A not Compressed point is a point representation as follows: 0x4 || x || y.

  
 
 Input: a point in not compressed form (uint8[65]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_not_compressed_form_p256(uint8_t *b, uint8_t *result);

/*
 Input: a point in compressed form (uint8[33]), 
 result: uint8[64] (internal point representation).
  
 Output: bool, where true stands for the correct decompression.
 
*/
bool Hacl_P256_decompression_compressed_form_p256(uint8_t *b, uint8_t *result);

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[65]).
*/
void Hacl_P256_compression_not_compressed_form_p256(uint8_t *b, uint8_t *result);

/*
 Input: a point buffer (internal representation: uint8[64]), 
 result: a point in not compressed form (uint8[33]).
*/
void Hacl_P256_compression_compressed_form_p256(uint8_t *b, uint8_t *result);

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_i_ml(uint8_t *result, uint8_t *scalar);

/*
 Input: result: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_i_radix(uint8_t *result, uint8_t *scalar);

uint64_t Hacl_P256_ecp384dh_i(uint8_t *result, uint8_t *scalar);

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_r_public_ml(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[64], 
 pub(lic)Key: uint8[64], 
 scalar: uint8[32].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp256dh_r_public_radix(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

uint64_t Hacl_P256_ecp256dh_r_private_ml(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

uint64_t Hacl_P256_ecp256dh_r_private_radix(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

/*
 This code is not side channel resistant on pub_key. 
 Input: result: uint8[96], 
 pub(lic)Key: uint8[96], 
 scalar: uint8[48].
  
 Output: uint64, where 0 stands for the correct key generation. All the other values mean that an error has occurred. 
  
*/
uint64_t Hacl_P256_ecp384dh_r(uint8_t *result, uint8_t *pubKey, uint8_t *scalar);

/*
Other exposed primitives 
 
Complete point addition.
Not side-channel resistant
*/
void Hacl_P256_point_add_out(uint64_t *p, uint64_t *q, uint64_t *result);

/*
Point inverse
*/
void Hacl_P256_point_inv(uint64_t *p, uint64_t *result);

/*
Moves a point to correct endian form + uint64
*/
void Hacl_P256_point_toForm(uint8_t *i, uint64_t *o);

/*
Moves a point from correct endian form + uint8
*/
void Hacl_P256_point_fromForm(uint64_t *i, uint8_t *o);

/*
Moves a point to domain
*/
void Hacl_P256_point_toDomain(uint64_t *p, uint64_t *result);

/*
From domain + to affine
*/
void Hacl_P256_point_norm(uint64_t *p, uint64_t *result);


#define __Hacl_P256_H_DEFINED
#endif
