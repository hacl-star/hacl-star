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


#ifndef __Hacl_K256_ECDSA_H
#define __Hacl_K256_ECDSA_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Krmllib.h"
#include "Hacl_K256_PrecompTable.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Bignum_K256.h"
#include "Hacl_Bignum_Base.h"
#include "lib_intrinsics.h"
/*******************************************************************************
  Verified C library for ECDSA signing and verification on the secp256k1 curve.

  For the comments on low-S normalization (or canonical lowest S value), see:
    • https://en.bitcoin.it/wiki/BIP_0062
    • https://yondon.blog/2019/01/01/how-not-to-use-ecdsa/
    • https://eklitzke.org/bitcoin-transaction-malleability

  For example, bitcoin-core/secp256k1 *always* performs low-S normalization.

*******************************************************************************/


/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` and `private_key` < the order of the curve
    • 0 < `nonce` and `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_sign_hashed_msg`.

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether a public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(uint8_t *m, uint8_t *public_key, uint8_t *signature);

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_verify_hashed_msg`.

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
);

/**
Compute canonical lowest S value for `signature` (R || S).

  The function returns `true` for successful normalization of S and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(uint8_t *signature);

/**
Check whether `signature` (R || S) is in canonical form.

  The function returns `true` if S is low-S normalized and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
*/
bool Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(uint8_t *signature);

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid values:
    • 0 < `private_key` and `private_key` < the order of the curve
    • 0 < `nonce` and `nonce` < the order of the curve
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_sign_hashed_msg`.

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_hashed_msg` if needed.

  The function also checks whether a public key (x || y) is valid:
    • 0 < x and x < prime
    • 0 < y and y < prime
    • (x, y) is on the curve
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
  uint8_t *msgHash,
  uint8_t *public_key,
  uint8_t *signature
);

/**
Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_verify_hashed_msg`.

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_sha256` if needed.
*/
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
);

/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the secp256k1 curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/


/**
Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is valid point.
*/
bool Hacl_K256_ECDSA_public_key_uncompressed_to_raw(uint8_t *pk_raw, uint8_t *pk);

/**
Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
void Hacl_K256_ECDSA_public_key_uncompressed_from_raw(uint8_t *pk, uint8_t *pk_raw);

/**
Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is valid point.
*/
bool Hacl_K256_ECDSA_public_key_compressed_to_raw(uint8_t *pk_raw, uint8_t *pk);

/**
Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point.
*/
void Hacl_K256_ECDSA_public_key_compressed_from_raw(uint8_t *pk, uint8_t *pk_raw);

#if defined(__cplusplus)
}
#endif

#define __Hacl_K256_ECDSA_H_DEFINED
#endif
