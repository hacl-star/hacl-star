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


#ifndef __Hacl_RSAPSS_H
#define __Hacl_RSAPSS_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"


#include "Hacl_Spec.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Bignum_Base.h"

/* SNIPPET_START: Hacl_RSAPSS_rsapss_sign */

/**
Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  * Spec_Hash_Definitions_SHA2_256,
  * Spec_Hash_Definitions_SHA2_384, and
  * Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSAPSS_new_rsapss_load_skey`.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful.
*/
bool
Hacl_RSAPSS_rsapss_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
);

/* SNIPPET_END: Hacl_RSAPSS_rsapss_sign */

/* SNIPPET_START: Hacl_RSAPSS_rsapss_verify */

/**
Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param pkey Pointer to public key created by `Hacl_RSAPSS_new_rsapss_load_pkey`.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid.
*/
bool
Hacl_RSAPSS_rsapss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t saltLen,
  uint32_t sgntLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
);

/* SNIPPET_END: Hacl_RSAPSS_rsapss_verify */

/* SNIPPET_START: Hacl_RSAPSS_new_rsapss_load_pkey */

/**
Load a public key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`) is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value is read from.

@return Returns an allocated public key. Note: caller must take care to `free()` the created key.
*/
uint64_t
*Hacl_RSAPSS_new_rsapss_load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb);

/* SNIPPET_END: Hacl_RSAPSS_new_rsapss_load_pkey */

/* SNIPPET_START: Hacl_RSAPSS_new_rsapss_load_skey */

/**
Load a secret key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`) is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value is read from.

@return Returns an allocated secret key. Note: caller must take care to `free()` the created key.
*/
uint64_t
*Hacl_RSAPSS_new_rsapss_load_skey(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db
);

/* SNIPPET_END: Hacl_RSAPSS_new_rsapss_load_skey */

/* SNIPPET_START: Hacl_RSAPSS_rsapss_skey_sign */

/**
Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`) is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value is read from.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful.
*/
bool
Hacl_RSAPSS_rsapss_skey_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
);

/* SNIPPET_END: Hacl_RSAPSS_rsapss_skey_sign */

/* SNIPPET_START: Hacl_RSAPSS_rsapss_pkey_verify */

/**
Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`) is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value is read from.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid.
*/
bool
Hacl_RSAPSS_rsapss_pkey_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint8_t *nb,
  uint8_t *eb,
  uint32_t saltLen,
  uint32_t sgntLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
);

/* SNIPPET_END: Hacl_RSAPSS_rsapss_pkey_verify */

/* SNIPPET_START: Hacl_RSAPSS_mgf_hash */

/**
  The mask generation function defined in the Public Key Cryptography Standard #1 
  (https://www.ietf.org/rfc/rfc2437.txt Section 10.2.1) 
*/
void
Hacl_RSAPSS_mgf_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t len,
  uint8_t *mgfseed,
  uint32_t maskLen,
  uint8_t *res
);

/* SNIPPET_END: Hacl_RSAPSS_mgf_hash */

#if defined(__cplusplus)
}
#endif

#define __Hacl_RSAPSS_H_DEFINED
#endif
