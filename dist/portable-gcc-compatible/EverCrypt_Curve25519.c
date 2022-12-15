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


#include "EverCrypt_Curve25519.h"


#include "config.h"
/* SNIPPET_START: has_adx_bmi2 */

static inline bool has_adx_bmi2()
{
  bool has_bmi2 = EverCrypt_AutoConfig2_has_bmi2();
  bool has_adx = EverCrypt_AutoConfig2_has_adx();
  return has_bmi2 && has_adx;
}

/* SNIPPET_END: has_adx_bmi2 */

/* SNIPPET_START: EverCrypt_Curve25519_secret_to_public */

/**
Calculate a public point from a secret/private key.

This computes a scalar multiplication of the secret/private key with the curve's basepoint.

@param pub Pointer to 32 bytes of memory where the resulting point is written to.
@param priv Pointer to 32 bytes of memory where the secret/private key is read from.
*/
void EverCrypt_Curve25519_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  #if HACL_CAN_COMPILE_VALE
  if (has_adx_bmi2())
  {
    Hacl_Curve25519_64_secret_to_public(pub, priv);
    return;
  }
  #endif
  Hacl_Curve25519_51_secret_to_public(pub, priv);
}

/* SNIPPET_END: EverCrypt_Curve25519_secret_to_public */

/* SNIPPET_START: EverCrypt_Curve25519_scalarmult */

/**
Compute the scalar multiple of a point.

@param shared Pointer to 32 bytes of memory where the resulting point is written to.
@param my_priv Pointer to 32 bytes of memory where the secret/private key is read from.
@param their_pub Pointer to 32 bytes of memory where the public point is read from.
*/
void EverCrypt_Curve25519_scalarmult(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub)
{
  #if HACL_CAN_COMPILE_VALE
  if (has_adx_bmi2())
  {
    Hacl_Curve25519_64_scalarmult(shared, my_priv, their_pub);
    return;
  }
  #endif
  Hacl_Curve25519_51_scalarmult(shared, my_priv, their_pub);
}

/* SNIPPET_END: EverCrypt_Curve25519_scalarmult */

/* SNIPPET_START: EverCrypt_Curve25519_ecdh */

/**
Execute the diffie-hellmann key exchange.

@param shared Pointer to 32 bytes of memory where the resulting point is written to.
@param my_priv Pointer to 32 bytes of memory where **our** secret/private key is read from.
@param their_pub Pointer to 32 bytes of memory where **their** public point is read from.
*/
bool EverCrypt_Curve25519_ecdh(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub)
{
  #if HACL_CAN_COMPILE_VALE
  if (has_adx_bmi2())
  {
    return Hacl_Curve25519_64_ecdh(shared, my_priv, their_pub);
  }
  #endif
  return Hacl_Curve25519_51_ecdh(shared, my_priv, their_pub);
}

/* SNIPPET_END: EverCrypt_Curve25519_ecdh */

