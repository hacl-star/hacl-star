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

#include "haclnacl.h"
#include "kremlib.h"
#include "Hacl_Curve25519.h"
#include "Hacl_Chacha20.h"
#include "Hacl_Salsa20.h"
#include "Hacl_HMAC_SHA2_256.h"
#define Hacl_Impl_Poly1305_64_State_poly1305_state Hacl_Impl_Poly1305_64_State_poly1305_state_poly
#include "Hacl_Poly1305_64.h"
#undef Hacl_Impl_Poly1305_64_State_poly1305_state
#define Hacl_Impl_Poly1305_64_State_poly1305_state Hacl_Impl_Poly1305_64_State_poly1305_state_aead
#include "Hacl_Chacha20Poly1305.h"
#undef Hacl_Impl_Poly1305_64_State_poly1305_state

#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_ed
#include "Hacl_Ed25519.h"
#undef K___uint32_t_uint8_t_
#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_sha256
#include "Hacl_SHA2_256.h"
#undef K___uint32_t_uint8_t_
#define K___uint32_t_uint8_t_ K___uint32_t_uint8_t_sha512
#include "Hacl_SHA2_512.h"
#undef K___uint32_t_uint8_t_
#include "NaCl.h"


extern void randombytes(uint8_t *bytes, uint64_t bytes_len);


/* HACL* Primitives and Constructions */

void curve25519_scalarmult(uint8_t *out, uint8_t *secret, uint8_t *point){
  Hacl_Curve25519_crypto_scalarmult(out, secret, point);
}

void chacha20(uint8_t *output, uint8_t *plain, uint32_t plain_len, uint8_t *key, uint8_t *nonce, uint32_t ctr){
  Hacl_Chacha20_chacha20(output, plain, plain_len, key, nonce, ctr);
}

void salsa20(uint8_t *output, uint8_t *plain, uint32_t len, uint8_t *key, uint8_t *nonce, uint64_t ctr){
  Hacl_Salsa20_salsa20(output, plain, len, key, nonce, ctr);
}

void poly1305_onetimeauth(uint8_t *output, uint8_t *input, uint64_t input_len, uint8_t *key){
  Hacl_Poly1305_64_crypto_onetimeauth(output, input, input_len, key);
}

uint32_t aead_chacha20_poly1305_encrypt(uint8_t *cipher, uint8_t *mac, uint8_t *msg, uint32_t msg_len, uint8_t *aad, uint32_t aad_len, uint8_t *key, uint8_t *nonce){
  return Hacl_Chacha20Poly1305_aead_encrypt(cipher, mac, msg, msg_len, aad, aad_len, key, nonce);
}

uint32_t aead_chacha20_poly1305_decrypt(uint8_t *msg, uint8_t *cipher, uint32_t msg_len, uint8_t *mac, uint8_t *aad, uint32_t aad_len, uint8_t *key, uint8_t *nonce){
  return Hacl_Chacha20Poly1305_aead_decrypt(msg, cipher, msg_len, mac, aad, aad_len, key, nonce);
}

void ed25519_secret_to_public(uint8_t *public_key, uint8_t *secret_key){
  Hacl_Ed25519_secret_to_public(public_key, secret_key);
}

void ed25519_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t msg_len){
  Hacl_Ed25519_sign(signature, secret, msg, msg_len);
}

bool ed25519_verify(uint8_t *public, uint8_t *msg, uint32_t msg_len, uint8_t *signature){
  return Hacl_Ed25519_verify(public, msg, msg_len, signature);
}

void sha2_512_hash(uint8_t *hash, uint8_t *input, uint32_t len){
  Hacl_SHA2_512_hash(hash, input, len);
}


/* NaCl-like API */

int crypto_auth(uint8_t *output, const uint8_t *input, uint64_t input_len, const uint8_t *key){
  Hacl_HMAC_SHA2_256_hmac_core(output, (uint8_t *)key, (uint8_t *)input, input_len);
  return 0;
}

// JP: the owner of this file should include the proper header
// ("kremlib/generated/FStar_UInt8.h")
extern uint8_t FStar_UInt8_eq_mask(uint8_t x0, uint8_t x1);

int crypto_auth_verify(const uint8_t *tag, const uint8_t *input, uint64_t input_len, const uint8_t *key){
  uint8_t recomputed_tag[32], tmp = 0xff;
  Hacl_HMAC_SHA2_256_hmac_core(recomputed_tag, (uint8_t *)key, (uint8_t *)input, input_len);
  for (int i = 0; i < 32; i++){
    tmp = tmp & FStar_UInt8_eq_mask((uint8_t)tag[i], recomputed_tag[i]);
  }
  tmp >>= 7;
  return (int)tmp - 1;
}


int crypto_box_keypair(uint8_t *pk, uint8_t *sk){
  randombytes(sk, 32);
  uint8_t basepoint[32] = {9};
  curve25519_scalarmult(pk, sk, basepoint);
  return 0;
}

int crypto_box_easy(uint8_t *c, const uint8_t *m,
                    uint64_t mlen, const uint8_t *n,
                    const uint8_t *pk, const uint8_t *sk){
  return NaCl_crypto_box_easy(c, (uint8_t*)m, mlen, (uint8_t*)n, (uint8_t*)pk, (uint8_t*)sk);
}

int crypto_box_open_easy(uint8_t *m, const uint8_t *c,
                         uint64_t clen, const uint8_t *n,
                         const uint8_t *pk, const uint8_t *sk){
  return NaCl_crypto_box_open_easy(m, (uint8_t*)c, clen, (uint8_t*)n, (uint8_t*)pk, (uint8_t*)sk);
}

int crypto_box_beforenm(uint8_t *k, const uint8_t *pk,
                        const uint8_t *sk){
  return NaCl_crypto_box_beforenm(k, (uint8_t*)pk, (uint8_t*)sk);
}

int crypto_box_easy_afternm(uint8_t *c, const uint8_t *m,
                            uint64_t mlen, const uint8_t *n,
                            const uint8_t *k){
  return NaCl_crypto_box_easy_afternm(c, (uint8_t*)m, mlen, (uint8_t*)n, (uint8_t*)k);
}

int crypto_box_open_easy_afternm(uint8_t *m, const uint8_t *c,
                                 uint64_t clen, const uint8_t *n,
                                 const uint8_t *k){
  return NaCl_crypto_box_open_easy_afternm(m, (uint8_t*)c, clen, (uint8_t*)n, (uint8_t*)k);
}

uint32_t crypto_box_detached_afternm(uint8_t *c, uint8_t *mac, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_box_detached_afternm(c, mac, m, mlen, n, k);
}

uint32_t crypto_box_detached(uint8_t *c, uint8_t *mac, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *pk, uint8_t *sk){
  return NaCl_crypto_box_detached(c, mac, m, mlen, n, pk, sk);
}

uint32_t crypto_box_open_detached(uint8_t *m, uint8_t *c, uint8_t *mac, uint64_t mlen,  uint8_t *n, uint8_t *pk, uint8_t *sk){
  return NaCl_crypto_box_open_detached(m, c, mac, mlen, n, pk, sk);
}

uint32_t crypto_box_open_detached_afternm(uint8_t *m, uint8_t *c, uint8_t *mac, uint64_t mlen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_box_detached_afternm(m, c, mac, mlen, n, k);
}


int crypto_box(uint8_t *cipher, const uint8_t *msg, uint64_t msg_len, const uint8_t *nonce,  const uint8_t *pk, const uint8_t *sk){
  return crypto_box_easy(cipher, (uint8_t *)msg, msg_len - 32, (uint8_t *)nonce, (uint8_t *)pk, (uint8_t *)sk);
}

int crypto_box_open(uint8_t *msg, const uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *pk, const uint8_t *sk){
  return crypto_box_open_easy(msg, cipher, cipher_len - 32, nonce, pk, sk);
}

int crypto_box_afternm(uint8_t *cipher, const uint8_t *msg, uint64_t msg_len, const uint8_t *nonce, const uint8_t *key){
  return NaCl_crypto_box_easy_afternm(cipher, (uint8_t *)msg, msg_len, (uint8_t *)nonce, (uint8_t *)key);
}

int crypto_box_open_afternm(uint8_t *msg, const uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key){
  return NaCl_crypto_box_open_easy_afternm(msg, (uint8_t *)cipher, cipher_len, (uint8_t *)nonce, (uint8_t *)key);
}


int crypto_hash(uint8_t *output, const uint8_t *input,uint64_t input_len){
  Hacl_SHA2_256_hash(output, (uint8_t *)input, input_len);
  return 0;
}

int crypto_onetimeauth(uint8_t *output, const uint8_t *input, uint64_t input_len, const uint8_t *key){
  poly1305_onetimeauth(output, (uint8_t *)input, input_len, (uint8_t *)key);
  return 0;
}

int crypto_onetimeauth_verify(const uint8_t *auth, const uint8_t *input, uint64_t input_len, const uint8_t *key){
  uint8_t tag[16], tmp = 0xff;
  poly1305_onetimeauth(tag, (uint8_t *)input, input_len, (uint8_t *)key);
  for (int i = 0; i < 16; i++){
    tmp = tmp & FStar_UInt8_eq_mask(tag[i], (uint8_t)auth[i]);
  }
  tmp >>= 7;
  return (int)tmp - 1;
}


int crypto_scalarmult_base(uint8_t *q, const uint8_t *n){
  /* This leaves room for improvements with precomputations */
  uint8_t basepoint[32] = {9};
  Hacl_Curve25519_crypto_scalarmult(q, (uint8_t*)n, basepoint);
  return 0;
}

int crypto_scalarmult(uint8_t *q, const uint8_t *n, const uint8_t *p){
  Hacl_Curve25519_crypto_scalarmult(q, (uint8_t*)n, (uint8_t*)p);
  return 0;
}


uint32_t crypto_secretbox_detached(uint8_t *c, uint8_t *mac, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_secretbox_detached(c, mac, m, mlen, n, k);
}

uint32_t crypto_secretbox_open_detached(uint8_t *m, uint8_t *c, uint8_t *mac, uint64_t clen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_secretbox_open_detached(m, c, mac, clen, n, k);
}

uint32_t crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint64_t mlen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_secretbox_easy(c, m, mlen, n, k);
}

uint32_t crypto_secretbox_open_easy(uint8_t *m, uint8_t *c, uint64_t clen, uint8_t *n, uint8_t *k){
  return NaCl_crypto_secretbox_open_easy(m, c, clen, n, k);
}

int crypto_secretbox(uint8_t *cipher, const uint8_t *msg, uint64_t msg_len, const uint8_t *nonce, const uint8_t *key){
  return crypto_secretbox_easy(cipher, (uint8_t *)msg, msg_len - 32, (uint8_t *)nonce, (uint8_t *)key);
}

int crypto_secretbox_open(uint8_t *msg, const uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key){
  return crypto_secretbox_open_detached(msg, (uint8_t *)cipher, (uint8_t *)cipher + 16, cipher_len - 32, (uint8_t *)nonce, (uint8_t *)key);
}


int crypto_sign(uint8_t *signed_msg, uint64_t *signed_len, const uint8_t *msg, uint64_t msg_len, const uint8_t *sk){
  Hacl_Ed25519_sign(signed_msg, (uint8_t *)sk, (uint8_t *)msg, msg_len);
  memmove(signed_msg+64, msg, msg_len * sizeof(uint8_t));
  *signed_len = msg_len + 64;
  return 0;
}

int crypto_sign_open(uint8_t *unsigned_msg, uint64_t *unsigned_msg_len, const uint8_t *msg, uint64_t msg_len, const uint8_t *pk){
  uint32_t res;
  res = Hacl_Ed25519_verify((uint8_t *)pk, (uint8_t *)msg+64, msg_len - 64, (uint8_t *)msg);
  if (res){
    memmove(unsigned_msg, msg+64, sizeof(uint8_t) * (msg_len-64));
    *unsigned_msg_len = msg_len - 64;
    return 0;
  } else {
    return -1;
  }
}

int crypto_sign_keypair(uint8_t pk[32], uint8_t sk[64]){
  randombytes(sk, 32 * sizeof(uint8_t));
  Hacl_Ed25519_secret_to_public(pk, sk);
  for (int i = 0; i < 32; i++) sk[32+i] = pk[i];
  return 0;
}

int crypto_sign_secret_to_public(uint8_t *public_key, uint8_t *secret_key){
  Hacl_Ed25519_secret_to_public(public_key, secret_key);
  return 0;
}


int crypto_stream(uint8_t *cipher, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key){
  uint8_t subkey[32];
  memset(cipher, 0, cipher_len * sizeof(uint8_t));
  Hacl_Salsa20_hsalsa20(subkey, (uint8_t *)key, (uint8_t *)nonce);
  Hacl_Salsa20_salsa20(cipher, cipher, cipher_len, subkey, (uint8_t *)nonce + 16, 0);
  return 0;
}

int crypto_stream_xor(uint8_t *cipher, const uint8_t *msg, uint64_t cipher_len, const uint8_t *nonce, const uint8_t *key){
  uint8_t subkey[32];
  memset(cipher, 0, cipher_len * sizeof(uint8_t));
  Hacl_Salsa20_hsalsa20(subkey, (uint8_t *)key, (uint8_t *)nonce);
  Hacl_Salsa20_salsa20(cipher, (uint8_t *)msg, cipher_len, subkey, (uint8_t *)nonce + 16, 0);
  return 0;
}
