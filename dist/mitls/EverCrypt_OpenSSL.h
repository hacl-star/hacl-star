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


#ifndef __EverCrypt_OpenSSL_H
#define __EverCrypt_OpenSSL_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "evercrypt_targetconfig.h"
#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"




extern uint32_t EverCrypt_OpenSSL_random_init();

extern void EverCrypt_OpenSSL_random_sample(uint32_t len, uint8_t *out);

extern void
EverCrypt_OpenSSL_aes128_gcm_encrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

extern uint32_t
EverCrypt_OpenSSL_aes128_gcm_decrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

extern void
EverCrypt_OpenSSL_aes256_gcm_encrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

extern uint32_t
EverCrypt_OpenSSL_aes256_gcm_decrypt(
  uint8_t *key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

#define EverCrypt_OpenSSL_AES128_GCM 0
#define EverCrypt_OpenSSL_AES256_GCM 1
#define EverCrypt_OpenSSL_CHACHA20_POLY1305 2

typedef uint8_t EverCrypt_OpenSSL_alg;

extern FStar_Dyn_dyn EverCrypt_OpenSSL_aead_create(EverCrypt_OpenSSL_alg alg1, uint8_t *key);

extern void
EverCrypt_OpenSSL_aead_encrypt(
  FStar_Dyn_dyn key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

extern uint32_t
EverCrypt_OpenSSL_aead_decrypt(
  FStar_Dyn_dyn key,
  uint8_t *iv,
  uint8_t *ad,
  uint32_t adlen,
  uint8_t *plain,
  uint32_t len,
  uint8_t *cipher,
  uint8_t *tag
);

extern void EverCrypt_OpenSSL_aead_free(FStar_Dyn_dyn key);

extern FStar_Dyn_dyn
EverCrypt_OpenSSL_dh_load_group(
  uint8_t *dh_p,
  uint32_t dh_p_len,
  uint8_t *dh_g,
  uint32_t dh_g_len,
  uint8_t *dh_q,
  uint32_t dh_q_len
);

extern void EverCrypt_OpenSSL_dh_free_group(FStar_Dyn_dyn st);

extern uint32_t EverCrypt_OpenSSL_dh_keygen(FStar_Dyn_dyn st, uint8_t *out);

extern uint32_t
EverCrypt_OpenSSL_dh_compute(
  FStar_Dyn_dyn st,
  uint8_t *public,
  uint32_t public_len,
  uint8_t *out
);

#define EverCrypt_OpenSSL_ECC_P256 0
#define EverCrypt_OpenSSL_ECC_P384 1
#define EverCrypt_OpenSSL_ECC_P521 2
#define EverCrypt_OpenSSL_ECC_X25519 3
#define EverCrypt_OpenSSL_ECC_X448 4

typedef uint8_t EverCrypt_OpenSSL_ec_curve;

extern FStar_Dyn_dyn EverCrypt_OpenSSL_ecdh_load_curve(EverCrypt_OpenSSL_ec_curve g);

extern void EverCrypt_OpenSSL_ecdh_free_curve(FStar_Dyn_dyn st);

extern void EverCrypt_OpenSSL_ecdh_keygen(FStar_Dyn_dyn st, uint8_t *outx, uint8_t *outy);

extern uint32_t
EverCrypt_OpenSSL_ecdh_compute(FStar_Dyn_dyn st, uint8_t *inx, uint8_t *iny, uint8_t *out);

#if defined(__cplusplus)
}
#endif

#define __EverCrypt_OpenSSL_H_DEFINED
#endif
