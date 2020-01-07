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

#include "libintvector.h"
#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "kremlin/internal/target.h"

#ifndef __EverCrypt_OpenSSL_H
#define __EverCrypt_OpenSSL_H




extern u32 EverCrypt_OpenSSL_random_init();

extern void EverCrypt_OpenSSL_random_sample(u32 len, u8 *out);

extern void
EverCrypt_OpenSSL_aes128_gcm_encrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plain,
  u32 len,
  u8 *cipher,
  u8 *tag
);

extern u32
EverCrypt_OpenSSL_aes128_gcm_decrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plain,
  u32 len,
  u8 *cipher,
  u8 *tag
);

extern void
EverCrypt_OpenSSL_aes256_gcm_encrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plain,
  u32 len,
  u8 *cipher,
  u8 *tag
);

extern u32
EverCrypt_OpenSSL_aes256_gcm_decrypt(
  u8 *key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plain,
  u32 len,
  u8 *cipher,
  u8 *tag
);

#define EverCrypt_OpenSSL_AES128_GCM 0
#define EverCrypt_OpenSSL_AES256_GCM 1
#define EverCrypt_OpenSSL_CHACHA20_POLY1305 2

typedef u8 EverCrypt_OpenSSL_alg;

extern FStar_Dyn_dyn EverCrypt_OpenSSL_aead_create(EverCrypt_OpenSSL_alg alg, u8 *key);

extern void
EverCrypt_OpenSSL_aead_encrypt(
  FStar_Dyn_dyn key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plain,
  u32 len,
  u8 *cipher,
  u8 *tag
);

extern u32
EverCrypt_OpenSSL_aead_decrypt(
  FStar_Dyn_dyn key,
  u8 *iv,
  u8 *ad,
  u32 adlen,
  u8 *plain,
  u32 len,
  u8 *cipher,
  u8 *tag
);

extern void EverCrypt_OpenSSL_aead_free(FStar_Dyn_dyn key);

extern FStar_Dyn_dyn
EverCrypt_OpenSSL_dh_load_group(
  u8 *dh_p,
  u32 dh_p_len,
  u8 *dh_g,
  u32 dh_g_len,
  u8 *dh_q,
  u32 dh_q_len
);

extern void EverCrypt_OpenSSL_dh_free_group(FStar_Dyn_dyn st);

extern u32 EverCrypt_OpenSSL_dh_keygen(FStar_Dyn_dyn st, u8 *out);

extern u32 EverCrypt_OpenSSL_dh_compute(FStar_Dyn_dyn st, u8 *public, u32 public_len, u8 *out);

#define EverCrypt_OpenSSL_ECC_P256 0
#define EverCrypt_OpenSSL_ECC_P384 1
#define EverCrypt_OpenSSL_ECC_P521 2
#define EverCrypt_OpenSSL_ECC_X25519 3
#define EverCrypt_OpenSSL_ECC_X448 4

typedef u8 EverCrypt_OpenSSL_ec_curve;

extern FStar_Dyn_dyn EverCrypt_OpenSSL_ecdh_load_curve(EverCrypt_OpenSSL_ec_curve g);

extern void EverCrypt_OpenSSL_ecdh_free_curve(FStar_Dyn_dyn st);

extern void EverCrypt_OpenSSL_ecdh_keygen(FStar_Dyn_dyn st, u8 *outx, u8 *outy);

extern u32 EverCrypt_OpenSSL_ecdh_compute(FStar_Dyn_dyn st, u8 *inx, u8 *iny, u8 *out);

#define __EverCrypt_OpenSSL_H_DEFINED
#endif
