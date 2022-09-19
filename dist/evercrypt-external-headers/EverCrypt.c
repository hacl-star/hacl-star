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


#include "EverCrypt.h"



<<<<<<< HEAD
#define AES128_OPENSSL 0
#define AES128_BCRYPT 1
#define AES128_VALE 2
#define AES128_HACL 3

typedef uint8_t aes128_key_s_tags;

typedef struct EverCrypt_aes128_key_s_s
{
  aes128_key_s_tags tag;
  union {
    FStar_Dyn_dyn case_AES128_OPENSSL;
    FStar_Dyn_dyn case_AES128_BCRYPT;
    struct
    {
      uint8_t *w;
      uint8_t *sbox;
    }
    case_AES128_VALE;
    struct
    {
      uint8_t *w;
      uint8_t *sbox;
    }
    case_AES128_HACL;
  }
  ;
}
EverCrypt_aes128_key_s;

extern bool EverCrypt_uu___is_AES128_OPENSSL(EverCrypt_aes128_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES128_OPENSSL__item__st(EverCrypt_aes128_key_s projectee);

extern bool EverCrypt_uu___is_AES128_BCRYPT(EverCrypt_aes128_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES128_BCRYPT__item__st(EverCrypt_aes128_key_s projectee);

extern bool EverCrypt_uu___is_AES128_VALE(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_VALE__item__w(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_VALE__item__sbox(EverCrypt_aes128_key_s projectee);

extern bool EverCrypt_uu___is_AES128_HACL(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_HACL__item__w(EverCrypt_aes128_key_s projectee);

extern uint8_t *EverCrypt___proj__AES128_HACL__item__sbox(EverCrypt_aes128_key_s projectee);

#define AES256_OPENSSL 0
#define AES256_BCRYPT 1
#define AES256_HACL 2

typedef uint8_t aes256_key_s_tags;

typedef struct EverCrypt_aes256_key_s_s
{
  aes256_key_s_tags tag;
  union {
    FStar_Dyn_dyn case_AES256_OPENSSL;
    FStar_Dyn_dyn case_AES256_BCRYPT;
    struct
    {
      uint8_t *w;
      uint8_t *sbox;
    }
    case_AES256_HACL;
  }
  ;
}
EverCrypt_aes256_key_s;

extern bool EverCrypt_uu___is_AES256_OPENSSL(EverCrypt_aes256_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES256_OPENSSL__item__st(EverCrypt_aes256_key_s projectee);

extern bool EverCrypt_uu___is_AES256_BCRYPT(EverCrypt_aes256_key_s projectee);

extern FStar_Dyn_dyn
EverCrypt___proj__AES256_BCRYPT__item__st(EverCrypt_aes256_key_s projectee);

extern bool EverCrypt_uu___is_AES256_HACL(EverCrypt_aes256_key_s projectee);

extern uint8_t *EverCrypt___proj__AES256_HACL__item__w(EverCrypt_aes256_key_s projectee);

extern uint8_t *EverCrypt___proj__AES256_HACL__item__sbox(EverCrypt_aes256_key_s projectee);

#define AEAD_OPENSSL 0
#define AEAD_BCRYPT 1
#define AEAD_AES128_GCM_VALE 2
#define AEAD_AES256_GCM_VALE 3
#define AEAD_CHACHA20_POLY1305_HACL 4

typedef uint8_t _aead_state_tags;

typedef struct EverCrypt__aead_state_s
{
  _aead_state_tags tag;
  union {
    FStar_Dyn_dyn case_AEAD_OPENSSL;
    FStar_Dyn_dyn case_AEAD_BCRYPT;
    uint8_t *case_AEAD_AES128_GCM_VALE;
    uint8_t *case_AEAD_AES256_GCM_VALE;
    uint8_t *case_AEAD_CHACHA20_POLY1305_HACL;
  }
  ;
}
EverCrypt__aead_state;

typedef EverCrypt__aead_state EverCrypt_aead_state_s;

#define DH_OPENSSL 0
#define DH_DUMMY 1

typedef uint8_t _dh_state_tags;

typedef struct EverCrypt__dh_state_s
{
  _dh_state_tags tag;
  FStar_Dyn_dyn st;
}
EverCrypt__dh_state;

typedef EverCrypt__dh_state EverCrypt_dh_state_s;

#define ECDH_OPENSSL 0
#define ECDH_DUMMY 1

typedef uint8_t _ecdh_state_tags;

typedef struct EverCrypt__ecdh_state_s
{
  _ecdh_state_tags tag;
  FStar_Dyn_dyn st;
}
EverCrypt__ecdh_state;

typedef EverCrypt__ecdh_state EverCrypt_ecdh_state_s;

=======
>>>>>>> main
typedef struct EverCrypt_AEAD_state_s_s
{
  Spec_Cipher_Expansion_impl impl;
  uint8_t *ek;
}
EverCrypt_AEAD_state_s;

