#ifndef __EverCrypt_Bytes_Lib_H
#define __EverCrypt_Bytes_Lib_H

#include <stdint.h>
#include "kremlin/internal/compat.h"

extern FStar_Bytes_bytes EverCrypt_Bytes_x25519(FStar_Bytes_bytes x0, FStar_Bytes_bytes x1);

typedef struct EverCrypt_Bytes_cipher_tag_s
{
  FStar_Bytes_bytes cipher;
  FStar_Bytes_bytes tag;
}
EverCrypt_Bytes_cipher_tag;

extern EverCrypt_Bytes_cipher_tag
EverCrypt_Bytes_chacha20_poly1305_encrypt(
  FStar_Bytes_bytes x0,
  FStar_Bytes_bytes x1,
  FStar_Bytes_bytes x2,
  FStar_Bytes_bytes x3
);

#define EverCrypt_Bytes_Error 0
#define EverCrypt_Bytes_Correct 1

typedef uint8_t EverCrypt_Bytes_maybe_plaintext_tags;

typedef struct EverCrypt_Bytes_maybe_plaintext_s
{
  EverCrypt_Bytes_maybe_plaintext_tags tag;
  FStar_Bytes_bytes _0;
}
EverCrypt_Bytes_maybe_plaintext;

extern EverCrypt_Bytes_maybe_plaintext
EverCrypt_Bytes_chacha20_poly1305_decrypt(
  FStar_Bytes_bytes x0,
  FStar_Bytes_bytes x1,
  FStar_Bytes_bytes x2,
  FStar_Bytes_bytes x3,
  FStar_Bytes_bytes x4
);

#endif
