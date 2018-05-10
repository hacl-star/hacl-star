#include "EverCrypt_Native.h"

// Filling out the default implementations: HACL*.
EverCrypt_Native_impl EverCrypt_Native_sha256_impl = EverCrypt_Native_Vale;
EverCrypt_Native_impl EverCrypt_Native_sha384_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_sha512_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_x25519_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_aes_gcm_impl = EverCrypt_Native_OpenSSL;

void EverCrypt_Native_init(FStar_Pervasives_Native_option__EverCrypt_Native_impl x0) {
  if (x0.tag == FStar_Pervasives_Native_None || x0.v == EverCrypt_Native_Vale) {
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Vale;
    // The other four algorithms have a single implementation, for now.
  } else if (x0.v == EverCrypt_Native_Hacl) {
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Hacl;
    // The other four algorithms have a single implementation, for now.
  }
}
