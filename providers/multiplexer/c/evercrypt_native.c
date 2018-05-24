#include "EverCrypt_Native.h"

// Filling out the default implementations: HACL*.
EverCrypt_Native_impl EverCrypt_Native_sha256_impl = EverCrypt_Native_Vale;
EverCrypt_Native_impl EverCrypt_Native_sha384_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_sha512_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_x25519_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_aes_gcm_impl = EverCrypt_Native_OpenSSL;
EverCrypt_Native_impl EverCrypt_Native_chacha20_poly1305_impl = EverCrypt_Native_Hacl;

void EverCrypt_Native_init(EverCrypt_Native_cfg x0) {
  if (x0.tag == EverCrypt_Native_Default || x0.preferred == EverCrypt_Native_Vale) {
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Vale;
    // The other four algorithms have a single implementation, for now.
  } else if (x0.preferred == EverCrypt_Native_Hacl) {
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Hacl;
    // The other four algorithms have a single implementation, for now.
  }
}
