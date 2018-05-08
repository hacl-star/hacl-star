#include "EverCrypt_Native.h"

// Filling out the default implementations: HACL*.
EverCrypt_Native_impl EverCrypt_Native_sha256_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_sha384_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_sha512_impl = EverCrypt_Native_Hacl;
EverCrypt_Native_impl EverCrypt_Native_x25519_impl = EverCrypt_Native_Hacl;

void EverCrypt_Native_init(FStar_Pervasives_Native_option__EverCrypt_Native_impl x0) {
  if (x0.tag == FStar_Pervasives_Native_None) {
    // Default best SHA256: unconditionally Vale.
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Vale;
  } else if (x0.v == EverCrypt_Native_Hacl) {
    // Prefer HACL*
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Hacl;
  } else if (x0.v == EverCrypt_Native_Vale) {
    // Prefer Vale
    EverCrypt_Native_sha256_impl = EverCrypt_Native_Vale;
  }
}
