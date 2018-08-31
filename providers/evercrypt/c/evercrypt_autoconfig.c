#include "EverCrypt_AutoConfig.h"
#include "EverCrypt_StaticConfig.h"

// Abbreviations, for readability
typedef EverCrypt_AutoConfig_impl impl;

#define Vale EverCrypt_AutoConfig_Vale
#define Hacl EverCrypt_AutoConfig_Hacl
#define OpenSSL EverCrypt_AutoConfig_OpenSSL
#define BCrypt EverCrypt_AutoConfig_BCrypt

EverCrypt_AutoConfig_cfg_tags Default = EverCrypt_AutoConfig_Default;
EverCrypt_AutoConfig_cfg_tags Prefer = EverCrypt_AutoConfig_Prefer;

// We store our choices in global variables to improve processor branch
// prediction and prefetching.
impl sha256_impl = Vale;
impl sha384_impl = Hacl;
impl sha512_impl = Hacl;
impl x25519_impl = Hacl;
impl random_impl = BCrypt;
impl aes128_impl = Hacl;
impl aes256_impl = Hacl;
impl chacha20_impl = Hacl;
impl aes128_gcm_impl = Vale;
impl aes256_gcm_impl = Vale;
impl chacha20_poly1305_impl = Hacl;

// https://en.wikipedia.org/wiki/CPUID
#ifdef _MSC_VER

#include <intrin.h>
bool detect_aesni() {
// X64: cpuid exists, we have vale code that uses aesni, detect
#if defined(_M_X64)
  int features[4];
  // 1: request feature bits
  __cpuid(features, 1);
  return (features[3] & 0x2000000) != 0;
// X86: cpuid exists, but we do not have vale code; bail
#elif defined(_M_IX86)
  return false;
// other architectures: no cpuid intrinsic, todo
#else
  return false;
#endif
}

#else // _MSC_VER

#include <cpuid.h>
bool detect_aesni() {
// Same logic as above
#if defined(__x86_64)
  // https://github.com/gcc-mirror/gcc/blob/master/gcc/config/i386/cpuid.h
  unsigned int eax, ebx, ecx, edx;
  if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx))
    return false;
  return (ecx & bit_AES) != 0;
#else
  return false;
#endif
}

#endif // _MSC_VER


void EverCrypt_AutoConfig_init(EverCrypt_AutoConfig_cfg x0) {
  bool prefer_hacl = x0.tag == Prefer && x0.preferred == Hacl;
  bool prefer_vale = x0.tag == Prefer && x0.preferred == Vale;
  bool prefer_openssl = x0.tag == Prefer && x0.preferred == OpenSSL;
  bool prefer_bcrypt = x0.tag == Prefer && x0.preferred == BCrypt;
  bool has_aesni = detect_aesni();

  // The switches follow a regular structure. Honor the prefered choice first,
  // then make a sensible choice given the static configuration. Note that we DO
  // NOT tackle the case where, say, the user does something silly and runs in a
  // static configuration with Vale disabled and still calls us with prefer_vale.

  // SHA256: best = Vale (unconditionally), fallback = Hacl (always works)
  if (prefer_hacl) {
    sha256_impl = Hacl;
  } else if (EverCrypt_StaticConfig_vale && prefer_vale) {
    sha256_impl = Vale;
  } else {
    sha256_impl = Hacl;
  }

  // AES128-GCM: best = Vale (IF AES-NI), fallback = OpenSSL or BCrypt
  if (EverCrypt_StaticConfig_openssl && prefer_openssl) {
    random_impl = OpenSSL;
  } else if (EverCrypt_StaticConfig_bcrypt && prefer_bcrypt) {
    random_impl = BCrypt;
  } else {
    random_impl = EverCrypt_StaticConfig_bcrypt ? BCrypt : OpenSSL;
  }
  
  // AES128-GCM: best = Vale (IF AES-NI), fallback = OpenSSL or BCrypt
  if (has_aesni && EverCrypt_StaticConfig_vale && prefer_vale) {
    aes128_gcm_impl = Vale;
  } else if (EverCrypt_StaticConfig_bcrypt && prefer_bcrypt) {
    aes128_gcm_impl = BCrypt;
  } else if (EverCrypt_StaticConfig_openssl && prefer_openssl) {
    aes128_gcm_impl = OpenSSL;
  } else if (EverCrypt_StaticConfig_bcrypt) {
    aes128_gcm_impl = BCrypt;
  } else if (EverCrypt_StaticConfig_openssl) {
    aes128_gcm_impl = OpenSSL;
  } else {
    //assert (EverCrypt_StaticConfig_vale);
    aes128_gcm_impl = Vale;
  }

  // AES256-GCM: best = Vale (IF AES-NI), fallback = OpenSSL or BCrypt
  if (has_aesni && EverCrypt_StaticConfig_vale && prefer_vale) {
    aes256_gcm_impl = Vale;
  } else if (EverCrypt_StaticConfig_bcrypt && prefer_bcrypt) {
    aes256_gcm_impl = BCrypt;
  } else if (EverCrypt_StaticConfig_openssl && prefer_openssl) {
    aes256_gcm_impl = OpenSSL;
  } else if (EverCrypt_StaticConfig_bcrypt) {
    aes128_gcm_impl = BCrypt;
  } else if (EverCrypt_StaticConfig_openssl) {
    aes128_gcm_impl = OpenSSL;
  } else {
    //assert (EverCrypt_StaticConfig_vale);
    aes128_gcm_impl = Vale;
  }

  if (EverCrypt_StaticConfig_openssl && prefer_openssl) {
    chacha20_poly1305_impl = OpenSSL;
  } else {
    chacha20_poly1305_impl = Hacl;
  }
}

impl EverCrypt_AutoConfig_sha256_impl() {
  return sha256_impl;
}

impl EverCrypt_AutoConfig_sha384_impl() {
  return sha384_impl;
}

impl EverCrypt_AutoConfig_sha512_impl() {
  return sha512_impl;
}

impl EverCrypt_AutoConfig_x25519_impl() {
  return x25519_impl;
}

impl EverCrypt_AutoConfig_random_impl() {
  return random_impl;
}

impl EverCrypt_AutoConfig_aes128_gcm_impl() {
  return aes128_gcm_impl;
}

impl EverCrypt_AutoConfig_aes128_impl() {
  return aes128_impl;
}

impl EverCrypt_AutoConfig_aes256_impl() {
  return aes256_impl;
}

impl EverCrypt_AutoConfig_chacha20_impl() {
  return chacha20_impl;
}

impl EverCrypt_AutoConfig_aes256_gcm_impl() {
  return aes256_gcm_impl;
}

impl EverCrypt_AutoConfig_chacha20_poly1305_impl() {
  return chacha20_poly1305_impl;
}
