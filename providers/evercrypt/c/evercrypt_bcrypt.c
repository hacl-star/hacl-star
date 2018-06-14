
// BCrypt is only available on Windows platforms
#if defined(_MSC_VER) || defined(__MINGW32__)
  #define IS_WINDOWS 1
  #ifdef _KERNEL_MODE
    #include <nt.h>
    #include <ntrtl.h>
  #else
    #include <windows.h>
  #endif
  #include <bcrypt.h>
  #ifndef BCRYPT_AES_GCM_ALG_HANDLE
  #define BCRYPT_AES_GCM_ALG_HANDLE ((BCRYPT_ALG_HANDLE) 0x000001e1)
  #endif
#else
  #define IS_WINDOWS 0
  #include <unistd.h>
#endif

#define NT_SUCCESS(Status)          (((NTSTATUS)(Status)) >= 0)

#include <fcntl.h>
#include <inttypes.h>
#include "kremlin/internal/target.h"
#include "EverCrypt_BCrypt.h"

// KB, BB, JP: for now, we just ignore internal errors since the HACL* interface
// has enough preconditions to make sure that no errors ever happen; if the
// OpenSSL F* interface is strong enough, then any error here should be
// catastrophic and not something we can recover from.
// If we want to do something better, we can define:
//   type error a = | Ok of a | Error of error_code
// Then at the boundary we could catch the error, print it, then exit abruptly.

#define handleErrors(...)                                                      \
  do {                                                                         \
    KRML_HOST_EPRINTF("Error at %s:%d\n", __FILE__, __LINE__);                   \
  } while (0)

static int bcrypt_aead(ULONG key_size, int enc,
  uint8_t *key, uint8_t *iv,
  uint8_t *aad, uint32_t aad_len,
  uint8_t *plaintext, uint32_t plaintext_len,
  uint8_t *ciphertext, uint8_t *tag)
{
#if IS_WINDOWS
  BCRYPT_KEY_HANDLE hKey = NULL;
  BCRYPT_AUTHENTICATED_CIPHER_MODE_INFO Info;
  NTSTATUS s;
  ULONG OutSize;

  s = BCryptGenerateSymmetricKey(BCRYPT_AES_GCM_ALG_HANDLE, &hKey, NULL, 0, key, key_size, 0);
  if(!NT_SUCCESS(s)) return 0;

  BCRYPT_INIT_AUTH_MODE_INFO(Info);
  Info.pbAuthData = (PUCHAR) aad;
  Info.cbAuthData = aad_len;
  Info.pbTag = tag;
  Info.cbTag = 16;
  Info.pbNonce = iv;
  Info.cbNonce = 12;

  if(enc)
    s = BCryptEncrypt(hKey, plaintext, plaintext_len, &Info, iv, 12, ciphertext, plaintext_len, &OutSize, 0);
  else
    s = BCryptDecrypt(hKey, ciphertext, plaintext_len, &Info, iv, 12, plaintext, plaintext_len, &OutSize, 0);

  BCryptDestroyKey(hKey);

  if (!NT_SUCCESS(s))
    return 0;

  return 1;
#else
  return 0;
#endif
}

void EverCrypt_BCrypt_aes128_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  if(1 != bcrypt_aead(16, 1, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
}

uint32_t EverCrypt_BCrypt_aes128_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return bcrypt_aead(16, 0, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

void EverCrypt_BCrypt_aes256_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  if(1 != bcrypt_aead(32, 1, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
}

uint32_t EverCrypt_BCrypt_aes256_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return bcrypt_aead(32, 0, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

