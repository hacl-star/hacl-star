
/* BCrypt is only available on Windows platforms */
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

  #ifndef NT_SUCCESS
  #define NT_SUCCESS(Status) (((NTSTATUS)(Status)) >= 0)
  #endif
#else
  #define IS_WINDOWS 0
  #include <unistd.h>
#endif

#include <fcntl.h>
#include <inttypes.h>
#include "kremlin/internal/target.h"
#include "EverCrypt_BCrypt.h"

/* KB, BB, JP: for now, we just ignore internal errors since the HACL* interface
 * has enough preconditions to make sure that no errors ever happen; if the
 * OpenSSL F* interface is strong enough, then any error here should be
 * catastrophic and not something we can recover from.
 * If we want to do something better, we can define:
 *   type error a = | Ok of a | Error of error_code
 * Then at the boundary we could catch the error, print it, then exit abruptly.
 * */

#define handleErrors(...)                                                      \
  do {                                                                         \
    fprintf(stderr, "Error at %s:%d\n", __FILE__, __LINE__);                   \
  } while (0)

#if IS_WINDOWS

static BCRYPT_ALG_HANDLE g_hAlgRandom = NULL;

static uint32_t bcrypt_rng_init(void)
{
  NTSTATUS st = BCryptOpenAlgorithmProvider(
    &g_hAlgRandom,
    BCRYPT_RNG_ALGORITHM,
    NULL,
#ifdef _KERNEL_MODE
    BCRYPT_PROV_DISPATCH
#else
    0
#endif
  );
  
  if (!NT_SUCCESS(st)) {
    return 0;
  }

  return 1;
}

static void bcrypt_rng_sample(uint32_t len, uint8_t *out)
{
  NTSTATUS st;

  /* Try to lazily initialize the RNG if it wasn't done
   * by the user. If it fails, the app crashes. */
  if(g_hAlgRandom == NULL)
  {
    if(!bcrypt_rng_init())
      handleErrors();
  }

  st = BCryptGenRandom(g_hAlgRandom, out, len, 0);

  if (!NT_SUCCESS(st)) {
    handleErrors();
  }
}

static void bcrypt_rng_cleanup(void)
{
  BCryptCloseAlgorithmProvider(g_hAlgRandom, 0);
}

static BCRYPT_KEY_HANDLE bcrypt_create(BCRYPT_ALG_HANDLE alg, uint8_t *key, ULONG key_size)
{
  NTSTATUS s;
  BCRYPT_KEY_HANDLE hKey = NULL;
  s = BCryptGenerateSymmetricKey(alg, &hKey, NULL, 0, key, key_size, 0);
  if(!NT_SUCCESS(s)) handleErrors();
  return hKey;
}

static uint32_t bcrypt_aead(BCRYPT_KEY_HANDLE hKey,
  int enc, uint8_t *iv,
  uint8_t *aad, uint32_t aad_len,
  uint8_t *plaintext, uint32_t plaintext_len,
  uint8_t *ciphertext, uint8_t *tag)
{
  BCRYPT_AUTHENTICATED_CIPHER_MODE_INFO Info;
  NTSTATUS s;
  ULONG OutSize;

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

  if (!NT_SUCCESS(s))
    return 0;

  return 1;
}

static void bcrypt_free(BCRYPT_KEY_HANDLE hKey)
{
  BCryptDestroyKey(hKey);
}

#else /* IS_WINDOWS */

#define BCRYPT_KEY_HANDLE void*
#define BCRYPT_ALG_HANDLE uint8_t
#define BCRYPT_AES_GCM_ALG_HANDLE 0

static uint32_t bcrypt_rng_init(void)
{
  return 0;
}

static void bcrypt_rng_sample(uint32_t len, uint8_t *out)
{
  handleErrors();
}

static void bcrypt_rng_cleanup(void)
{
  handleErrors();
}

static BCRYPT_KEY_HANDLE bcrypt_create(BCRYPT_ALG_HANDLE alg, uint8_t key, ULONG key_size)
{
  return NULL;
}

static uint32_t bcrypt_aead(BCRYPT_KEY_HANDLE hKey,
  int enc, uint8_t *iv,
  uint8_t *aad, uint32_t aad_len,
  uint8_t *plaintext, uint32_t plaintext_len,
  uint8_t *ciphertext, uint8_t *tag)
{
  return 0;
}

static void bcrypt_free(BCRYPT_KEY_HANDLE hKey)
{
}

#endif /* IS_WINDOWS */

uint32_t EverCrypt_BCrypt_random_init(void)
{
  return bcrypt_rng_init();
}

void EverCrypt_BCrypt_random_sample(uint32_t len, uint8_t *out)
{
  bcrypt_rng_sample(len, out);
}

void EverCrypt_BCrypt_random_cleanup(void)
{
  bcrypt_rng_cleanup();
}

void EverCrypt_BCrypt_aes128_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  BCRYPT_KEY_HANDLE hKey = bcrypt_create(BCRYPT_AES_GCM_ALG_HANDLE, key, 16);
  if(NULL == hKey || 1 != bcrypt_aead(hKey, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
  bcrypt_free(hKey);
}

uint32_t EverCrypt_BCrypt_aes128_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  BCRYPT_KEY_HANDLE hKey = bcrypt_create(BCRYPT_AES_GCM_ALG_HANDLE, key, 16);
  if(hKey == NULL) return 0;  
  uint32_t ret = bcrypt_aead(hKey, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
  bcrypt_free(hKey);
  return ret;
}

void EverCrypt_BCrypt_aes256_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  BCRYPT_KEY_HANDLE hKey = bcrypt_create(BCRYPT_AES_GCM_ALG_HANDLE, key, 32);
  if(NULL == hKey || 1 != bcrypt_aead(hKey, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
  bcrypt_free(hKey);  
}

uint32_t EverCrypt_BCrypt_aes256_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  uint32_t ret;
  BCRYPT_KEY_HANDLE hKey = bcrypt_create(BCRYPT_AES_GCM_ALG_HANDLE, key, 32);
  if(hKey == NULL) return 0;
  ret = bcrypt_aead(hKey, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
  bcrypt_free(hKey);
  return ret;
}

void* EverCrypt_BCrypt_aead_create(uint8_t alg, uint8_t *key)
{
  BCRYPT_KEY_HANDLE hKey = bcrypt_create(BCRYPT_AES_GCM_ALG_HANDLE, key, alg ? 32 : 16);
  if(hKey == NULL) handleErrors();
  return (void*)hKey;
}

void EverCrypt_BCrypt_aead_encrypt(void* hKey, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                   uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  bcrypt_aead((BCRYPT_KEY_HANDLE)hKey, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

uint32_t EverCrypt_BCrypt_aead_decrypt(void* hKey, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                       uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return bcrypt_aead((BCRYPT_KEY_HANDLE)hKey, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

void EverCrypt_BCrypt_aead_free(void* hKey)
{
  bcrypt_free((BCRYPT_KEY_HANDLE)hKey);
}
