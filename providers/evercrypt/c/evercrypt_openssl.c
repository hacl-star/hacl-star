#include <openssl/evp.h>
#include <inttypes.h>

#include "kremlin/internal/target.h"
#include "EverCrypt_OpenSSL.h"

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

EVP_CIPHER_CTX *openssl_create(const EVP_CIPHER *alg, uint8_t *key)
{
  EVP_CIPHER_CTX *ctx;
  
  if (!(ctx = EVP_CIPHER_CTX_new()))
    return NULL;

  if (1 != EVP_CipherInit_ex(ctx, alg, NULL, key, NULL, -1))
  {
    EVP_CIPHER_CTX_free(ctx);
    return NULL;
  }

  return ctx;
}

void openssl_free(EVP_CIPHER_CTX *ctx)
{
  EVP_CIPHER_CTX_free(ctx);
}

static int openssl_aead(EVP_CIPHER_CTX *ctx,
  int enc, uint8_t *iv,
  uint8_t *aad, uint32_t aad_len,
  uint8_t *plaintext, uint32_t plaintext_len,
  uint8_t *ciphertext, uint8_t *tag)
{
  int len;

  // Initialise the cipher with the key and IV
  if (1 != EVP_CipherInit_ex(ctx, NULL, NULL, NULL, iv, enc))
    handleErrors();

  // Set additional authenticated data
  if (aad_len > 0 && 1 != EVP_CipherUpdate(ctx, NULL, &len, aad, aad_len))
    handleErrors();

  // Process the plaintext
  if (enc && plaintext_len > 0
      && 1 != EVP_CipherUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
    handleErrors();

  // Process the ciphertext
  if (!enc && plaintext_len > 0
      && 1 != EVP_CipherUpdate(ctx, plaintext, &len, ciphertext, plaintext_len))
    handleErrors();

  // Set the tag
  if(!enc && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, 16, tag) <= 0)
    handleErrors();

  // Finalize last block
  if (1 != EVP_CipherFinal_ex(ctx, ciphertext + len, &len))
    return 0;

  // Get the tag
  if (enc && 1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, 16, tag))
    handleErrors();

  return 1;
}

void EverCrypt_OpenSSL_aes128_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_aes_128_gcm(), key);
  if(NULL == ctx || 1 != openssl_aead(ctx, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
  openssl_free(ctx);
}

uint32_t EverCrypt_OpenSSL_aes128_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                              uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_aes_128_gcm(), key);
  int ret = openssl_aead(ctx, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
  openssl_free(ctx);
  return ret;
}

void EverCrypt_OpenSSL_aes256_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_aes_256_gcm(), key);
  if(NULL == ctx || 1 != openssl_aead(ctx, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
  openssl_free(ctx);
}

uint32_t EverCrypt_OpenSSL_aes256_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                              uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_aes_256_gcm(), key);
  int ret = openssl_aead(ctx, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
  openssl_free(ctx);
  return ret;
}

void EverCrypt_OpenSSL_chacha20_poly1305_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                                 uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_chacha20_poly1305(), key);
  if(NULL == ctx || 1 != openssl_aead(ctx, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
  openssl_free(ctx);
}

uint32_t EverCrypt_OpenSSL_chacha20_poly1305_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                                     uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_chacha20_poly1305(), key);
  int ret = openssl_aead(ctx, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
  openssl_free(ctx);
  return ret;
}

void* EverCrypt_OpenSSL_aead_create(uint8_t alg, uint8_t *key)
{
  const EVP_CIPHER *a;
  EVP_CIPHER_CTX *ctx;
  
  if(alg == 0) a = EVP_aes_128_gcm();
  else if(alg == 1) a = EVP_aes_256_gcm();
  else if(alg == 2) a = EVP_chacha20_poly1305();
  else handleErrors();

  ctx = openssl_create(a, key);
  if(ctx == NULL) handleErrors();

  return (void*)ctx;
}

void EverCrypt_OpenSSL_aead_encrypt(void* ctx, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                    uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  if(!openssl_aead((EVP_CIPHER_CTX*)ctx, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
}

uint32_t EverCrypt_OpenSSL_aead_decrypt(void* ctx, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                    uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return openssl_aead((EVP_CIPHER_CTX*)ctx, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

void EverCrypt_OpenSSL_aead_free(void* ctx)
{
  openssl_free((EVP_CIPHER_CTX *)ctx);
}
