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

static int openssl_aead(const EVP_CIPHER *alg, int enc,
  uint8_t *key, uint8_t *iv,
  uint8_t *aad, uint32_t aad_len,
  uint8_t *plaintext, uint32_t plaintext_len,
  uint8_t *ciphertext, uint8_t *tag)
{
  EVP_CIPHER_CTX *ctx;
  int len;

  // Create and initialise the context
  if (!(ctx = EVP_CIPHER_CTX_new()))
    handleErrors();

  // Initialise the cipher with the key and IV
  if (1 != EVP_CipherInit_ex(ctx, alg, NULL, key, iv, enc))
    handleErrors();

  if(!enc && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, 16, tag) <= 0)
    handleErrors();

  // Set additional authenticated data
  if (1 != EVP_CipherUpdate(ctx, NULL, &len, aad, aad_len))
    handleErrors();

  // Process the data
  if (1 != EVP_CipherUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
    handleErrors();

  // Finalize last block
  if (1 != EVP_CipherFinal_ex(ctx, ciphertext + len, &len))
    return 0;

  /* Get the tag */
  if (enc && 1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, tag))
    handleErrors();

  /* Clean up */
  EVP_CIPHER_CTX_free(ctx);

  return 1;
}

void EverCrypt_OpenSSL_aes128_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  if(1 != openssl_aead(EVP_aes_128_gcm(), 1, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
}

uint32_t EverCrypt_OpenSSL_aes128_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return openssl_aead(EVP_aes_128_gcm(), 0, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

void EverCrypt_OpenSSL_aes256_gcm_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  if(1 != openssl_aead(EVP_aes_256_gcm(), 1, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
}

uint32_t EverCrypt_OpenSSL_aes256_gcm_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return openssl_aead(EVP_aes_256_gcm(), 0, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

void EverCrypt_OpenSSL_chacha20_poly1305_encrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                          uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  if(1 != openssl_aead(EVP_chacha20_poly1305(), 1, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
}

uint32_t EverCrypt_OpenSSL_chacha20_poly1305_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                         uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
  return openssl_aead(EVP_chacha20_poly1305(), 0, key, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
}

