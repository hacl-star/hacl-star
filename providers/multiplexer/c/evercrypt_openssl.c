#ifndef NO_OPENSSL
#include <openssl/evp.h>
#endif
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

#ifdef NO_OPENSSL

void EverCrypt_OpenSSL_aes256_gcm_encrypt(uint8_t *ciphertext,
                                          uint8_t *tag,
                                          uint8_t *key,
                                          uint8_t *iv,
                                          uint8_t *plaintext,
                                          uint32_t plaintext_len,
                                          uint8_t *aad,
                                          uint32_t aad_len) {
  KRML_HOST_EPRINTF("OpenSSL not available in this build\n");
  KRML_HOST_EXIT(255);
}

#else

void EverCrypt_OpenSSL_aes256_gcm_encrypt(uint8_t *ciphertext,
                                          uint8_t *tag,
                                          uint8_t *key,
                                          uint8_t *iv,
                                          uint8_t *plaintext,
                                          uint32_t plaintext_len,
                                          uint8_t *aad,
                                          uint32_t aad_len) {
  EVP_CIPHER_CTX *ctx;

  int iv_len = 12;
  int len;

  int ciphertext_len;

  /* Create and initialise the context */
  if (!(ctx = EVP_CIPHER_CTX_new()))
    handleErrors();

  /* Initialise the encryption operation. */
  if (1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_gcm(), NULL, NULL, NULL))
    handleErrors();

  /* Set IV length if default 12 bytes (96 bits) is not appropriate */
  if (1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, iv_len, NULL))
    handleErrors();

  /* Initialise key and IV */
  if (1 != EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv))
    handleErrors();

  /* Provide any AAD data. This can be called zero or more times as
   * required
   */
  if (1 != EVP_EncryptUpdate(ctx, NULL, &len, aad, aad_len))
    handleErrors();

  /* Provide the message to be encrypted, and obtain the encrypted output.
   * EVP_EncryptUpdate can be called multiple times if necessary
   */
  if (1 != EVP_EncryptUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
    handleErrors();
  ciphertext_len = len;

  /* Finalise the encryption. Normally ciphertext bytes may be written at
   * this stage, but this does not occur in GCM mode
   */
  if (1 != EVP_EncryptFinal_ex(ctx, ciphertext + len, &len))
    handleErrors();
  ciphertext_len += len;

  /* Get the tag */
  if (1 != EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, tag))
    handleErrors();

  /* Clean up */
  EVP_CIPHER_CTX_free(ctx);

  return;
}

#endif
