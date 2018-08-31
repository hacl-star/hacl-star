#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/dh.h>
#include <openssl/ec.h>
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


/* OpenSSL PRNG */

uint32_t EverCrypt_OpenSSL_random_init()
{
  if(RAND_status()) return 1;
  return RAND_poll();
}

void EverCrypt_OpenSSL_random_sample(uint32_t len, uint8_t *out)
{
  if(1 != RAND_bytes(out, len))
    handleErrors();
}

/* OpenSSL AEAD */

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

/* Diffie-Hellman */

void* EverCrypt_OpenSSL_dh_load_group(
  uint8_t *dh_p,  uint32_t dh_p_len,
  uint8_t *dh_g,  uint32_t dh_g_len,
  uint8_t *dh_q,  uint32_t dh_q_len)
{
  DH *dh = DH_new();
  if(dh == NULL) handleErrors();

  BIGNUM *p = BN_bin2bn(dh_p, dh_p_len, NULL);
  BIGNUM *g = BN_bin2bn(dh_g, dh_g_len, NULL);
  BIGNUM *q = dh_q_len ? BN_bin2bn(dh_q, dh_q_len, NULL) : NULL;
  DH_set0_pqg(dh, p, q, g);
  
  return (void*)dh;
}

void EverCrypt_OpenSSL_dh_free_group(void *g)
{
  DH_free((DH*)g);
}

K___uint32_t_uint32_t EverCrypt_OpenSSL_dh_keygen(void *g, uint8_t *priv, uint8_t *pub)
{
  const BIGNUM *opub, *opriv;
  DH_get0_key((DH*)g, &opub, &opriv);
  BN_bn2bin(opub, pub);
  BN_bn2bin(opriv, priv);
  K___uint32_t_uint32_t ret =
    {
     .fst = BN_num_bytes(opriv),
     .snd = BN_num_bytes(opub)
    };
  return ret;
}

uint32_t EverCrypt_OpenSSL_dh_compute(void *g,
  uint8_t *pub, uint32_t pub_len,
  uint8_t *out)
{
  BIGNUM *opub = BN_bin2bn(pub, pub_len, NULL);
  
  if(DH_compute_key(out, opub, (DH*)g) < 0)
    handleErrors();
  
  BN_free(opub);
  return DH_size((DH*)g);
}
