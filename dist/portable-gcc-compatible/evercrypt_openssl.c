#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/rand.h>
#include <openssl/dh.h>
#include <openssl/ec.h>
#include <openssl/ecdh.h>
#include <inttypes.h>
#include <stdio.h>

#include "kremlin/internal/target.h"
#include "EverCrypt_OpenSSL.h"

/* KB, BB, JP: for now, we just ignore internal errors since the HACL* interface
 * has enough preconditions to make sure that no errors ever happen; if the
 * OpenSSL F* interface is strong enough, then any error here should be
 * catastrophic and not something we can recover from.
 * If we want to do something better, we can define:
 *   type error a = | Ok of a | Error of error_code
 * Then at the boundary we could catch the error, print it, then exit abruptly. */

#define handleErrors(...)                                                      \
  do {                                                                         \
    fprintf(stderr, "Error at %s:%d\n", __FILE__, __LINE__);                   \
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

  /* Initialise the cipher with the key and IV */
  if (1 != EVP_CipherInit_ex(ctx, NULL, NULL, NULL, iv, enc))
    handleErrors();

  /* Set additional authenticated data */
  if (aad_len > 0 && 1 != EVP_CipherUpdate(ctx, NULL, &len, aad, aad_len))
    handleErrors();

  /* Process the plaintext */
  if (enc && plaintext_len > 0
      && 1 != EVP_CipherUpdate(ctx, ciphertext, &len, plaintext, plaintext_len))
    handleErrors();

  /* Process the ciphertext */
  if (!enc && plaintext_len > 0
      && 1 != EVP_CipherUpdate(ctx, plaintext, &len, ciphertext, plaintext_len))
    handleErrors();

  /* Set the tag */
  if(!enc && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, 16, tag) <= 0)
    handleErrors();

  /* Finalize last block */
  if (1 != EVP_CipherFinal_ex(ctx, ciphertext + len, &len))
    return 0;

  /* Get the tag */
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
#ifdef OPENSSL_IS_BORINGSSL
  handleErrors();
#else
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_chacha20_poly1305(), key);
  if(NULL == ctx || 1 != openssl_aead(ctx, 1, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag))
    handleErrors();
  openssl_free(ctx);
#endif
}

uint32_t EverCrypt_OpenSSL_chacha20_poly1305_decrypt(uint8_t *key, uint8_t *iv, uint8_t *aad, uint32_t aad_len,
                                                     uint8_t *plaintext, uint32_t plaintext_len, uint8_t *ciphertext, uint8_t *tag)
{
#ifdef OPENSSL_IS_BORINGSSL
  handleErrors();
  return 0;
#else
  EVP_CIPHER_CTX *ctx = openssl_create(EVP_chacha20_poly1305(), key);
  int ret = openssl_aead(ctx, 0, iv, aad, aad_len, plaintext, plaintext_len, ciphertext, tag);
  openssl_free(ctx);
  return ret;
#endif
}

void* EverCrypt_OpenSSL_aead_create(uint8_t alg, uint8_t *key)
{
  const EVP_CIPHER *a;
  EVP_CIPHER_CTX *ctx;
  
  if(alg == 0) a = EVP_aes_128_gcm();
  else if(alg == 1) a = EVP_aes_256_gcm();
#ifndef OPENSSL_IS_BORINGSSL
  else if(alg == 2) a = EVP_chacha20_poly1305();
#endif
  else{ handleErrors(); return NULL; }

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

uint32_t EverCrypt_OpenSSL_dh_keygen(void *st, uint8_t *pub)
{
  DH *dh = (DH*)st;
  const BIGNUM *opub, *opriv;
  DH_generate_key(dh);
  DH_get0_key(dh, &opub, &opriv);
  BN_bn2bin(opub, pub);
  return BN_num_bytes(opub);
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

void* EverCrypt_OpenSSL_ecdh_load_curve(EverCrypt_OpenSSL_ec_curve g)
{
  EC_KEY *k = NULL;
  switch (g) {
    case EverCrypt_OpenSSL_ECC_P256:
      k = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);
      break;
    case EverCrypt_OpenSSL_ECC_P384:
      k = EC_KEY_new_by_curve_name(NID_secp384r1);
      break;
    case EverCrypt_OpenSSL_ECC_P521:
      k = EC_KEY_new_by_curve_name(NID_secp521r1);
      break;
    case EverCrypt_OpenSSL_ECC_X25519:
      k = EC_KEY_new_by_curve_name(NID_X25519);
      break;
#ifdef OPENSSL_IS_BORINGSSL
    case EverCrypt_OpenSSL_ECC_X448:
      handleErrors();
      break;
#else
    case EverCrypt_OpenSSL_ECC_X448:
      k = EC_KEY_new_by_curve_name(NID_X448);
      break;
#endif
  }
  return (void*)k;
}

void EverCrypt_OpenSSL_ecdh_free_curve(void* st)
{
  EC_KEY_free((EC_KEY*)st);
}

void dump(const unsigned char buffer[], size_t len)
{
  size_t i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i] & 0xFF);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

void EverCrypt_OpenSSL_ecdh_keygen(void* st, uint8_t *outx, uint8_t *outy)
{
  EC_KEY *k = (EC_KEY*)st;
  EC_KEY_generate_key(k);
  
  const EC_GROUP *g = EC_KEY_get0_group(k);
  const EC_POINT *p = EC_KEY_get0_public_key(k);
  size_t len = (EC_GROUP_get_degree(g) + 7) / 8;
  
  BIGNUM *x = BN_new(), *y = BN_new();
  EC_POINT_get_affine_coordinates_GFp(g, p, x, y, NULL);

#ifdef OPENSSL_IS_BORINGSSL
  BN_bn2bin_padded(outx, len, x);
  BN_bn2bin_padded(outy, len, y);
#else
  BN_bn2binpad(x, outx, len);
  BN_bn2binpad(y, outy, len);
#endif

  BN_free(y);
  BN_free(x);
}

uint32_t EverCrypt_OpenSSL_ecdh_compute(void* st,
  uint8_t *inx, uint8_t *iny, uint8_t *out)
{
  EC_KEY *k = (EC_KEY*)st;
  const EC_GROUP *g = EC_KEY_get0_group(k);
  EC_POINT *p = EC_POINT_new(g);
  size_t len = (EC_GROUP_get_degree(g) + 7) / 8;
  
  BIGNUM *px = BN_bin2bn(inx, len, NULL);
  BIGNUM *py = BN_bin2bn(iny, len, NULL);
  
  EC_POINT_set_affine_coordinates_GFp(g, p, px, py, NULL);
  int olen = ECDH_compute_key((uint8_t *)out, len, p, k, NULL);

  BN_free(px);
  BN_free(py);
  EC_POINT_free(p);
  
  return olen < 0 ? 0 : olen;
}

/*
bool CoreCrypto_ec_is_on_curve_(CoreCrypto_ec_params *x0,
                               CoreCrypto_ec_point *x1) {

  EC_KEY *k = key_of_core_crypto_curve(x0->curve);
  const EC_GROUP *group = EC_KEY_get0_group(k);

  EC_POINT *point = EC_POINT_new(group);
  BIGNUM *ppx = BN_bin2bn((uint8_t *)x1->ecx.data, x1->ecx.length, NULL);
  BIGNUM *ppy = BN_bin2bn((uint8_t *)x1->ecy.data, x1->ecy.length, NULL);
  EC_POINT_set_affine_coordinates_GFp(group, point, ppx, ppy, NULL);

  bool ret = EC_POINT_is_on_curve(group, point, NULL);

  BN_free(ppy);
  BN_free(ppx);
  EC_POINT_free(point);
  EC_KEY_free(k);
  return ret;
}

*/
