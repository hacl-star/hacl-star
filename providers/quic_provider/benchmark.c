/*
 *  Benchmark demonstration program
 *
 *  Copyright (C) 2006-2016, ARM Limited, All Rights Reserved
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); you may
 *  not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  This file is part of mbed TLS (https://tls.mbed.org)
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <openssl/evp.h>
#include <inttypes.h>

#include "timing.h"
#include "EverCrypt.h"

// How long to measure for KB/s figures
#define MEASUREMENT_TIME 2
// How many iterations to run for cycles/byte figures
#define ITERATIONS(bsize) (uint64_t)(6553500 / bsize) //(bsize <= 2048 ? 4000 : (bsize <= 8096 ? 2000 : 1000))
#define HEADER_FORMAT   "  %-24s :  "

#define TIME_AND_TSC( TITLE, BUFSIZE, CODE )                            \
do {                                                                    \
    uint64_t ii, jj, tsc;                                               \
    uint64_t cnt = ITERATIONS(BUFSIZE);                                 \
                                                                        \
    printf( HEADER_FORMAT, TITLE );                                     \
    fflush( stdout );                                                   \
                                                                        \
    set_alarm( MEASUREMENT_TIME );                                      \
    for( ii = 1; ! timing_alarmed; ii++ )                               \
    {                                                                   \
        CODE;                                                           \
    }                                                                   \
                                                                        \
    tsc = timing_hardclock();                                           \
    for( jj = 0; jj < cnt; jj++ )                                       \
    {                                                                   \
        CODE;                                                           \
    }                                                                   \
                                                                        \
    printf( "%9lu KiB/s,  %9f cycles/byte\n",                           \
                     (ii * BUFSIZE) / (MEASUREMENT_TIME * 1024),        \
                     (double)(timing_hardclock() - tsc ) /(double)( jj * BUFSIZE ) ); \
} while( 0 )

#define TIME_PUBLIC( TITLE, TYPE, CODE )                                \
do {                                                                    \
    unsigned long ii, tsc;                                              \
    int ret;                                                            \
                                                                        \
    printf( HEADER_FORMAT, TITLE );                                     \
    fflush( stdout );                                                   \
    set_alarm( 3 );                                                     \
    tsc = timing_hardclock();                                           \
                                                                        \
    ret = 0;                                                            \
    for( ii = 1; ! timing_alarmed && ! ret ; ii++ )                     \
    {                                                                   \
        CODE;                                                           \
    }                                                                   \
                                                                        \
    if( ret != 0 )                                                      \
    {                                                                   \
        PRINT_ERROR;                                                    \
    }                                                                   \
    else                                                                \
    {                                                                   \
        printf( "%6lu " TYPE "/s (%9lu cycles/" TYPE ")\n", ii/3,       \
			      (timing_hardclock() - tsc) / ii );        \
    }                                                                   \
} while( 0 )

void bench_aead(Spec_AEAD_alg a, const unsigned char *alg, size_t plain_len)
{
  unsigned char tag[16], key[32], iv[12];
  unsigned char *plain = malloc(65536);
  unsigned char *cipher = malloc(65536);
  EverCrypt_AEAD_state_s *s;
  EverCrypt_AEAD_create_in(a, &s, key);

  char title[128];
  sprintf(title, "ENC %s[%5d]", alg, plain_len);

  TIME_AND_TSC(title, plain_len,
    EverCrypt_AEAD_encrypt(s, iv, "", 0, plain, plain_len, cipher, tag);
  );

  sprintf(title, "DEC %s[%5d]", alg, plain_len);

  TIME_AND_TSC(title, plain_len,
    EverCrypt_AEAD_decrypt(s, iv, "", 0, cipher, plain_len, tag, plain);
  );

  EverCrypt_AEAD_free(s);
  free(plain);
  free(cipher);
}

void bench_hash(Spec_Hash_Definitions_hash_alg a, const unsigned char *alg, size_t plain_len)
{
  unsigned char *plain = malloc(plain_len);

  char title[128];
  uint8_t hash[64];
  sprintf(title, "HASH %s[%5d]", alg, plain_len);

  TIME_AND_TSC(title, plain_len,
    EverCrypt_Hash_hash(a, hash, plain, plain_len)
  );

  free(plain);
}

void run() //EverCrypt_AutoConfig_cfg cfg)
{
  /*
  switch(cfg.preferred)
  {
    case EverCrypt_AutoConfig_Hacl:
      printf(" ================= Prefer Hacl ===================\n");
      break;
    case EverCrypt_AutoConfig_Vale:
      printf(" ================= Prefer Vale ===================\n");
      break;
    case EverCrypt_AutoConfig_OpenSSL:
      printf(" =============== Prefer OpenSSL ==================\n");
      break;
    case EverCrypt_AutoConfig_BCrypt:
      printf(" ================ Prefer BCrypt ==================\n");
      break;
  }

  EverCrypt_AutoConfig_init(cfg);
  */
  EverCrypt_AutoConfig2_init();
  size_t i;

  for(i=4; i<=65536; i<<=1)
    bench_aead(Spec_AEAD_AES128_GCM, "AES128-GCM", i);

  for(i=4; i<=65536; i<<=1)
    bench_aead(Spec_AEAD_AES256_GCM, "AES256-GCM", i);

  for(i=4; i<=65536; i<<=1)
    bench_aead(Spec_AEAD_CHACHA20_POLY1305, "CHA20-P1305", i);

  for(i=4; i<=65536; i<<=1)
    bench_hash(Spec_Hash_Definitions_SHA2_256, "SHA256", i);
  for(i=4; i<=65536; i<<=1)
    bench_hash(Spec_Hash_Definitions_SHA2_384, "SHA384", i);
  for(i=4; i<=65536; i<<=1)
    bench_hash(Spec_Hash_Definitions_SHA2_512, "SHA512", i);
  for(i=4; i<=65536; i<<=1)
    bench_hash(Spec_Hash_Definitions_SHA1, "SHA1", i);
  for(i=4; i<=65536; i<<=1)
    bench_hash(Spec_Hash_Definitions_MD5, "MD5", i);
}

void handleErrors()
{
  printf("Fatal error!\n");
  exit(1);
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

void bench_openssl(const EVP_CIPHER *a, const unsigned char *alg, size_t plain_len)
{
  unsigned char tag[16], key[32], iv[12];
  unsigned char *plain = malloc(65536);
  unsigned char *cipher = malloc(65536);
  EVP_CIPHER_CTX *ctx;

  if (!(ctx = EVP_CIPHER_CTX_new()))
    handleErrors();

  if (1 != EVP_CipherInit_ex(ctx, a, NULL, key, NULL, -1))
  {
    EVP_CIPHER_CTX_free(ctx);
    handleErrors();
  }

  char title[128];
  sprintf(title, "ENC %s[%5d]", alg, plain_len);

  TIME_AND_TSC(title, plain_len,
    openssl_aead(ctx, 1, iv, "", 0, plain, plain_len, cipher, tag);
  );

  sprintf(title, "DEC %s[%5d]", alg, plain_len);

  TIME_AND_TSC(title, plain_len,
    openssl_aead(ctx, 0, iv, "", 0, plain, plain_len, cipher, tag);
  );

  EVP_CIPHER_CTX_free(ctx);
  free(plain);
  free(cipher);
}


void run_openssl()
{
  size_t i;

  for(i=4; i<=65536; i<<=1)
    bench_openssl(EVP_aes_128_gcm(), "AES128-GCM", i);

  for(i=4; i<=65536; i<<=1)
    bench_openssl(EVP_aes_256_gcm(), "AES256-GCM", i);
}

int main(int argc, char **argv)
{
//  EverCrypt_AutoConfig_cfg cfg = { .tag = EverCrypt_AutoConfig_Prefer };

/*
  if(argc <= 1)
  {
    for(uint8_t i=0; i<4; i++)
    {
      cfg.preferred = i;
      run(cfg);
    }
  }
  else
  {
    uint8_t alg = 0;
    if(!memcmp(argv[1], "hacl", 5)) alg = 0;
    else if(!memcmp(argv[1], "vale", 5)) alg = 1;
    else if(!memcmp(argv[1], "openssl", 8)) alg = 2;
    else if(!memcmp(argv[1], "bcrypt", 7)) alg = 3;
    else {
      printf("Valid arguments are: hacl, vale, openssl, bcrypt\n");
      return 1;
    }
    cfg.preferred = alg;
    run(cfg);
  }
*/
  printf("*** EverCrypt bencharks ***\n\n");
  run();
  printf("*** OpenSSL comparison ***\n\n");
  run_openssl();
  return 0;
}

