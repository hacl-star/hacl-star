#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <stdbool.h>
#include <sodium.h>

#include "Hacl_Blake2s_32.h"
#include "Hacl_Blake2b_32.h"

#include "test_helpers.h"

#include "EverCrypt_AutoConfig2.h"
#include "blake2_vectors.h"

#include <openssl/core.h>
#include <openssl/evp.h>

#define ROUNDS 16384
#define SIZE   8196

EVP_MAC *evp_mac_blake2s;
EVP_MAC *evp_mac_blake2b;

void sodium_blake2s_mac(int in_len, uint8_t* in, int key_len, uint8_t* key,
                        unsigned int out_len, uint8_t* out) {
    if(key == NULL || key_len == 0) {
        printf("sodium_blake2s_mac: the key mustn't be NULL\n");
        return;
    }
    int res = 0;
    EVP_MAC_CTX *evp_ctx = EVP_MAC_CTX_new(evp_mac_blake2s);
    if(!evp_ctx) {
        printf("sodium_blake2s_mac: context creation failed\n");
        return;
    }
    size_t outl = 0;

    OSSL_PARAM params[3];
    params[0] = OSSL_PARAM_construct_end();

    res = EVP_MAC_init(evp_ctx, key, key_len, params);
    if(res == 0) {
        printf("sodium_blake2s_mac: EVP_MAC_init failed\n");
    }
    res = EVP_MAC_update(evp_ctx, in, in_len);
    if(res == 0) {
        printf("sodium_blake2s_mac: EVP_MAC_update failed\n");
    }
    res = EVP_MAC_final(evp_ctx, out, &outl, out_len);
    if(res == 0) {
        printf("sodium_blake2s_mac: EVP_MAC_final failed\n");
    }

    EVP_MAC_CTX_free(evp_ctx);
}

void sodium_blake2b_mac(int in_len, uint8_t* in, int key_len, uint8_t* key,
                        unsigned int out_len, uint8_t* out) {
    if(key == NULL || key_len == 0) {
        printf("sodium_blake2b_mac: the key mustn't be NULL\n");
        return;
    }
    int res = 0;
    EVP_MAC_CTX *evp_ctx = EVP_MAC_CTX_new(evp_mac_blake2b);
    if(!evp_ctx) {
        printf("sodium_blake2b_mac: context creation failed\n");
        return;
    }
    size_t outl = 0;

    OSSL_PARAM params[3];
    params[0] = OSSL_PARAM_construct_end();

    res = EVP_MAC_init(evp_ctx, key, key_len, params);
    if(res == 0) {
        printf("sodium_blake2b_mac: EVP_MAC_init failed\n");
    }
    res = EVP_MAC_update(evp_ctx, in, in_len);
    if(res == 0) {
        printf("sodium_blake2b_mac: EVP_MAC_update failed\n");
    }
    res = EVP_MAC_final(evp_ctx, out, &outl, out_len);
    if(res == 0) {
        printf("sodium_blake2b_mac: EVP_MAC_final failed\n");
    }

    EVP_MAC_CTX_free(evp_ctx);
}

bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

bool print_test2b(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp){
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);
  bool ok = true;

  sodium_blake2b_mac(in_len,in,key_len,key,exp_len,comp);
  printf("testing blake2b (OpenSSL) vec-32:\n");
  ok = print_result(exp_len,comp,exp) && ok;

  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2b_32_blake2b(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2b vec-32:\n");
  ok = print_result(exp_len,comp,exp) && ok;
  return ok;
}

bool print_test2s(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp) {
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  bool ok = true;

  if(key_len > 0) {
    sodium_blake2s_mac(in_len,in,key_len,key,exp_len,comp);
    printf("testing blake2s (OpenSSL) vec-32:\n");
    ok = print_result(exp_len,comp,exp) && ok;
  }
  else {
      printf("Ignoring a test for OpenSSL: OpenSSL only supports keyed-hash\n");
  }

  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2s_32_blake2s(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2s vec-32:\n");
  ok = print_result(exp_len,comp,exp) && ok;

  return ok;
}


int main()
{
  EverCrypt_AutoConfig2_init();
  evp_mac_blake2s = EVP_MAC_fetch(NULL, "BLAKE2SMAC", NULL);
  evp_mac_blake2b = EVP_MAC_fetch(NULL, "BLAKE2BMAC", NULL);
  if(!evp_mac_blake2s || !evp_mac_blake2b) {
      printf("OpenSSL initialization failed\n");
      return EXIT_FAILURE;
  }
  bool ok = true;
  for (int i = 0; i < sizeof(vectors2s)/sizeof(blake2_test_vector); ++i) {
    ok &= print_test2s(vectors2s[i].input_len,vectors2s[i].input,vectors2s[i].key_len,vectors2s[i].key,vectors2s[i].expected_len,vectors2s[i].expected);
  }
  for (int i = 0; i < sizeof(vectors2b)/sizeof(blake2_test_vector); ++i) {
    ok &= print_test2b(vectors2b[i].input_len,vectors2b[i].input,vectors2b[i].key_len,vectors2b[i].key,vectors2b[i].expected_len,vectors2b[i].expected);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint64_t keylen2s = 32;
  uint8_t key2s[32];
  uint64_t keylen2b = 64;
  uint8_t key2b[64];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);
  memset(key2s,'K',32);
  memset(key2b,'K',64);

  // Blake2S
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,keylen2s,key2s);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,keylen2s,key2s);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff1 = b - a;
  double tdiff1 = t2 - t1;

  // Blake2B
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,keylen2b,key2b);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,keylen2b,key2b);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff2 = b - a;
  double tdiff2 = t2 - t1;

  // OpenSSL Blake2S
  for (int j = 0; j < ROUNDS; j++) {
      sodium_blake2s_mac(SIZE,plain,keylen2s,key2s,32,plain);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
      sodium_blake2s_mac(SIZE,plain,keylen2s,key2s,32,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff3 = b - a;
  double tdiff3 = t2 - t1;

  // OpenSSL Blake2B
  for (int j = 0; j < ROUNDS; j++) {
      sodium_blake2b_mac(SIZE,plain,keylen2b,key2b,32,plain);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
      sodium_blake2b_mac(SIZE,plain,keylen2b,key2b,32,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff4 = b - a;
  double tdiff4 = t2 - t1;

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2S (Vec 32-bit):\n"); print_time(count,tdiff1,cdiff1);
  printf("Blake2B (Vec 64-bit):\n"); print_time(count,tdiff2,cdiff2);
  printf("Blake2S (OpenSSL):\n"); print_time(count,tdiff3,cdiff3);
  printf("Blake2B (OpenSSL):\n"); print_time(count,tdiff4,cdiff4);

  // Cleanup
  EVP_MAC_free(evp_mac_blake2s);
  EVP_MAC_free(evp_mac_blake2b);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
