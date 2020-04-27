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

#include "Hacl_Chacha20_Vec32.h"
#include "Hacl_Chacha20_Vec128.h"
#include "Hacl_Chacha20_Vec256.h"

#include "test_helpers.h"
#include "chacha20_vectors.h"

#include <openssl/evp.h>
#include "chacha.h"
//#define ossl_chacha20(cipher,plain,len,nonce,key,ctr) (CRYPTO_chacha_20(cipher,plain,len,nonce,key,ctr))

void ossl_chacha20(uint8_t* cipher, uint8_t* plain, int len, uint8_t* key, uint8_t* nonce){
   ChaCha20_ctr32(cipher, plain, len, (uint32_t*)key, (uint32_t*)nonce);
   //EVP_CIPHER_CTX *ctx;
   //int clen;
   //ctx = EVP_CIPHER_CTX_new();
   //EVP_EncryptInit_ex(ctx, EVP_chacha20(), NULL, key, nonce);
   //EVP_EncryptUpdate(ctx, cipher, &clen, plain, len);
   //EVP_EncryptFinal_ex(ctx, cipher + clen, &clen);
   //EVP_CIPHER_CTX_free(ctx);
}

#include "impl.h"

extern void chacha20_impl(unsigned char *out, const unsigned char *in, unsigned long long inlen,
			  const unsigned char *k, const unsigned char *n, unsigned int counter);


#define ROUNDS 100000
#define SIZE   8192

bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

bool print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* nonce, uint8_t* exp){
  uint8_t comp[in_len];
  memset(comp, 0, in_len * sizeof comp[0]);

  Hacl_Chacha20_Vec32_chacha20_encrypt_32(in_len,comp,in,key,nonce,1);
  printf("Chacha20 (32-bit) Result:\n");
  bool ok = print_result(in_len,comp,exp);

  Hacl_Chacha20_Vec128_chacha20_encrypt_128(in_len,comp,in,key,nonce,1);
  printf("Chacha20 (128-bit) Result:\n");
  ok = ok && print_result(in_len,comp,exp);

  Hacl_Chacha20_Vec256_chacha20_encrypt_256(in_len,comp,in,key,nonce,1);
  printf("Chacha20 (256-bit) Result:\n");
  ok = ok && print_result(in_len,comp,exp);

  chacha20_impl(comp,in,in_len,key,nonce,1);
  printf("Jasmin (avx2) Result:\n");
  ok = ok && print_result(in_len,comp,exp);

  uint8_t c_n[16] = {0};
  c_n[0] = 1; // store a counter
  memcpy(c_n + 4, nonce, 12 * sizeof nonce[0]); // store a nonce
  ossl_chacha20(comp,in,in_len,key,c_n);
  printf("OpenSSL Result:\n");
  ok = ok && print_result(in_len,comp,exp);

  return ok;
}

int main() {
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(chacha20_test_vector); ++i) {
    ok &= print_test(vectors[i].input_len,vectors[i].input,vectors[i].key,vectors[i].nonce,vectors[i].cipher);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint8_t key[16];
  uint8_t nonce[12];
  cycles a,b;
  clock_t t1,t2;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec32_chacha20_encrypt_32(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec32_chacha20_encrypt_32(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc1 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec128_chacha20_encrypt_128(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec128_chacha20_encrypt_128(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc2 = b - a;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec256_chacha20_encrypt_256(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_Vec256_chacha20_encrypt_256(SIZE,plain,plain,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc3 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  uint8_t ctr_nonce[16] = { 0 };
  ctr_nonce[0] = 1;
  memset(ctr_nonce + (uint32_t)4U,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    ossl_chacha20(plain,plain,SIZE,key,ctr_nonce);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    ossl_chacha20(plain,plain,SIZE,key,ctr_nonce);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff4 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc4 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    chacha20_impl(plain,plain,SIZE,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    chacha20_impl(plain,plain,SIZE,key,nonce,1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff5 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  uint64_t cyc5 = b - a;

  uint64_t count = ROUNDS * SIZE;
  printf("32-bit Chacha20\n"); print_time(count,diff1,cyc1);
  printf("128-bit Chacha20\n"); print_time(count,diff2,cyc2);
  printf("256-bit Chacha20\n"); print_time(count,diff3,cyc3);
  printf("OpenSSL Chacha20\n"); print_time(count,diff4,cyc4);
  printf("Jasmin (avx2) Chacha20\n"); print_time(count,diff5,cyc5);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
