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
#include "Hacl_Hash.h"
#include <openssl/sha.h>

#include "sha2_vectors.h"
#include "test_helpers.h"


void ossl_sha2(uint8_t* hash, uint8_t* input, int len){
  SHA256_CTX ctx;
  SHA256_Init(&ctx);
  SHA256_Update(&ctx,input,len);
  SHA256_Final(hash,&ctx);
   //ctx = EVP_CIPHER_CTX_new();
   //EVP_EncryptInit_ex(ctx, EVP_chacha20(), NULL, key, nonce);
   //EVP_EncryptUpdate(ctx, cipher, &clen, plain, len);
   //EVP_EncryptFinal_ex(ctx, cipher + clen, &clen);
   //EVP_CIPHER_CTX_free(ctx);
}


#define ROUNDS 16384
#define SIZE   16384


bool print_result(uint8_t* comp, uint8_t* exp, int len) {
  return compare_and_print(len, comp, exp);
}

bool print_test(uint8_t* in, int in_len, uint8_t* exp224, uint8_t* exp256, uint8_t* exp384, uint8_t* exp512){
  uint8_t comp[64] = {0};

  Hacl_Hash_SHA2_hash_224(in,in_len,comp);
  printf("SHA2-224 (32-bit) Result:\n");
  bool ok = print_result(comp, exp224,28);

  Hacl_Hash_SHA2_hash_256(in,in_len,comp);
  printf("SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp, exp256,32) && ok;

  ossl_sha2(comp,in,in_len);
  printf("OpenSSL SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp, exp256,32) && ok;

  Hacl_Hash_SHA2_hash_384(in,in_len,comp);
  printf("SHA2-384 (32-bit) Result:\n");
  ok = print_result(comp, exp384,48) && ok;

  Hacl_Hash_SHA2_hash_512(in,in_len,comp);
  printf("SHA2-512 (32-bit) Result:\n");
  ok = print_result(comp, exp512,64) && ok;

  return ok;
}

int main(){

  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(sha2_test_vector); ++i) {
    ok &= print_test(vectors[i].input,vectors[i].input_len,vectors[i].tag_224,vectors[i].tag_256,vectors[i].tag_384,vectors[i].tag_512);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_224(plain,SIZE,plain);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_224(plain,SIZE,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff1 = b - a;
  double tdiff1 = t2 - t1;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_256(plain,SIZE,plain);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_256(plain,SIZE,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff2 = b - a;
  double tdiff2 = t2 - t1;

  for (int j = 0; j < ROUNDS; j++) {
    ossl_sha2(plain,plain,SIZE);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    ossl_sha2(plain,plain,SIZE);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff2a = b - a;
  double tdiff2a = t2 - t1;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_384(plain,SIZE,plain);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_384(plain,SIZE,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff3 = b - a;
  double tdiff3 = t2 - t1;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_512(plain,SIZE,plain);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_SHA2_hash_512(plain,SIZE,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff4 = b - a;
  double tdiff4 = t2 - t1;

  uint8_t res = plain[0];
  uint64_t count = ROUNDS * SIZE;
  printf("SHA2-224 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff1,cdiff1);
  printf("SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2,cdiff2);
  printf("OpenSSL SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2a,cdiff2a);
  printf("SHA2-384 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff3,cdiff3);
  printf("SHA2-512 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff4,cdiff4);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
