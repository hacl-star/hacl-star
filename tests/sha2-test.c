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

typedef uint64_t cycles;

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

static __inline__ cycles cpucycles_begin(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}

static __inline__ cycles cpucycles_end(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}



#define ROUNDS 16384
#define SIZE   16384


void print_time(clock_t tdiff, cycles cdiff){
  uint64_t count = ROUNDS * SIZE;
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff,(double)cdiff/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff,(double)tdiff/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff / CLOCKS_PER_SEC) * 1000000.0));
}

bool print_result(uint8_t* comp, uint8_t* exp, int len) {
  printf("computed:");
  for (int i = 0; i < len; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < len; i++)
    printf("%02x",exp[i]);
  printf("\n");
  bool ok = true;
  for (int i = 0; i < len; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  else printf("**FAILED**\n");
  return ok;
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

int main()
{

//
// Test 1
//

uint32_t test1_plaintext_len = vectors[0].input_len;

uint8_t *test1_plaintext = vectors[0].input;

uint8_t *test1_expected224 = vectors[0].tag_224;

uint8_t *test1_expected256 = vectors[0].tag_256;

uint8_t *test1_expected384 = vectors[0].tag_384;

uint8_t *test1_expected512 = vectors[0].tag_512;

//
// Test 2
//

uint32_t test2_plaintext_len = vectors[1].input_len;

uint8_t *test2_plaintext = vectors[1].input;

uint8_t *test2_expected224 = vectors[1].tag_224;

uint8_t *test2_expected256 = vectors[1].tag_256;

uint8_t *test2_expected384 = vectors[1].tag_384;

uint8_t *test2_expected512 = vectors[1].tag_512;

//
// Test 3
//

uint32_t test3_plaintext_len = vectors[2].input_len;

uint8_t *test3_plaintext = vectors[2].input;

uint8_t *test3_expected224 = vectors[2].tag_224;

uint8_t *test3_expected256 = vectors[2].tag_256;

uint8_t *test3_expected384 = vectors[2].tag_384;

uint8_t *test3_expected512 = vectors[2].tag_512;

//
// Test 4
//

uint32_t test4_plaintext_len = vectors[3].input_len;

uint8_t *test4_plaintext = vectors[3].input;

uint8_t *test4_expected224 = vectors[3].tag_224;

uint8_t *test4_expected256 = vectors[3].tag_256;

uint8_t *test4_expected384 = vectors[3].tag_384;

uint8_t *test4_expected512 = vectors[3].tag_512;

  bool ok = print_test(test1_plaintext,test1_plaintext_len,test1_expected224,test1_expected256,test1_expected384,test1_expected512);
  ok = print_test(test2_plaintext,test2_plaintext_len,test2_expected224,test2_expected256,test2_expected384,test2_expected512) && ok;
  ok = print_test(test3_plaintext,test3_plaintext_len,test3_expected224,test3_expected256,test3_expected384,test3_expected512) && ok;
  ok = print_test(test4_plaintext,test4_plaintext_len,test4_expected224,test4_expected256,test4_expected384,test4_expected512) && ok;

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
  double tdiff1 = (double)(t2 - t1)/CLOCKS_PER_SEC;

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
  double tdiff2 = (double)(t2 - t1)/CLOCKS_PER_SEC;

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
  double tdiff2a = (double)(t2 - t1)/CLOCKS_PER_SEC;

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
  double tdiff3 = (double)(t2 - t1)/CLOCKS_PER_SEC;

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
  double tdiff4 = (double)(t2 - t1)/CLOCKS_PER_SEC;
  
  uint8_t res = plain[0];
  printf("SHA2-224 (32-bit) PERF: %d\n",(int)res); print_time(tdiff1,cdiff1);
  printf("SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(tdiff2,cdiff2);
  printf("OpenSSL SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(tdiff2a,cdiff2a);
  printf("SHA2-384 (32-bit) PERF: %d\n",(int)res); print_time(tdiff3,cdiff3);
  printf("SHA2-512 (32-bit) PERF: %d\n",(int)res); print_time(tdiff4,cdiff4);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}

