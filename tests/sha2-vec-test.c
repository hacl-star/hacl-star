#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <stdbool.h>

#include "Hacl_SHA2_Scalar32.h"
#include "Hacl_SHA2_Vec128.h"
#include "Hacl_SHA2_Vec256.h"

#include "sha2_vectors.h"
#include "sha2vec_vectors.h"
#include "test_helpers.h"

#include <openssl/sha.h>

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

bool print_test1(uint8_t* in, int in_len, uint8_t* exp256){
  uint8_t comp[32] = {0};
  Hacl_SHA2_Scalar32_sha256(comp,in_len,in);
  printf("NEW SHA2-256 (32-bit) Result:\n");
  bool ok = print_result(comp,exp256,32);

  ossl_sha2(comp,in,in_len);
  printf("OpenSSL SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp,exp256,32) && ok;

  return ok;
}

bool print_test4(uint8_t* in, uint8_t* in1, uint8_t* in2, uint8_t* in3, int in_len, uint8_t* exp, uint8_t* exp1, uint8_t* exp2, uint8_t* exp3){
  uint8_t comp[32] = {0};
  uint8_t comp1[32] = {0};
  uint8_t comp2[32] = {0};
  uint8_t comp3[32] = {0};

  Hacl_SHA2_Vec128_sha256_4(comp,comp1,comp2,comp3,in_len,in,in1,in2,in3);
  printf("VEC4 SHA2-256 (32-bit) Result:\n");
  bool ok = print_result(comp, exp,32);
  ok = print_result(comp1,exp1,32) && ok;
  ok = print_result(comp2,exp2,32) && ok;
  ok = print_result(comp3,exp3,32) && ok;

  return ok;
}

bool print_test8(uint8_t* in, uint8_t* in1, uint8_t* in2, uint8_t* in3, uint8_t* in4, uint8_t* in5, uint8_t* in6, uint8_t* in7, int in_len,
		 uint8_t* exp, uint8_t* exp1, uint8_t* exp2, uint8_t* exp3, uint8_t* exp4, uint8_t* exp5, uint8_t* exp6, uint8_t* exp7){
  uint8_t comp[32] = {0};
  uint8_t comp1[32] = {0};
  uint8_t comp2[32] = {0};
  uint8_t comp3[32] = {0};
  uint8_t comp4[32] = {0};
  uint8_t comp5[32] = {0};
  uint8_t comp6[32] = {0};
  uint8_t comp7[32] = {0};

  Hacl_SHA2_Vec256_sha256_8(comp,comp1,comp2,comp3,comp4,comp5,comp6,comp7,in_len,in,in1,in2,in3,in4,in5,in6,in7);
  printf("VEC8 SHA2-256 (32-bit) Result:\n");
  bool ok = print_result(comp, exp,32);
  ok = print_result(comp1,exp1,32) && ok;
  ok = print_result(comp2,exp2,32) && ok;
  ok = print_result(comp3,exp3,32) && ok;
  ok = print_result(comp4,exp4,32) && ok;
  ok = print_result(comp5,exp5,32) && ok;
  ok = print_result(comp6,exp6,32) && ok;
  ok = print_result(comp7,exp7,32) && ok;

  return ok;
}


int main()
{
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(sha2_test_vector); ++i) {
    ok &= print_test1(vectors[i].input,vectors[i].input_len,vectors[i].tag_256);
  }


  ok &= print_test4(vectors_vec[0].input,vectors_vec[1].input,vectors_vec[2].input,vectors_vec[3].input,vectors_vec[0].input_len,
		    vectors_vec[0].tag_256,vectors_vec[1].tag_256,vectors_vec[2].tag_256,vectors_vec[3].tag_256);

  ok &= print_test8(vectors_vec[0].input,vectors_vec[1].input,vectors_vec[2].input,vectors_vec[3].input,
		    vectors_vec[4].input,vectors_vec[5].input,vectors_vec[6].input,vectors_vec[7].input, vectors_vec[0].input_len,
		    vectors_vec[0].tag_256,vectors_vec[1].tag_256,vectors_vec[2].tag_256,vectors_vec[3].tag_256,
		    vectors_vec[4].tag_256,vectors_vec[5].tag_256,vectors_vec[6].tag_256,vectors_vec[7].tag_256);


  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Scalar32_sha256(plain,SIZE,plain);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Scalar32_sha256(plain,SIZE,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff2n = b - a;
  double tdiff2n = (double)(t2 - t1);


  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Vec128_sha256_4(plain,plain+32,plain+64,plain+96,SIZE,plain,plain,plain,plain);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Vec128_sha256_4(plain,plain+32,plain+64,plain+96,SIZE,plain,plain,plain,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff2v = b - a;
  double tdiff2v = (double)(t2 - t1);


  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Vec256_sha256_8(plain,plain+32,plain+64,plain+96,plain+128,plain+160,plain+192,plain+224,SIZE,plain,plain,plain,plain,plain,plain,plain,plain);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Vec256_sha256_8(plain,plain+32,plain+64,plain+96,plain+128,plain+160,plain+192,plain+224,SIZE,plain,plain,plain,plain,plain,plain,plain,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff2v8 = b - a;
  double tdiff2v8 = (double)(t2 - t1);


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
  double tdiff2a = (double)(t2 - t1);


  uint8_t res = plain[0];
  uint64_t count = ROUNDS * SIZE;
  printf("NEW SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2n,cdiff2n);
  printf("VEC4 SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2v,cdiff2v);
  printf("VEC8 SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2v8,cdiff2v8);
  printf("OpenSSL SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2a,cdiff2a);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
