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

#include "test_helpers.h"

#include "Hacl_SHA2_Scalar32.h"

#if defined(HACL_CAN_COMPILE_VEC128)
#include "Hacl_SHA2_Vec128.h"
#endif

#if defined(HACL_CAN_COMPILE_VEC256)
#include "Hacl_SHA2_Vec256.h"
#endif

#include "EverCrypt_AutoConfig2.h"

#include "sha2_vectors.h"
#include "sha2mb_vectors.h"


#define ROUNDS 16384
#define SIZE   16384


bool print_result(uint8_t* comp, uint8_t* exp, int len) {
  return compare_and_print(len, comp, exp);
}

bool print_test1(uint8_t* in, int in_len, uint8_t* exp256, uint8_t* exp512){
  uint8_t comp256[32] = {0};
  uint8_t comp512[64] = {0};

  Hacl_SHA2_Scalar32_sha256(comp256,in_len,in);
  printf("NEW SHA2-256 (32-bit) Result:\n");
  bool ok = print_result(comp256,exp256,32);

  Hacl_SHA2_Scalar32_sha512(comp512,in_len,in);
  printf("NEW SHA2-512 (32-bit) Result:\n");
  ok = print_result(comp512,exp512,64) && ok;

  return ok;
}

bool print_test4(uint8_t* in, uint8_t* in1, uint8_t* in2, uint8_t* in3, int in_len, uint8_t* exp, uint8_t* exp1, uint8_t* exp2, uint8_t* exp3){
  uint8_t comp[32] = {0};
  uint8_t comp1[32] = {0};
  uint8_t comp2[32] = {0};
  uint8_t comp3[32] = {0};

#if defined(HACL_CAN_COMPILE_VEC128)
  Hacl_SHA2_Vec128_sha256_4(comp,comp1,comp2,comp3,in_len,in,in1,in2,in3);
  printf("VEC4 SHA2-256 (32-bit) Result:\n");
  bool ok = print_result(comp, exp,32);
  ok = print_result(comp1,exp1,32) && ok;
  ok = print_result(comp2,exp2,32) && ok;
  ok = print_result(comp3,exp3,32) && ok;
#endif

  return ok;
}

bool print_test4_512(uint8_t* in, uint8_t* in1, uint8_t* in2, uint8_t* in3, int in_len, uint8_t* exp, uint8_t* exp1, uint8_t* exp2, uint8_t* exp3){
  uint8_t comp[64] = {0};
  uint8_t comp1[64] = {0};
  uint8_t comp2[64] = {0};
  uint8_t comp3[64] = {0};

  bool ok = true;
#if defined(HACL_CAN_COMPILE_VEC256)
  Hacl_SHA2_Vec256_sha512_4(comp,comp1,comp2,comp3,in_len,in,in1,in2,in3);
  printf("VEC4 SHA2-512 (32-bit) Result:\n");
  ok = print_result(comp, exp,64);
  ok = print_result(comp1,exp1,64) && ok;
  ok = print_result(comp2,exp2,64) && ok;
  ok = print_result(comp3,exp3,64) && ok;
#endif

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

  bool ok = true;
#if defined(HACL_CAN_COMPILE_VEC256)
  Hacl_SHA2_Vec256_sha256_8(comp,comp1,comp2,comp3,comp4,comp5,comp6,comp7,in_len,in,in1,in2,in3,in4,in5,in6,in7);
  printf("VEC8 SHA2-256 (32-bit) Result:\n");
  ok = print_result(comp, exp,32);
  ok = print_result(comp1,exp1,32) && ok;
  ok = print_result(comp2,exp2,32) && ok;
  ok = print_result(comp3,exp3,32) && ok;
  ok = print_result(comp4,exp4,32) && ok;
  ok = print_result(comp5,exp5,32) && ok;
  ok = print_result(comp6,exp6,32) && ok;
  ok = print_result(comp7,exp7,32) && ok;
#endif

  return ok;
}

int main()
{
  EverCrypt_AutoConfig2_init();

  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(sha2_test_vector); ++i) {
    ok &= print_test1(vectors[i].input,vectors[i].input_len,vectors[i].tag_256,vectors[i].tag_512);
  }


  ok &= print_test4(vectors_mb[0].input,vectors_mb[1].input,vectors_mb[2].input,vectors_mb[3].input,vectors_mb[0].input_len,
		    vectors_mb[0].tag_256,vectors_mb[1].tag_256,vectors_mb[2].tag_256,vectors_mb[3].tag_256);


  if (EverCrypt_AutoConfig2_has_avx2()) {
    ok &= print_test8(vectors_mb[0].input,vectors_mb[1].input,vectors_mb[2].input,vectors_mb[3].input,
		    vectors_mb[4].input,vectors_mb[5].input,vectors_mb[6].input,vectors_mb[7].input, vectors_mb[0].input_len,
		    vectors_mb[0].tag_256,vectors_mb[1].tag_256,vectors_mb[2].tag_256,vectors_mb[3].tag_256,
		    vectors_mb[4].tag_256,vectors_mb[5].tag_256,vectors_mb[6].tag_256,vectors_mb[7].tag_256);

    ok &= print_test4_512(vectors_mb[0].input,vectors_mb[1].input,vectors_mb[2].input,vectors_mb[3].input,vectors_mb[0].input_len,
			vectors_mb[0].tag_512,vectors_mb[1].tag_512,vectors_mb[2].tag_512,vectors_mb[3].tag_512);
  }

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


#if defined(HACL_CAN_COMPILE_VEC128)
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
#endif

  if (EverCrypt_AutoConfig2_has_avx2()) {
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
  }
  double cdiff2v8 = b - a;
  double tdiff2v8 = (double)(t2 - t1);


  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Scalar32_sha512(plain,SIZE,plain);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_SHA2_Scalar32_sha512(plain,SIZE,plain);
  }
  b = cpucycles_end();
  t2 = clock();
  double cdiff1 = b - a;
  double tdiff1 = (double)(t2 - t1);


  if (EverCrypt_AutoConfig2_has_avx2()) {
    for (int j = 0; j < ROUNDS; j++) {
      Hacl_SHA2_Vec256_sha512_4(plain,plain+64,plain+128,plain+192,SIZE,plain,plain,plain,plain);
    }

    t1 = clock();
    a = cpucycles_begin();
    for (int j = 0; j < ROUNDS; j++) {
      Hacl_SHA2_Vec256_sha512_4(plain,plain+64,plain+128,plain+192,SIZE,plain,plain,plain,plain);
    }
    b = cpucycles_end();
    t2 = clock();
  }
  double cdiff2 = b - a;
  double tdiff2 = (double)(t2 - t1);

  uint8_t res = plain[0];
  uint64_t count = ROUNDS * SIZE;
  printf ("\n\n");
  printf("NEW SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2n,cdiff2n);

#if defined(HACL_CAN_COMPILE_VEC128)
  printf("VEC4 SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2v,cdiff2v);
#endif

  if (EverCrypt_AutoConfig2_has_avx2()) {
    printf("VEC8 SHA2-256 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2v8,cdiff2v8);
  }
  printf ("\n\n");
  printf("NEW SHA2-512 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff1,cdiff1);

  if (EverCrypt_AutoConfig2_has_avx2()) {
    printf("VEC4 SHA2-512 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff2,cdiff2);
  }

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
