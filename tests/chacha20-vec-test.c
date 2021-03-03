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

#include "Hacl_Chacha20_Vec32.h"

#if defined(EVERCRYPT_CAN_COMPILE_128)
#include "Hacl_Chacha20_Vec128.h"
#endif

#if defined(EVERCRYPT_CAN_COMPILE_256)
#include "Hacl_Chacha20_Vec256.h"
#endif

#include "EverCrypt_AutoConfig2.h"

#include "chacha20_vectors.h"

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

#if defined(EVERCRYPT_CAN_COMPILE_128)
  Hacl_Chacha20_Vec128_chacha20_encrypt_128(in_len,comp,in,key,nonce,1);
  printf("Chacha20 (128-bit) Result:\n");
  ok = ok && print_result(in_len,comp,exp);
#endif

#if defined(EVERCRYPT_CAN_COMPILE_256)
  if (EverCrypt_AutoConfig2_has_avx2()) {
    Hacl_Chacha20_Vec256_chacha20_encrypt_256(in_len,comp,in,key,nonce,1);
    printf("Chacha20 (256-bit) Result:\n");
    ok = ok && print_result(in_len,comp,exp);
  }
#endif
  return ok;
}


int main() {
  EverCrypt_AutoConfig2_init();
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
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

#if defined(EVERCRYPT_CAN_COMPILE_128)
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
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;
#endif

#if defined(EVERCRYPT_CAN_COMPILE_256)
  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  if (EverCrypt_AutoConfig2_has_avx2()) {
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
  }
  double diff3 = t2 - t1;
  uint64_t cyc3 = b - a;
#endif

  uint64_t count = ROUNDS * SIZE;
  printf("32-bit Chacha20\n"); print_time(count,diff1,cyc1);

#if defined(EVERCRYPT_CAN_COMPILE_128)
  printf("128-bit Chacha20\n"); print_time(count,diff2,cyc2);
#endif

#if defined(EVERCRYPT_CAN_COMPILE_256)
  if (EverCrypt_AutoConfig2_has_avx2()) {
    printf("256-bit Chacha20\n"); print_time(count,diff3,cyc3);
  }
#endif

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
