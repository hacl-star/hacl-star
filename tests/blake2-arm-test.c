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

#include "Hacl_Blake2s_32.h"
#include "Hacl_Blake2b_32.h"

#if defined(EVERCRYPT_CAN_COMPILE_128)
#include "Hacl_Blake2s_128.h"
#endif

#include "test_helpers.h"
#include "blake2_vectors.h"

#define ROUNDS 16384
#define SIZE   8196

bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}


bool print_test2b(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp){
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2b_32_blake2b(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2b vec-32:\n");
  bool ok = print_result(exp_len,comp,exp);

  return ok;
}


bool print_test2s(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp){
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2s_32_blake2s(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2s vec-32:\n");
  bool ok = print_result(exp_len,comp,exp);

#if defined(EVERCRYPT_CAN_COMPILE_128)
  Hacl_Blake2s_128_blake2s(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2s vec-128:\n");
  ok = ok && print_result(exp_len,comp,exp);
#endif

  return ok;
}


int main()
{

  bool ok = true;
  for (int i = 0; i < sizeof(vectors2b)/sizeof(blake2_test_vector); ++i) {
    ok &= print_test2b(vectors2b[i].input_len,vectors2b[i].input,vectors2b[i].key_len,vectors2b[i].key,vectors2b[i].expected_len,vectors2b[i].expected);
  }

  for (int i = 0; i < sizeof(vectors2s)/sizeof(blake2_test_vector); ++i) {
    ok &= print_test2s(vectors2s[i].input_len,vectors2s[i].input,vectors2s[i].key_len,vectors2s[i].key,vectors2s[i].expected_len,vectors2s[i].expected);
  }


  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t2 = clock();
  clock_t tdiff1 = (t2 - t1);


  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  t2 = clock();
  clock_t tdiff2 = (t2 - t1);

#if defined(EVERCRYPT_CAN_COMPILE_128)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_128_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_128_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t2 = clock();
  clock_t tdiff3 = (t2 - t1);
#endif

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2S (Vec 32-bit):\n"); print_time(count,tdiff1,0);
  printf("Blake2B (Vec 64-bit):\n"); print_time(count,tdiff2,0);

#if defined(EVERCRYPT_CAN_COMPILE_128)
  printf("Blake2S (Vec 128-bit):\n"); print_time(count,tdiff3,0);
#endif

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
