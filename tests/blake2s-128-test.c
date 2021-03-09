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

#include "Hacl_Blake2s_128.h"

#include "test_helpers.h"

#include "EverCrypt_AutoConfig2.h"
#include "blake2_vectors.h"

#define ROUNDS 16384
#define SIZE   8196

bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

bool print_test2s(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp){
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2s_128_blake2s(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2s vec-128:\n");
  bool ok = print_result(exp_len,comp,exp);

  return ok;
}

int main()
{
  EverCrypt_AutoConfig2_init();
  bool ok = true;
  for (int i = 0; i < sizeof(vectors2s)/sizeof(blake2_test_vector); ++i) {
    ok &= print_test2s(vectors2s[i].input_len,vectors2s[i].input,vectors2s[i].key_len,vectors2s[i].key,vectors2s[i].expected_len,vectors2s[i].expected);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_128_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_128_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff1 = b - a;
  double tdiff1 = t2 - t1;

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2S (Vec 128-bit):\n"); print_time(count,tdiff1,cdiff1);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
