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

#include "Hacl_Hash_Blake2b_256.h"

#include "test_helpers.h"

#include "EverCrypt_AutoConfig2.h"
#include "blake2_vectors.h"

#define ROUNDS 16384
#define SIZE   8196

bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}


bool print_test2b(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp){
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2b_256_blake2b(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2b vec-256:\n");
  bool ok = print_result(exp_len,comp,exp);
  return ok;
}


int main()
{
  EverCrypt_AutoConfig2_init();
  if (!EverCrypt_AutoConfig2_has_vec256()) {
      printf("The current hardware doesn't support vec256: aborting\n");
      return EXIT_SUCCESS;
  }
  else {
      printf("The current hardware supports vec256: performing the tests\n");
  }

  bool ok = true;
  for (int i = 0; i < sizeof(vectors2b)/sizeof(blake2_test_vector); ++i) {
    ok &= print_test2b(vectors2b[i].input_len,vectors2b[i].input,vectors2b[i].key_len,vectors2b[i].key,vectors2b[i].expected_len,vectors2b[i].expected);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_256_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_256_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();

  uint64_t cdiff1 = b - a;
  double tdiff1 = t2 - t1;

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2B (Vec 256-bit):\n"); print_time(count,tdiff1,cdiff1);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
