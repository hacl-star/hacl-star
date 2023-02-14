#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include "Hacl_Chacha20.h"

#include "chacha20_vectors.h"
#include "test_helpers.h"

#define ROUNDS 16384
#define SIZE 81920

bool
print_result(int in_len, uint8_t* comp, uint8_t* exp)
{
  return compare_and_print(in_len, comp, exp);
}

bool
print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* nonce, uint8_t* exp)
{
  uint8_t comp[in_len];
  memset(comp, 0, in_len);

  Hacl_Chacha20_chacha20_encrypt(in_len, comp, in, key, nonce, 1);
  bool ok = print_result(in_len, comp, exp);

  return ok;
}

int
main()
{
  bool ok = true;
  for (int i = 0; i < sizeof(vectors) / sizeof(chacha20_test_vector); ++i) {
    ok &= print_test(vectors[i].input_len,
                     vectors[i].input,
                     vectors[i].key,
                     vectors[i].nonce,
                     vectors[i].cipher);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint8_t key[16];
  uint8_t nonce[12];
  memset(plain, 'P', SIZE);
  memset(key, 'K', 16);
  memset(nonce, 'N', 12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_chacha20_encrypt(SIZE, plain, plain, key, nonce, 1);
  }

  cycles a, b;
  clock_t t1, t2;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Chacha20_chacha20_encrypt(SIZE, plain, plain, key, nonce, 1);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

  uint64_t count = ROUNDS * SIZE;
  print_time(count, diff1, cyc1);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
