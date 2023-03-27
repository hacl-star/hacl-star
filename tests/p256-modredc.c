#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

#include "Hacl_P256_ModReduction.h"

#include "test_helpers.h"

#define ROUNDS 20971520

/*

void Hacl_P256_ModReduction_mul_mod_solinas(uint64_t *x, uint64_t *y, uint64_t *res);

void Hacl_P256_ModReduction_mul_mod_mont(uint64_t *x, uint64_t *y, uint64_t *res);
*/

int main() {
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS;

  uint64_t bignum_a[4U] = { 197876, 241305, 245979, 490424 };
  uint64_t bignum_b[4U] = { 180879, 475851, 123829, 108058 };

  // Benchmarking for Hacl_P256_ModReduction_mul_mod_solinas
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ModReduction_mul_mod_solinas(bignum_b, bignum_a, bignum_b);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ModReduction_mul_mod_solinas(bignum_b, bignum_a, bignum_b);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;


  // Benchmarking for Hacl_P256_ModReduction_mul_mod_mont
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ModReduction_mul_mod_mont(bignum_b, bignum_a, bignum_b);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_P256_ModReduction_mul_mod_mont(bignum_b, bignum_a, bignum_b);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;

  printf("\n mod_mul_solinas:\n");
  print_time(count,diff1,cyc1);
  printf("\n mod_mul_montgomery:\n");
  print_time(count,diff2,cyc2);

  return EXIT_SUCCESS;
}
