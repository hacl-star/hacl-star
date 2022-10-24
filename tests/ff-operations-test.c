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

#include "Hacl_Bignum_K256.h"
#include "Hacl_Bignum25519_51.h"

#include "test_helpers.h"

#define ROUNDS 209715200

int main() {
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS;

  uint64_t bignum_a[5U] = { 197876, 241305, 245979, 490424, 284994 };
  uint64_t bignum_b[5U] = { 180879, 475851, 123829, 108058, 144159 };

  // Benchmarking for Hacl_K256_Field_fmul
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fmul(bignum_b, bignum_a, bignum_b);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fmul(bignum_b, bignum_a, bignum_b);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

  // Benchmarking for Hacl_K256_Field_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fsqr(bignum_b, bignum_b);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_K256_Field_fsqr(bignum_b, bignum_b);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;

  printf("\n secp256k1_fmul:\n");
  print_time(count,diff1,cyc1);
  printf("\n secp256k1_fsqr:\n");
  print_time(count,diff2,cyc2);

  //  ---------------------------------------------------

  FStar_UInt128_uint128 tmp[10U];
  for (uint32_t _i = 0U; _i < (uint32_t)10U; ++_i)
    tmp[_i] = FStar_UInt128_uint64_to_uint128((uint64_t)0U);

 // Benchmarking for Hacl_Impl_Curve25519_Field51_fmul
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_Curve25519_Field51_fmul(bignum_b, bignum_a, bignum_b, tmp);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_Curve25519_Field51_fmul(bignum_b, bignum_a, bignum_b, tmp);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = t2 - t1;
  uint64_t cyc3 = b - a;

  // Benchmarking for Hacl_Impl_Curve25519_Field51_fsqr
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_Curve25519_Field51_fsqr(bignum_b, bignum_b, tmp);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_Curve25519_Field51_fsqr(bignum_b, bignum_b, tmp);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff4 = t2 - t1;
  uint64_t cyc4 = b - a;

  bool b1 = bignum_b[1] == 2 ? 0 : 1;
  printf("b1 = %d\n", b1);

  printf("\n ed25519_fmul:\n");
  print_time(count,diff3,cyc3);
  printf("\n ed25519_fsqr:\n");
  print_time(count,diff4,cyc4);

  return EXIT_SUCCESS;
}
