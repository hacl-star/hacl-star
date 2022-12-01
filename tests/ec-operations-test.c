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

#include "Hacl_EC_K256.h"
#include "Hacl_EC_Ed25519.h"

#include "test_helpers.h"

#define ROUNDS 2097152

int main() {
  uint64_t secp256k1_bp_proj[15U] = { 0U };
  Hacl_EC_K256_mk_base_point(secp256k1_bp_proj);
  uint64_t secp256k1_add_proj[15U] = { 0U };
  Hacl_EC_K256_mk_base_point(secp256k1_add_proj);

  // Benchmarking for secp256k1_point_add (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_K256_point_add(secp256k1_add_proj, secp256k1_bp_proj, secp256k1_add_proj);
  }

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_K256_point_add(secp256k1_add_proj, secp256k1_bp_proj, secp256k1_add_proj);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

  // Benchmarking for secp256k1_point_double (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_K256_point_double(secp256k1_add_proj, secp256k1_add_proj);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_K256_point_double(secp256k1_add_proj, secp256k1_add_proj);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;

  bool b2 = secp256k1_add_proj[1] == 2 ? 0 : 1;
  printf("b2 = %d\n", b2);

  uint64_t count = ROUNDS;
  printf("\n secp256k1_point_add:\n");
  print_time(count,diff1,cyc1);
  printf("\n secp256k1_point_double:\n");
  print_time(count,diff2,cyc2);

  //---------------------------------

  uint64_t secp256k1_sm_proj[15U] = { 0U };
  uint64_t scalar1[4U] = { 197876, 241305, 245979, 490424 };
  uint64_t scalar2[4U] = { 197337, 246730, 685978, 440564 };
  // Benchmarking for Hacl_EC_K256_point_mul_g_double_vartime
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_K256_point_mul_g_double_vartime(secp256k1_sm_proj, scalar1, scalar2, secp256k1_add_proj);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_K256_point_mul_g_double_vartime(secp256k1_sm_proj, scalar1, scalar2, secp256k1_add_proj);
  }
  b = cpucycles_end();
  t2 = clock();
  double diffsm = t2 - t1;
  uint64_t cycsm = b - a;

  printf("\n secp256k1_point_mul_g_double:\n");
  print_time(count,diffsm,cycsm);

  //---------------------------------

  uint64_t ed25519_bp_proj[20U] = { 0U };
  Hacl_EC_Ed25519_mk_base_point(ed25519_bp_proj);
  uint64_t ed25519_add_proj[20U] = { 0U };
  Hacl_EC_Ed25519_mk_base_point(ed25519_add_proj);

  // Benchmarking for ed25519_point_add (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_Ed25519_point_add(ed25519_add_proj, ed25519_bp_proj, ed25519_add_proj);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_Ed25519_point_add(ed25519_add_proj, ed25519_bp_proj, ed25519_add_proj);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = t2 - t1;
  uint64_t cyc3 = b - a;

  // Benchmarking for ed25519_point_double (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_Ed25519_point_double(ed25519_add_proj, ed25519_add_proj);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_EC_Ed25519_point_double(ed25519_add_proj, ed25519_add_proj);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff4 = t2 - t1;
  uint64_t cyc4 = b - a;

  bool b1 = ed25519_add_proj[1] == 2 ? 0 : 1;
  printf("b1 = %d\n", b1);

  printf("\n ed25519_point_add:\n");
  print_time(count,diff3,cyc3);
  printf("\n ed25519_point_double:\n");
  print_time(count,diff4,cyc4);

  return EXIT_SUCCESS;
}
