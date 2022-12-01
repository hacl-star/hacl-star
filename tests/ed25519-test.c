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

#include "Hacl_Ed25519.h"

#include "test_helpers.h"

#define ROUNDS 32768

static uint8_t msg3[2U] = { (uint8_t)0xafU, (uint8_t)0x82U };

static uint8_t sk3[32U] = {
    (uint8_t)0xc5U, (uint8_t)0xaaU, (uint8_t)0x8dU, (uint8_t)0xf4U, (uint8_t)0x3fU, (uint8_t)0x9fU,
    (uint8_t)0x83U, (uint8_t)0x7bU, (uint8_t)0xedU, (uint8_t)0xb7U, (uint8_t)0x44U, (uint8_t)0x2fU,
    (uint8_t)0x31U, (uint8_t)0xdcU, (uint8_t)0xb7U, (uint8_t)0xb1U, (uint8_t)0x66U, (uint8_t)0xd3U,
    (uint8_t)0x85U, (uint8_t)0x35U, (uint8_t)0x07U, (uint8_t)0x6fU, (uint8_t)0x09U, (uint8_t)0x4bU,
    (uint8_t)0x85U, (uint8_t)0xceU, (uint8_t)0x3aU, (uint8_t)0x2eU, (uint8_t)0x0bU, (uint8_t)0x44U,
    (uint8_t)0x58U, (uint8_t)0xf7U };

static uint8_t pk3[32U] = {
    (uint8_t)0xfcU, (uint8_t)0x51U, (uint8_t)0xcdU, (uint8_t)0x8eU, (uint8_t)0x62U, (uint8_t)0x18U,
    (uint8_t)0xa1U, (uint8_t)0xa3U, (uint8_t)0x8dU, (uint8_t)0xa4U, (uint8_t)0x7eU, (uint8_t)0xd0U,
    (uint8_t)0x02U, (uint8_t)0x30U, (uint8_t)0xf0U, (uint8_t)0x58U, (uint8_t)0x08U, (uint8_t)0x16U,
    (uint8_t)0xedU, (uint8_t)0x13U, (uint8_t)0xbaU, (uint8_t)0x33U, (uint8_t)0x03U, (uint8_t)0xacU,
    (uint8_t)0x5dU, (uint8_t)0xebU, (uint8_t)0x91U, (uint8_t)0x15U, (uint8_t)0x48U, (uint8_t)0x90U,
    (uint8_t)0x80U, (uint8_t)0x25U };

static uint8_t sig3[64U] = {
    (uint8_t)0x62U, (uint8_t)0x91U, (uint8_t)0xd6U, (uint8_t)0x57U, (uint8_t)0xdeU, (uint8_t)0xecU,
    (uint8_t)0x24U, (uint8_t)0x02U, (uint8_t)0x48U, (uint8_t)0x27U, (uint8_t)0xe6U, (uint8_t)0x9cU,
    (uint8_t)0x3aU, (uint8_t)0xbeU, (uint8_t)0x01U, (uint8_t)0xa3U, (uint8_t)0x0cU, (uint8_t)0xe5U,
    (uint8_t)0x48U, (uint8_t)0xa2U, (uint8_t)0x84U, (uint8_t)0x74U, (uint8_t)0x3aU, (uint8_t)0x44U,
    (uint8_t)0x5eU, (uint8_t)0x36U, (uint8_t)0x80U, (uint8_t)0xd7U, (uint8_t)0xdbU, (uint8_t)0x5aU,
    (uint8_t)0xc3U, (uint8_t)0xacU, (uint8_t)0x18U, (uint8_t)0xffU, (uint8_t)0x9bU, (uint8_t)0x53U,
    (uint8_t)0x8dU, (uint8_t)0x16U, (uint8_t)0xf2U, (uint8_t)0x90U, (uint8_t)0xaeU, (uint8_t)0x67U,
    (uint8_t)0xf7U, (uint8_t)0x60U, (uint8_t)0x98U, (uint8_t)0x4dU, (uint8_t)0xc6U, (uint8_t)0x59U,
    (uint8_t)0x4aU, (uint8_t)0x7cU, (uint8_t)0x15U, (uint8_t)0xe9U, (uint8_t)0x71U, (uint8_t)0x6eU,
    (uint8_t)0xd2U, (uint8_t)0x8dU, (uint8_t)0xc0U, (uint8_t)0x27U, (uint8_t)0xbeU, (uint8_t)0xceU,
    (uint8_t)0xeaU, (uint8_t)0x1eU, (uint8_t)0xc4U, (uint8_t)0x0aU };


int main() {
  bool ok = true;
  uint8_t signature[64U] = { 0U };
  uint8_t signature1[64U] = { 0U };
  uint8_t expanded_keys[96U] = { 0U };

  Hacl_Ed25519_sign(signature, sk3, 2ul, msg3);
  ok &= compare(64U, signature, sig3);
  ok &= Hacl_Ed25519_verify(pk3, 2ul, msg3, sig3);

  Hacl_Ed25519_expand_keys(expanded_keys, sk3);
  Hacl_Ed25519_sign_expanded(signature1, expanded_keys, 2ul, msg3);
  ok &= compare(64U, signature1, sig3);

  if (ok)
    printf ("\n Success :) \n");
  else
    printf ("\n Failed :( \n");

  // Benchmarking for signing (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Ed25519_sign(signature, sk3, 2ul, msg3);
  }

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Ed25519_sign(signature, sk3, 2ul, msg3);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff1 = t2 - t1;
  uint64_t cyc1 = b - a;

  // Benchmarking for verifying (HACL)
  bool b1 = true;
  for (int j = 0; j < ROUNDS; j++) {
    b1 &= Hacl_Ed25519_verify(pk3, 2ul, msg3, sig3);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    b1 &= Hacl_Ed25519_verify(pk3, 2ul, msg3, sig3);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff2 = t2 - t1;
  uint64_t cyc2 = b - a;

  // Benchmarking for signing with expanded keys (HACL)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Ed25519_sign_expanded(signature1, expanded_keys, 2ul, msg3);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Ed25519_sign_expanded(signature1, expanded_keys, 2ul, msg3);
  }
  b = cpucycles_end();
  t2 = clock();
  double diff3 = t2 - t1;
  uint64_t cyc3 = b - a;

  uint64_t count = ROUNDS;
  printf("\n Ed25519 Signing:\n");
  print_time(count,diff1,cyc1);
  printf("\n Ed25519 Verifying:\n");
  print_time(count,diff2,cyc2);
  printf("\n Ed25519 Signing with expanded keys:\n");
  print_time(count,diff3,cyc3);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
