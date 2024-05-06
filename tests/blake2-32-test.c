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

#include "Hacl_Hash_Blake2b.h"
#include "Hacl_Hash_Blake2s.h"

#if defined(HACL_CAN_COMPILE_VEC128)
#include "Hacl_Hash_Blake2s_Simd128.h"
#endif

#include "test_helpers.h"

#include "EverCrypt_AutoConfig2.h"
#include "blake2_vectors.h"

#define ROUNDS 16384
#define SIZE 8196

bool
print_result(int in_len, uint8_t* comp, uint8_t* exp)
{
  return compare_and_print(in_len, comp, exp);
}

bool
print_test2b(int in_len,
             uint8_t* in,
             int key_len,
             uint8_t* key,
             int exp_len,
             uint8_t* exp)
{
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Hash_Blake2b_hash_with_key(comp, exp_len, in, in_len, key, key_len);
  printf("testing blake2b vec-32:\n");
  bool ok = print_result(exp_len, comp, exp);
  return ok;
}

bool
print_test2s(int in_len,
             uint8_t* in,
             int key_len,
             uint8_t* key,
             int exp_len,
             uint8_t* exp)
{
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Hash_Blake2s_hash_with_key(comp, exp_len, in, in_len, key, key_len);
  printf("testing blake2s vec-32:\n");
  bool ok = print_result(exp_len, comp, exp);

#if defined(HACL_CAN_COMPILE_VEC128)
  Hacl_Hash_Blake2s_Simd128_hash_with_key(comp, exp_len, in, in_len, key, key_len);
  printf("testing blake2s vec-128:\n");
  ok = ok && print_result(exp_len, comp, exp);
#endif

  return ok;
}

int
main()
{
  EverCrypt_AutoConfig2_init();
  bool ok = true;
  for (size_t i = 0; i < sizeof(vectors2s) / sizeof(blake2_test_vector); ++i) {
    ok &= print_test2s(vectors2s[i].input_len,
                       vectors2s[i].input,
                       vectors2s[i].key_len,
                       vectors2s[i].key,
                       vectors2s[i].expected_len,
                       vectors2s[i].expected);
  }
  for (size_t i = 0; i < sizeof(vectors2b) / sizeof(blake2_test_vector); ++i) {
    ok &= print_test2b(vectors2b[i].input_len,
                       vectors2b[i].input,
                       vectors2b[i].key_len,
                       vectors2b[i].key,
                       vectors2b[i].expected_len,
                       vectors2b[i].expected);
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a, b;
  clock_t t1, t2;
  memset(plain, 'P', SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_Blake2s_hash_with_key(plain, 32 ,plain, SIZE, NULL, 0);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_Blake2s_hash_with_key(plain, 32, plain, SIZE, NULL, 0);
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_Blake2b_hash_with_key(plain, 64, plain, SIZE, NULL, 0);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_Blake2b_hash_with_key(plain, 64, plain, SIZE, NULL, 0);
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = (t2 - t1);

#if defined(HACL_CAN_COMPILE_VEC128)
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_Blake2s_Simd128_hash_with_key(plain, 32, plain, SIZE, NULL, 0);
  }
  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Hash_Blake2s_Simd128_hash_with_key(plain, 32, plain, SIZE, NULL, 0);
  }
  t2 = clock();
  clock_t tdiff3 = (t2 - t1);
#endif

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2S (Vec 32-bit):\n");
  print_time(count, tdiff1, 0);
  printf("Blake2B (Vec 64-bit):\n");
  print_time(count, tdiff2, 0);

#if defined(HACL_CAN_COMPILE_VEC128)
  printf("Blake2S (Vec 128-bit):\n");
  print_time(count, tdiff3, 0);
#endif

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
