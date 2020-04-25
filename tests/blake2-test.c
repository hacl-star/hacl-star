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
#include "Hacl_Blake2s_128.h"
#include "Hacl_Blake2b_256.h"

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

  Hacl_Blake2b_256_blake2b(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2b vec-256:\n");
  ok = ok && print_result(exp_len,comp,exp);
  return ok;
}


bool print_test2s(int in_len, uint8_t* in, int key_len, uint8_t* key, int exp_len, uint8_t* exp){
  uint8_t comp[exp_len];
  memset(comp, 0, exp_len * sizeof comp[0]);

  Hacl_Blake2s_32_blake2s(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2s vec-32:\n");
  bool ok = print_result(exp_len,comp,exp);

  Hacl_Blake2s_128_blake2s(exp_len,comp,in_len,in,key_len,key);
  printf("testing blake2s vec-128:\n");
  ok = ok && print_result(exp_len,comp,exp);
  return ok;
}


int main()
{
  int in_len = vectors2b[0].input_len;
  uint8_t *in = vectors2b[0].input;
  int key_len = vectors2b[0].key_len;
  uint8_t *key = vectors2b[0].key;
  int exp_len = vectors2b[0].expected_len;
  uint8_t *exp = vectors2b[0].expected;

  int in_len1 = vectors2b[1].input_len;
  uint8_t *in1 = vectors2b[1].input;
  int key_len1 = vectors2b[1].key_len;
  uint8_t *key1 = vectors2b[1].key;
  int exp_len1 = vectors2b[1].expected_len;
  uint8_t *exp1 = vectors2b[1].expected;

  bool ok = print_test2b(in_len,in,key_len,key,exp_len,exp);
  ok = print_test2b(in_len1,in1,key_len1,key1,exp_len1,exp1) && ok;

  int in_len2 = vectors2s[0].input_len;
  uint8_t *in2 = vectors2s[0].input;
  int key_len2 = vectors2s[0].key_len;
  uint8_t *key2 = vectors2s[0].key;
  int exp_len2 = vectors2s[0].expected_len;
  uint8_t *exp2 = vectors2s[0].expected;

  int in_len3 = vectors2s[1].input_len;
  uint8_t *in3 = vectors2s[1].input;
  int key_len3 = vectors2s[1].key_len;
  uint8_t *key3 = vectors2s[1].key;
  int exp_len3 = vectors2s[1].expected_len;
  uint8_t *exp3 = vectors2s[1].expected;

  int in_len4 = vectors2s[2].input_len;
  uint8_t *in4 = vectors2s[2].input;
  int key_len4 = vectors2s[2].key_len;
  uint8_t *key4 = vectors2s[2].key;
  int exp_len4 = vectors2s[2].expected_len;
  uint8_t *exp4 = vectors2s[2].expected;

  int in_len5 = vectors2s[3].input_len;
  uint8_t *in5 = vectors2s[3].input;
  int key_len5 = vectors2s[3].key_len;
  uint8_t *key5 = vectors2s[3].key;
  int exp_len5 = vectors2s[3].expected_len;
  uint8_t *exp5 = vectors2s[3].expected;

  ok = print_test2s(in_len2,in2,key_len2,key2,exp_len2,exp2) && ok;
  ok = print_test2s(in_len3,in3,key_len3,key3,exp_len3,exp3) && ok;
  ok = print_test2s(in_len4,in4,key_len4,key4,exp_len4,exp4) && ok;
  ok = print_test2s(in_len5,in5,key_len5,key5,exp_len5,exp5) && ok;


  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  cycles a,b;
  clock_t t1,t2;
  memset(plain,'P',SIZE);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2s_32_blake2s(32,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff1 = b - a;
  double tdiff1 = t2 - t1;


  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Blake2b_32_blake2b(64,plain,SIZE,plain,0,NULL);
  }
  b = cpucycles_end();
  t2 = clock();
  uint64_t cdiff2 = b - a;
  double tdiff2 = t2 - t1;


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
  uint64_t cdiff3 = b - a;
  double tdiff3 = t2 - t1;


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
  uint64_t cdiff4 = b - a;
  double tdiff4 = t2 - t1;

  uint64_t count = ROUNDS * SIZE;
  printf("Blake2S (Vec 32-bit):\n"); print_time(count,tdiff1,cdiff1);
  printf("Blake2B (Vec 64-bit):\n"); print_time(count,tdiff2,cdiff2);
  printf("Blake2S (Vec 128-bit):\n"); print_time(count,tdiff3,cdiff3);
  printf("Blake2B (Vec 256-bit):\n"); print_time(count,tdiff4,cdiff4);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
