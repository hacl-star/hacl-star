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

#include "EverCrypt_AutoConfig2.h"
#include "curve25519_vectors.h"
#include "test_helpers.h"

typedef __attribute__((aligned(32))) uint8_t X25519_KEY[32];

extern void
x25519_shared_secret_x64(uint8_t* sec, uint8_t* priv, uint8_t* pub);

#define ROUNDS 100000
#define SIZE 1

bool
print_result(int in_len, uint8_t* comp, uint8_t* exp)
{
  return compare_and_print(in_len, comp, exp);
}

bool
print_test(uint8_t* scalar, uint8_t* pub, uint8_t* exp)
{
  uint8_t comp[32] = { 0 };

  x25519_shared_secret_x64(comp, pub, scalar);
  printf("Curve25519 (RFC7794 Original 64-bit) Result:\n");
  bool ok = print_result(32, comp, exp);
  return ok;
}

int
main()
{
  EverCrypt_AutoConfig2_init();

  if (!(EverCrypt_AutoConfig2_has_adx() && EverCrypt_AutoConfig2_has_bmi2()))
    return EXIT_SUCCESS;

  bool ok = true;
  for (int i = 0; i < sizeof(vectors) / sizeof(curve25519_test_vector); ++i) {
    ok &= print_test(vectors[i].scalar, vectors[i].public, vectors[i].secret);
  }

  X25519_KEY pub, priv, key;
  uint64_t res = 0;
  cycles a, b;
  clock_t t1, t2;

  memset(pub, 'P', 32);
  memset(priv, 'S', 32);
  for (int j = 0; j < ROUNDS; j++) {
    x25519_shared_secret_x64(pub, priv, pub);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    x25519_shared_secret_x64(key, priv, pub);
    res ^= key[0] ^ key[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  uint64_t count = ROUNDS * SIZE;
  double time = (((double)tdiff1) / CLOCKS_PER_SEC);
  double nsigs = ((double)ROUNDS) / time;
  printf("Curve25519 (RFC7748 Original) PERF:\n");
  print_time(count, tdiff1, cdiff1);
  printf("smult %8.2f mul/s\n", nsigs);

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
