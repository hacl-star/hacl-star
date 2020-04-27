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

#include "Hacl_Curve25519_51.h"

#include "test_helpers.h"
#include "curve25519_vectors.h"

#define ROUNDS 100000
#define SIZE   1


bool print_result(int in_len, uint8_t* comp, uint8_t* exp) {
  return compare_and_print(in_len, comp, exp);
}

bool print_test(uint8_t* scalar, uint8_t* pub, uint8_t* exp){
  uint8_t comp[32] = {0};

  Hacl_Curve25519_51_ecdh(comp,scalar,pub);
  printf("Curve25519 (51-bit) Result:\n");
  bool ok = print_result(32,comp,exp);
  return ok;
}


int main() {
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(curve25519_test_vector); ++i) {
    ok &= print_test(vectors[i].scalar,vectors[i].public,vectors[i].secret);
  }

  uint8_t pub[32];
  uint8_t priv[32];
  uint8_t key[32];
  uint64_t res = 0;
  clock_t t1,t2;

  memset(pub,'P',32);
  memset(priv,'S',32);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Curve25519_51_ecdh(pub,priv,pub);
  }

  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Curve25519_51_ecdh(key,priv,pub);
    res ^= key[0] ^ key[15];
  }
  t2 = clock();
  clock_t tdiff1 = t2 - t1;

  uint64_t count = ROUNDS * SIZE;
  double time = (((double)tdiff1) / CLOCKS_PER_SEC);
  double nsigs = ((double)ROUNDS) / time;
  printf("Curve25519 (51-bit) PERF:\n"); print_time(count,tdiff1,0);
  printf("smult %8.2f mul/s\n",nsigs);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
