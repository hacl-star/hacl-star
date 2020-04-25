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

void print_time(clock_t tdiff, uint64_t cdiff){
  uint64_t count = ROUNDS * SIZE;
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff,(double)tdiff/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff / CLOCKS_PER_SEC) * 1000000.0));
}

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
  uint8_t *scalar0 = vectors[0].scalar;
  uint8_t *pub0 = vectors[0].public;
  uint8_t *exp0 = vectors[0].secret;

  uint8_t *scalar1 = vectors[1].scalar;
  uint8_t *pub1 = vectors[1].public;
  uint8_t *exp1 = vectors[1].secret;

  bool ok = print_test(scalar0,pub0,exp0);
  ok = print_test(scalar1,pub1,exp1) && ok;

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

  double time = (((double)tdiff1) / CLOCKS_PER_SEC);
  double nsigs = ((double)ROUNDS) / time;
  printf("Curve25519 (51-bit) PERF:\n"); print_time(tdiff1,0);
  printf("smult %8.2f mul/s\n",nsigs);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
