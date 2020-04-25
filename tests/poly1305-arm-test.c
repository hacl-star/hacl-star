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

#include "Hacl_Poly1305_32.h"
#include "Hacl_Poly1305_128.h"

#include "test_helpers.h"
#include "poly1305_vectors.h"

#define ROUNDS 100000
#define SIZE   16384

void print_time(clock_t tdiff, int cdiff){
  uint64_t count = ROUNDS * SIZE;
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff,(double)tdiff/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff / CLOCKS_PER_SEC) * 1000000.0));
}

bool print_result(uint8_t* comp, uint8_t* exp) {
  return compare_and_print(16, comp, exp);
}

bool print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* exp){
  uint8_t comp[16] = {0};

  Hacl_Poly1305_32_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (32-bit) Result:\n");
  bool ok = print_result(comp, exp);

  Hacl_Poly1305_128_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (128-bit) Result:\n");
  ok = ok && print_result(comp, exp);

  ok = ok && print_result(comp, exp);
  return ok;
}

int main() {
  int in_len = vectors[0].input_len;
  uint8_t *in = vectors[0].input;
  uint8_t *key = vectors[0].key;
  uint8_t *exp = vectors[0].tag;

  int in_len2 = vectors[1].input_len;
  uint8_t *in2 = vectors[1].input;
  uint8_t *key2 = vectors[1].key;
  uint8_t *exp2 = vectors[1].tag;

  int in_len3 = vectors[2].input_len;
  uint8_t *in3 = vectors[2].input;
  uint8_t *key3 = vectors[2].key;
  uint8_t *exp3 = vectors[2].tag;

  bool ok = print_test(in_len,in,key,exp);
  ok = print_test(in_len2,in2,key2,exp2) && ok;
  ok = print_test(in_len3,in3,key3,exp3) && ok;

  uint8_t plain[SIZE];
  uint64_t res = 0;
  uint8_t tag[16];
  clock_t t1,t2;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(plain,SIZE,plain,key);
  }

  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  t2 = clock();
  clock_t tdiff1 = t2 - t1;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_128_poly1305_mac(plain,SIZE,plain,key);
  }

  t1 = clock();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_128_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  t2 = clock();
  clock_t tdiff2 = t2 - t1;

  printf("Poly1305 (32-bit) PERF: %d\n",(int)res); print_time(tdiff1,0);
  printf("Poly1305 (128-bit) PERF:\n"); print_time(tdiff2,0);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
