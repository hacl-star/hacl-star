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

#if defined(EVERCRYPT_CAN_COMPILE_VEC128)
#include "Hacl_Poly1305_128.h"
#endif

#include "test_helpers.h"
#include "poly1305_vectors.h"

#define ROUNDS 100000
#define SIZE   16384


bool print_result(uint8_t* comp, uint8_t* exp) {
  return compare_and_print(16, comp, exp);
}

bool print_test(int in_len, uint8_t* in, uint8_t* key, uint8_t* exp){
  uint8_t comp[16] = {0};

  Hacl_Poly1305_32_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (32-bit) Result:\n");
  bool ok = print_result(comp, exp);

#if defined(EVERCRYPT_CAN_COMPILE_VEC128)
  Hacl_Poly1305_128_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (128-bit) Result:\n");
  ok = ok && print_result(comp, exp);
#endif

  return ok;
}

int main() {
  bool ok = true;
  for (int i = 0; i < sizeof(vectors)/sizeof(poly1305_test_vector); ++i) {
    ok &= print_test(vectors[i].input_len,vectors[i].input,vectors[i].key,vectors[i].tag);
  }

  uint8_t plain[SIZE];
  uint8_t key[32];
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

#if defined(EVERCRYPT_CAN_COMPILE_VEC128)
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
#endif

  uint64_t count = ROUNDS * SIZE;
  printf("Poly1305 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff1,0);

#if defined(EVERCRYPT_CAN_COMPILE_VEC128)
  printf("Poly1305 (128-bit) PERF:\n"); print_time(count,tdiff2,0);
#endif

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
