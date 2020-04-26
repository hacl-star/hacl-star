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
#include "Hacl_Poly1305_256.h"

#include "test_helpers.h"
#include "poly1305_vectors.h"

#include "poly1305.h"

void ossl_poly1305(uint8_t* mac, uint8_t* plain, int len, uint8_t* key){
  POLY1305 state;
  Poly1305_Init(&state,key);
  Poly1305_Update(&state,plain,len);
  Poly1305_Final(&state,mac);
}

#include "impl.h"

extern void poly1305_impl(unsigned char *out, const unsigned char *in, unsigned long long inlen, const unsigned char *k);

/* BoringSSL - slow
#include "openssl/poly1305.h"
static inline void bssl_poly1305(uint8_t mac[16],const uint8_t* in, size_t in_len, const uint8_t key[32]) {
  poly1305_state st;
  CRYPTO_poly1305_init(&st,key);
  CRYPTO_poly1305_update(&st,in,in_len);
  CRYPTO_poly1305_finish(&st,mac);
}
*/


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

  Hacl_Poly1305_128_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (128-bit) Result:\n");
  ok = ok && print_result(comp, exp);

  Hacl_Poly1305_256_poly1305_mac(comp,in_len,in,key);
  printf("Poly1305 (256-bit) Result:\n");
  ok = ok && print_result(comp, exp);

  ossl_poly1305(comp,in,in_len,key);
  printf("OpenSSL Result:\n");
  ok = ok && print_result(comp, exp);

  poly1305_impl(comp,in,in_len,key);
  printf("Jasmin (avx2) Result:\n");
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
  cycles a,b;
  clock_t t1,t2;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(plain,SIZE,plain,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_128_poly1305_mac(plain,SIZE,plain,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_128_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_256_poly1305_mac(plain,SIZE,plain,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_256_poly1305_mac(tag,SIZE,plain,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff3 = t2 - t1;
  cycles cdiff3 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    ossl_poly1305(tag,plain,SIZE,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    ossl_poly1305(tag,plain,SIZE,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff4 = t2 - t1;
  cycles cdiff4 = b - a;


  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    poly1305_impl(tag,plain,SIZE,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    poly1305_impl(tag,plain,SIZE,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff5 = t2 - t1;
  cycles cdiff5 = b - a;

  uint64_t count = ROUNDS * SIZE;
  printf("Poly1305 (32-bit) PERF: %d\n",(int)res); print_time(count,tdiff1,cdiff1);
  printf("Poly1305 (128-bit) PERF:\n"); print_time(count,tdiff2,cdiff2);
  printf("Poly1305 (256-bit) PERF:\n"); print_time(count,tdiff3,cdiff3);
  printf("OpenSSL Poly1305 (vec) PERF:\n"); print_time(count,tdiff4,cdiff4);
  printf("Jasmin Poly1305 (avx2) PERF:\n"); print_time(count,tdiff5,cdiff5);

  if (ok) return EXIT_SUCCESS;
  else return EXIT_FAILURE;
}
