#include "kremlib.h"
#include "testlib.h"
#include "Hacl_Poly1305_64.h"
#include "sodium.h"
#include "internal/poly1305.h"
#include "poly1305_local.h"
#include "tweetnacl.h"
#include "hacl_test_utils.h"

#define PLAINLEN (16*1024)
#define ROUNDS 1000
#define MACSIZE 16

void ossl_poly1305(uint8_t* mac, uint8_t* plain, int len, uint8_t* key){
  POLY1305 state;
  Hacl_Poly1305_Init(&state,key);
  Hacl_Poly1305_Update(&state,plain,len);
  Hacl_Poly1305_Final(&state,mac);
}

void print_results(char *txt, double t1, uint64_t d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times 2^20 bytes: %" PRIu64 " (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times 2^20 bytes: %f (%fus/byte)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}


void flush_results(char *txt, uint64_t hacl_cy, uint64_t sodium_cy, uint64_t ossl_cy, uint64_t tweet_cy, double hacl_utime, double sodium_utime, double ossl_utime, double tweet_utime, int rounds, int plainlen){
  FILE *fp;
  char hacl_cy_s[24], sodium_cy_s[24], ossl_cy_s[24], tweet_cy_s[24], hacl_utime_s[24], sodium_utime_s[24], ossl_utime_s[24], tweet_utime_s[24];
  if (hacl_cy == 0) {
    sprintf(hacl_cy_s, "NA");
  } else {
    sprintf(hacl_cy_s, "%.2f", (double)hacl_cy/plainlen/rounds);
  }
  if (sodium_cy == 0) {
    sprintf(sodium_cy_s, "NA");
  } else {
    sprintf(sodium_cy_s, "%.2f", (double)sodium_cy/plainlen/rounds);
  }
  if (ossl_cy == 0) {
    sprintf(ossl_cy_s, "NA");
  } else {
    sprintf(ossl_cy_s, "%.2f", (double)ossl_cy/plainlen/rounds);
  }
  if (tweet_cy == 0) {
    sprintf(tweet_cy_s, "NA");
  } else {
    sprintf(tweet_cy_s, "%.2f", (double)tweet_cy/plainlen/rounds);
  }
  if (hacl_utime == 0) {
    sprintf(hacl_utime_s, "NA");
  } else {
    sprintf(hacl_utime_s, "%f", (double)(hacl_utime/CLOCKS_PER_SEC*1000000)/(plainlen*rounds));
  }
  if (sodium_utime == 0) {
    sprintf(sodium_utime_s, "NA");
  } else {
    sprintf(sodium_utime_s, "%f", (double)(sodium_utime/CLOCKS_PER_SEC*1000000)/(plainlen*rounds));
  }
  if (ossl_utime == 0) {
    sprintf(ossl_utime_s, "NA");
  } else {
    sprintf(ossl_utime_s, "%f", (double)(ossl_utime/CLOCKS_PER_SEC*1000000)/(plainlen*rounds));
  }
  if (tweet_utime == 0) {
    sprintf(tweet_utime_s, "NA");
  } else {
    sprintf(tweet_utime_s, "%f", (double)(tweet_utime/CLOCKS_PER_SEC*1000000)/(plainlen*rounds));
  }
  fp = fopen("./bench.txt", "a");
  fprintf(fp, "%-16s%-16s%-16s%-16s%-16s%-16s%-16s%-16s%-16s\n", txt, hacl_cy_s, sodium_cy_s, ossl_cy_s, tweet_cy_s, hacl_utime_s, sodium_utime_s, ossl_utime_s, tweet_utime_s);
  fclose(fp);
}

uint8_t
plaintext[34] =
    {
      (uint8_t )0x43,
      (uint8_t )0x72,
      (uint8_t )0x79,
      (uint8_t )0x70,
      (uint8_t )0x74,
      (uint8_t )0x6f,
      (uint8_t )0x67,
      (uint8_t )0x72,
      (uint8_t )0x61,
      (uint8_t )0x70,
      (uint8_t )0x68,
      (uint8_t )0x69,
      (uint8_t )0x63,
      (uint8_t )0x20,
      (uint8_t )0x46,
      (uint8_t )0x6f,
      (uint8_t )0x72,
      (uint8_t )0x75,
      (uint8_t )0x6d,
      (uint8_t )0x20,
      (uint8_t )0x52,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x65,
      (uint8_t )0x61,
      (uint8_t )0x72,
      (uint8_t )0x63,
      (uint8_t )0x68,
      (uint8_t )0x20,
      (uint8_t )0x47,
      (uint8_t )0x72,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x70
    };
uint8_t
expected[16] =
    {
      (uint8_t )0xa8,
      (uint8_t )0x06,
      (uint8_t )0x1d,
      (uint8_t )0xc1,
      (uint8_t )0x30,
      (uint8_t )0x51,
      (uint8_t )0x36,
      (uint8_t )0xc6,
      (uint8_t )0xc2,
      (uint8_t )0x2b,
      (uint8_t )0x8b,
      (uint8_t )0xaf,
      (uint8_t )0x0c,
      (uint8_t )0x01,
      (uint8_t )0x27,
      (uint8_t )0xa9
    };

uint8_t
key[32] =
    {
      (uint8_t )0x85,
      (uint8_t )0xd6,
      (uint8_t )0xbe,
      (uint8_t )0x78,
      (uint8_t )0x57,
      (uint8_t )0x55,
      (uint8_t )0x6d,
      (uint8_t )0x33,
      (uint8_t )0x7f,
      (uint8_t )0x44,
      (uint8_t )0x52,
      (uint8_t )0xfe,
      (uint8_t )0x42,
      (uint8_t )0xd5,
      (uint8_t )0x06,
      (uint8_t )0xa8,
      (uint8_t )0x01,
      (uint8_t )0x03,
      (uint8_t )0x80,
      (uint8_t )0x8a,
      (uint8_t )0xfb,
      (uint8_t )0x0d,
      (uint8_t )0xb2,
      (uint8_t )0xfd,
      (uint8_t )0x4a,
      (uint8_t )0xbf,
      (uint8_t )0xf6,
      (uint8_t )0xaf,
      (uint8_t )0x41,
      (uint8_t )0x49,
      (uint8_t )0xf5,
      (uint8_t )0x1b
    };

int32_t test_poly()
{
  uint64_t len_ = (uint64_t )34;
  uint8_t mac[MACSIZE];
  memset(mac, 0, MACSIZE * sizeof mac[0]);
  Hacl_Poly1305_64_crypto_onetimeauth(mac, plaintext, 34, key);
  TestLib_compare_and_print("HACL Poly1305", expected, mac, MACSIZE);
  Hacl_Poly1305_64_crypto_onetimeauth(mac, plaintext, len_, key);
  TestLib_compare_and_print("Sodium Poly1305", expected, mac, MACSIZE);
  return exit_success;
}

int32_t perf_poly() {
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint32_t len = PLAINLEN * sizeof(char);
  uint8_t* plain = malloc(len);
  uint64_t res = 0;
  if (! (read_random_bytes(len, plain)))
    return 1;
  uint8_t* macs = malloc(ROUNDS * MACSIZE * sizeof(char));

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    Hacl_Poly1305_64_crypto_onetimeauth(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_onetimeauth(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);


  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    tweet_crypto_onetimeauth(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  tweet_cy = (double)b - a;
  tweet_utime = (double)t2 - t1;
  print_results("TweetNacl Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);


  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    ossl_poly1305(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  ossl_cy = (double)b - a;
  ossl_utime = (double)t2 - t1;
  print_results("OpenSSL Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("POLY1305", hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime, ROUNDS, PLAINLEN);

  return exit_success;
}

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    int32_t res = test_poly();
    if (res == exit_success) {
      res = perf_poly();
    }
    return res;
  } else if (argc == 2 && strcmp (argv[1], "unit-test") == 0 ) {
    return test_poly();
  } else {
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return exit_failure;
  }
}
