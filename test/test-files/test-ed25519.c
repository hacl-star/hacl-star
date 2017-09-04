#include "kremlib.h"
#include "testlib.h"
#include "Ed25519.h"
#include "sodium.h"
#include "tweetnacl.h"
#include "hacl_test_utils.h"

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

#define PLAINLEN (1024*1024)
#define ROUNDS 1000
#define SIGSIZE 64

  uint8_t
  sk11[32] =
    {
      (uint8_t )0x9d, (uint8_t )0x61, (uint8_t )0xb1, (uint8_t )0x9d, (uint8_t )0xef, (uint8_t )0xfd,
      (uint8_t )0x5a, (uint8_t )0x60, (uint8_t )0xba, (uint8_t )0x84, (uint8_t )0x4a, (uint8_t )0xf4,
      (uint8_t )0x92, (uint8_t )0xec, (uint8_t )0x2c, (uint8_t )0xc4, (uint8_t )0x44, (uint8_t )0x49,
      (uint8_t )0xc5, (uint8_t )0x69, (uint8_t )0x7b, (uint8_t )0x32, (uint8_t )0x69, (uint8_t )0x19,
      (uint8_t )0x70, (uint8_t )0x3b, (uint8_t )0xac, (uint8_t )0x03, (uint8_t )0x1c, (uint8_t )0xae,
      (uint8_t )0x7f, (uint8_t )0x60
    };
  uint8_t
  pk11[32] =
    {
      (uint8_t )0xd7, (uint8_t )0x5a, (uint8_t )0x98, (uint8_t )0x01, (uint8_t )0x82, (uint8_t )0xb1,
      (uint8_t )0x0a, (uint8_t )0xb7, (uint8_t )0xd5, (uint8_t )0x4b, (uint8_t )0xfe, (uint8_t )0xd3,
      (uint8_t )0xc9, (uint8_t )0x64, (uint8_t )0x07, (uint8_t )0x3a, (uint8_t )0x0e, (uint8_t )0xe1,
      (uint8_t )0x72, (uint8_t )0xf3, (uint8_t )0xda, (uint8_t )0xa6, (uint8_t )0x23, (uint8_t )0x25,
      (uint8_t )0xaf, (uint8_t )0x02, (uint8_t )0x1a, (uint8_t )0x68, (uint8_t )0xf7, (uint8_t )0x07,
      (uint8_t )0x51, (uint8_t )0x1a
    };
  uint8_t msg11[0];
  uint8_t
  sig11[64] =
    {
      (uint8_t )0xe5, (uint8_t )0x56, (uint8_t )0x43, (uint8_t )0x00, (uint8_t )0xc3, (uint8_t )0x60,
      (uint8_t )0xac, (uint8_t )0x72, (uint8_t )0x90, (uint8_t )0x86, (uint8_t )0xe2, (uint8_t )0xcc,
      (uint8_t )0x80, (uint8_t )0x6e, (uint8_t )0x82, (uint8_t )0x8a, (uint8_t )0x84, (uint8_t )0x87,
      (uint8_t )0x7f, (uint8_t )0x1e, (uint8_t )0xb8, (uint8_t )0xe5, (uint8_t )0xd9, (uint8_t )0x74,
      (uint8_t )0xd8, (uint8_t )0x73, (uint8_t )0xe0, (uint8_t )0x65, (uint8_t )0x22, (uint8_t )0x49,
      (uint8_t )0x01, (uint8_t )0x55, (uint8_t )0x5f, (uint8_t )0xb8, (uint8_t )0x82, (uint8_t )0x15,
      (uint8_t )0x90, (uint8_t )0xa3, (uint8_t )0x3b, (uint8_t )0xac, (uint8_t )0xc6, (uint8_t )0x1e,
      (uint8_t )0x39, (uint8_t )0x70, (uint8_t )0x1c, (uint8_t )0xf9, (uint8_t )0xb4, (uint8_t )0x6b,
      (uint8_t )0xd2, (uint8_t )0x5b, (uint8_t )0xf5, (uint8_t )0xf0, (uint8_t )0x59, (uint8_t )0x5b,
      (uint8_t )0xbe, (uint8_t )0x24, (uint8_t )0x65, (uint8_t )0x51, (uint8_t )0x41, (uint8_t )0x43,
      (uint8_t )0x8e, (uint8_t )0x7a, (uint8_t )0x10, (uint8_t )0x0b
    };

int32_t test_ed25519()
{
  uint8_t sig[SIGSIZE];
  memset(sig, 0, SIGSIZE * sizeof sig[0]);
  bool res = Ed25519_verify(pk11, msg11, (uint32_t )0, sig11);
  int32_t ret1;
  if (res)
  {
    Ed25519_sign(sig, sk11, msg11, (uint32_t )0);
    TestLib_compare_and_print("Ed25519 sig1", sig11, sig, (uint32_t )64);
    ret1 = exit_success;
  }
  else {
    printf("Verification failed\n");
    ret1 = exit_failure;
  }
  return ret1;
}

int32_t perf_ed25519() {
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint32_t len = PLAINLEN * sizeof(char);
  uint64_t res = 0;
  uint8_t* plain = malloc(len);
  if (! (read_random_bytes(len, plain)))
    return 1;
  uint8_t* macs = malloc(ROUNDS * SIGSIZE * sizeof(char));

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    Ed25519_sign(macs + SIGSIZE * i, sk11, plain, len);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL Ed25519 sign speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+SIGSIZE*i) + (uint64_t)*(macs+SIGSIZE*i+8)
				     + (uint64_t)*(macs+SIGSIZE*i+16) + (uint64_t)*(macs+SIGSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_sign_detached(macs + SIGSIZE * i, NULL, plain, len, sk11);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium Ed25519 sign speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+SIGSIZE*i) + (uint64_t)*(macs+SIGSIZE*i+8)
				     + (uint64_t)*(macs+SIGSIZE*i+16) + (uint64_t)*(macs+SIGSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("ED25519 SIGN", hacl_cy, sodium_cy, 0, 0, hacl_utime, sodium_utime, 0, 0, ROUNDS, PLAINLEN);
  
  bool bools[ROUNDS];
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    bools[i] = Ed25519_verify(pk11, plain, len, macs + SIGSIZE * i);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL Ed25519 verify speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)bools[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    bools[i] = crypto_sign_verify_detached(macs + SIGSIZE * i, plain, len, pk11);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium Ed25519 verify speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);

  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)bools[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("ED25519 VERIFY", hacl_cy, sodium_cy, 0, 0, hacl_utime, sodium_utime, 0, 0, ROUNDS, PLAINLEN);

  return exit_success;
}
  
int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    int32_t res = test_ed25519();
    if (res == exit_success) {
      res = perf_ed25519();
    }
    return res;
  } else if (argc == 2 && strcmp (argv[1], "unit-test") == 0 ) {
    return test_ed25519();
  } else {    
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return exit_failure;
  }
}
