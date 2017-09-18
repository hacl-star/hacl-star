#include "kremlib.h"
#include "testlib.h"
#include "HMAC_SHA2_256.h"
#include "sodium.h"
#include "tweetnacl.h"
#include <openssl/evp.h>
#include <openssl/hmac.h>
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

#define PLAINLEN (16*1024)
#define ROUNDS 1000
#define SIGSIZE 64

int32_t test_hmac_sha256()
{
  return exit_success;
}

int32_t perf_hmac_sha256() {
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint32_t len = PLAINLEN * sizeof(char);
  uint32_t key_len = 64 * sizeof(char);
  uint8_t* plain = malloc(len);
  uint8_t* key = malloc(key_len);
  if (! (read_random_bytes(len, plain)))
    return 1;
  if (! (read_random_bytes(key_len, key))
    return 1;
  uint8_t* macs = malloc(ROUNDS * SIGSIZE * sizeof(char));

  cycles a,b;
  clock_t t1,t2;

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_auth_hmacsha512(macs + SIGSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium SHA256 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+SIGSIZE*i) + (uint64_t)*(macs+SIGSIZE*i+8)
				     + (uint64_t)*(macs+SIGSIZE*i+16) + (uint64_t)*(macs+SIGSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  /*   t1 = clock(); */
  /* a = TestLib_cpucycles_begin(); */
  /* for (int i = 0; i < ROUNDS; i++){ */
  /*   tweet_crypto_hash_sha256_tweet(macs + SIGSIZE * i, plain, len); */
  /* } */
  /* b = TestLib_cpucycles_end(); */
  /* t2 = clock(); */
  /* tweet_cy = (double)b - a; */
  /* tweet_utime = (double)t2 - t1; */
  /* print_results("TweetNaCl SHA256 speed", (double)t2-t1, */
  /*  	(double) b - a, ROUNDS, PLAINLEN); */
  /* for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+SIGSIZE*i) + (uint64_t)*(macs+SIGSIZE*i+8) */
  /*  			     + (uint64_t)*(macs+SIGSIZE*i+16) + (uint64_t)*(macs+SIGSIZE*i+24); */
  /* printf("Composite result (ignore): %" PRIx64 "\n", res); */

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    HMAC_SHA2_256_hmac_core(macs + SIGSIZE * i, key, plain, len);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL SHA256 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+SIGSIZE*i) + (uint64_t)*(macs+SIGSIZE*i+8)
				     + (uint64_t)*(macs+SIGSIZE*i+16) + (uint64_t)*(macs+SIGSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  unsigned int *resultlen = 0;
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    HMAC(EVP_sha256(), key, key_len, plain, len, macs + SIGSIZE * i, resultlen);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  ossl_cy = (double)b - a;
  ossl_utime = (double)t2 - t1;
  print_results("OpenSSL SHA256 speed", (double)t2-t1,
        	(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+SIGSIZE*i) + (uint64_t)*(macs+SIGSIZE*i+8)
        			     + (uint64_t)*(macs+SIGSIZE*i+16) + (uint64_t)*(macs+SIGSIZE*i+24);
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("SHA256", hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime, ROUNDS, PLAINLEN);

  return exit_success;
}

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    int32_t res = test_hmac_sha256();
    if (res == exit_success) {
      res = perf_hmac_sha256();
    }
    return res;
  } else if (argc == 2 && strcmp (argv[1], "unit-test") == 0 ) {
    return test_hmac_sha256();
  } else {
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return exit_failure;
  }
}
