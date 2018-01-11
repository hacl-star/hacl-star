#include "kremlib.h"
#include "testlib.h"
#include "hacl_test_utils.h"

#if defined(__COMPCERT__)

int32_t test_chacha()
{
  printf("\nWARNING:Skipping the Chacha20 vectorized unit tests as it is not supported by CompCert\n");
  return exit_success;
}

int32_t perf_chacha() {
  printf("\nWARNING:\nSkipping the Chacha20 vectorized performace tests as it is not supported by CompCert\n");
  return exit_success;
}

#else

#include "Hacl_Chacha20_Vec128.h"
#include "sodium.h"
#include "openssl/evp.h"

void ossl_chacha20(uint8_t* cipher, uint8_t* plain, int len, uint8_t* nonce, uint8_t* key){
  EVP_CIPHER_CTX *ctx;
  int clen;
  ctx = EVP_CIPHER_CTX_new();
  EVP_EncryptInit_ex(ctx, EVP_chacha20(), NULL, key, nonce);
  EVP_EncryptUpdate(ctx, cipher, &clen, plain, len);
  EVP_EncryptFinal_ex(ctx, cipher + clen, &clen);
  EVP_CIPHER_CTX_free(ctx);
}


void print_results(char *txt, double t1, uint64_t d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d * %d bytes: %" PRIu64 " (%.2fcycles/byte)\n", rounds, plainlen, d1, (double)d1/plainlen/rounds);
  double ts = t1/CLOCKS_PER_SEC;
  printf("User time for %d times %d bytes: %fs (%fus/byte)\n", rounds, plainlen, ts, (double)(ts*1000000)/(plainlen*rounds));
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
#define MACSIZE 32


uint8_t
plaintext[114] =
    {
      (uint8_t )0x4c,
      (uint8_t )0x61,
      (uint8_t )0x64,
      (uint8_t )0x69,
      (uint8_t )0x65,
      (uint8_t )0x73,
      (uint8_t )0x20,
      (uint8_t )0x61,
      (uint8_t )0x6e,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x47,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x74,
      (uint8_t )0x6c,
      (uint8_t )0x65,
      (uint8_t )0x6d,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x68,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x63,
      (uint8_t )0x6c,
      (uint8_t )0x61,
      (uint8_t )0x73,
      (uint8_t )0x73,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x27,
      (uint8_t )0x39,
      (uint8_t )0x39,
      (uint8_t )0x3a,
      (uint8_t )0x20,
      (uint8_t )0x49,
      (uint8_t )0x66,
      (uint8_t )0x20,
      (uint8_t )0x49,
      (uint8_t )0x20,
      (uint8_t )0x63,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x6c,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x66,
      (uint8_t )0x66,
      (uint8_t )0x65,
      (uint8_t )0x72,
      (uint8_t )0x20,
      (uint8_t )0x79,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x6e,
      (uint8_t )0x6c,
      (uint8_t )0x79,
      (uint8_t )0x20,
      (uint8_t )0x6f,
      (uint8_t )0x6e,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x69,
      (uint8_t )0x70,
      (uint8_t )0x20,
      (uint8_t )0x66,
      (uint8_t )0x6f,
      (uint8_t )0x72,
      (uint8_t )0x20,
      (uint8_t )0x74,
      (uint8_t )0x68,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x66,
      (uint8_t )0x75,
      (uint8_t )0x74,
      (uint8_t )0x75,
      (uint8_t )0x72,
      (uint8_t )0x65,
      (uint8_t )0x2c,
      (uint8_t )0x20,
      (uint8_t )0x73,
      (uint8_t )0x75,
      (uint8_t )0x6e,
      (uint8_t )0x73,
      (uint8_t )0x63,
      (uint8_t )0x72,
      (uint8_t )0x65,
      (uint8_t )0x65,
      (uint8_t )0x6e,
      (uint8_t )0x20,
      (uint8_t )0x77,
      (uint8_t )0x6f,
      (uint8_t )0x75,
      (uint8_t )0x6c,
      (uint8_t )0x64,
      (uint8_t )0x20,
      (uint8_t )0x62,
      (uint8_t )0x65,
      (uint8_t )0x20,
      (uint8_t )0x69,
      (uint8_t )0x74,
      (uint8_t )0x2e
    };
uint8_t
expected[114] =
    {
      (uint8_t )0x6e,
      (uint8_t )0x2e,
      (uint8_t )0x35,
      (uint8_t )0x9a,
      (uint8_t )0x25,
      (uint8_t )0x68,
      (uint8_t )0xf9,
      (uint8_t )0x80,
      (uint8_t )0x41,
      (uint8_t )0xba,
      (uint8_t )0x07,
      (uint8_t )0x28,
      (uint8_t )0xdd,
      (uint8_t )0x0d,
      (uint8_t )0x69,
      (uint8_t )0x81,
      (uint8_t )0xe9,
      (uint8_t )0x7e,
      (uint8_t )0x7a,
      (uint8_t )0xec,
      (uint8_t )0x1d,
      (uint8_t )0x43,
      (uint8_t )0x60,
      (uint8_t )0xc2,
      (uint8_t )0x0a,
      (uint8_t )0x27,
      (uint8_t )0xaf,
      (uint8_t )0xcc,
      (uint8_t )0xfd,
      (uint8_t )0x9f,
      (uint8_t )0xae,
      (uint8_t )0x0b,
      (uint8_t )0xf9,
      (uint8_t )0x1b,
      (uint8_t )0x65,
      (uint8_t )0xc5,
      (uint8_t )0x52,
      (uint8_t )0x47,
      (uint8_t )0x33,
      (uint8_t )0xab,
      (uint8_t )0x8f,
      (uint8_t )0x59,
      (uint8_t )0x3d,
      (uint8_t )0xab,
      (uint8_t )0xcd,
      (uint8_t )0x62,
      (uint8_t )0xb3,
      (uint8_t )0x57,
      (uint8_t )0x16,
      (uint8_t )0x39,
      (uint8_t )0xd6,
      (uint8_t )0x24,
      (uint8_t )0xe6,
      (uint8_t )0x51,
      (uint8_t )0x52,
      (uint8_t )0xab,
      (uint8_t )0x8f,
      (uint8_t )0x53,
      (uint8_t )0x0c,
      (uint8_t )0x35,
      (uint8_t )0x9f,
      (uint8_t )0x08,
      (uint8_t )0x61,
      (uint8_t )0xd8,
      (uint8_t )0x07,
      (uint8_t )0xca,
      (uint8_t )0x0d,
      (uint8_t )0xbf,
      (uint8_t )0x50,
      (uint8_t )0x0d,
      (uint8_t )0x6a,
      (uint8_t )0x61,
      (uint8_t )0x56,
      (uint8_t )0xa3,
      (uint8_t )0x8e,
      (uint8_t )0x08,
      (uint8_t )0x8a,
      (uint8_t )0x22,
      (uint8_t )0xb6,
      (uint8_t )0x5e,
      (uint8_t )0x52,
      (uint8_t )0xbc,
      (uint8_t )0x51,
      (uint8_t )0x4d,
      (uint8_t )0x16,
      (uint8_t )0xcc,
      (uint8_t )0xf8,
      (uint8_t )0x06,
      (uint8_t )0x81,
      (uint8_t )0x8c,
      (uint8_t )0xe9,
      (uint8_t )0x1a,
      (uint8_t )0xb7,
      (uint8_t )0x79,
      (uint8_t )0x37,
      (uint8_t )0x36,
      (uint8_t )0x5a,
      (uint8_t )0xf9,
      (uint8_t )0x0b,
      (uint8_t )0xbf,
      (uint8_t )0x74,
      (uint8_t )0xa3,
      (uint8_t )0x5b,
      (uint8_t )0xe6,
      (uint8_t )0xb4,
      (uint8_t )0x0b,
      (uint8_t )0x8e,
      (uint8_t )0xed,
      (uint8_t )0xf2,
      (uint8_t )0x78,
      (uint8_t )0x5e,
      (uint8_t )0x42,
      (uint8_t )0x87,
      (uint8_t )0x4d
    };
uint8_t
key[32] =
    {
      (uint8_t )0,
      (uint8_t )1,
      (uint8_t )2,
      (uint8_t )3,
      (uint8_t )4,
      (uint8_t )5,
      (uint8_t )6,
      (uint8_t )7,
      (uint8_t )8,
      (uint8_t )9,
      (uint8_t )10,
      (uint8_t )11,
      (uint8_t )12,
      (uint8_t )13,
      (uint8_t )14,
      (uint8_t )15,
      (uint8_t )16,
      (uint8_t )17,
      (uint8_t )18,
      (uint8_t )19,
      (uint8_t )20,
      (uint8_t )21,
      (uint8_t )22,
      (uint8_t )23,
      (uint8_t )24,
      (uint8_t )25,
      (uint8_t )26,
      (uint8_t )27,
      (uint8_t )28,
      (uint8_t )29,
      (uint8_t )30,
      (uint8_t )31
    };
uint8_t
nonce[12] =
    {
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0x4a,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0,
      (uint8_t )0
    };

int32_t test_chacha()
{
  uint32_t len = (uint32_t )114;
  uint8_t ciphertext[len];
  memset(ciphertext, 0, len * sizeof ciphertext[0]);
  uint32_t counter = (uint32_t )1;
  uint32_t ctx[32] = { 0 };
  Hacl_Chacha20_Vec128_chacha20(ciphertext,plaintext,len, key, nonce, counter);
  TestLib_compare_and_print("HACL Chacha20", expected, ciphertext, len);

  crypto_stream_chacha20_ietf_xor_ic(ciphertext,plaintext, len, nonce, 1, key);
  TestLib_compare_and_print("Sodium Chacha20", expected, ciphertext, len);

  return exit_success;
}

int32_t perf_chacha() {
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint32_t len = PLAINLEN * sizeof(char);
  uint8_t* plain = malloc(len);
  uint8_t* cipher = malloc(len);
  uint64_t res = 0;
  if (! (read_random_bytes(len, plain)))
    return 1;

  uint32_t counter = (uint32_t )1;
  uint32_t ctx[32] = { 0 };

  cycles a,b;
  clock_t t1,t2;

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    Hacl_Chacha20_Vec128_chacha20(plain,plain,len, key, nonce, counter);
    plain[0] = cipher[0];
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL ChaCha20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_stream_chacha20_ietf_xor(plain,plain, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium ChaCha20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    ossl_chacha20(plain,plain, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  ossl_cy = (double)b - a;
  ossl_utime = (double)t2 - t1;
  print_results("OpenSSL ChaCha20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("CHACHA20VEC128", hacl_cy, sodium_cy, 0, tweet_cy, hacl_utime, sodium_utime, 0, tweet_utime, ROUNDS, PLAINLEN);

  return exit_success;
}

#endif

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    int32_t res = test_chacha();
    if (res == exit_success) {
      res = perf_chacha();
    }
    return res;
    } else if (argc == 2 && strcmp(argv[1], "unit-test") == 0 ) {
    return test_chacha();
  } else {
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return exit_failure;
  }
}
