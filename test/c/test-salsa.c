#include "kremlib.h"
#include "testlib.h"
#include "Salsa20.h"
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
#define MACSIZE 32

__attribute__ ((aligned (16)))  uint8_t
  expected1[64] =
    {
      (uint8_t )0xE3,
      (uint8_t )0xBE,
      (uint8_t )0x8F,
      (uint8_t )0xDD,
      (uint8_t )0x8B,
      (uint8_t )0xEC,
      (uint8_t )0xA2,
      (uint8_t )0xE3,
      (uint8_t )0xEA,
      (uint8_t )0x8E,
      (uint8_t )0xF9,
      (uint8_t )0x47,
      (uint8_t )0x5B,
      (uint8_t )0x29,
      (uint8_t )0xA6,
      (uint8_t )0xE7,
      (uint8_t )0x00,
      (uint8_t )0x39,
      (uint8_t )0x51,
      (uint8_t )0xE1,
      (uint8_t )0x09,
      (uint8_t )0x7A,
      (uint8_t )0x5C,
      (uint8_t )0x38,
      (uint8_t )0xD2,
      (uint8_t )0x3B,
      (uint8_t )0x7A,
      (uint8_t )0x5F,
      (uint8_t )0xAD,
      (uint8_t )0x9F,
      (uint8_t )0x68,
      (uint8_t )0x44,
      (uint8_t )0xB2,
      (uint8_t )0x2C,
      (uint8_t )0x97,
      (uint8_t )0x55,
      (uint8_t )0x9E,
      (uint8_t )0x27,
      (uint8_t )0x23,
      (uint8_t )0xC7,
      (uint8_t )0xCB,
      (uint8_t )0xBD,
      (uint8_t )0x3F,
      (uint8_t )0xE4,
      (uint8_t )0xFC,
      (uint8_t )0x8D,
      (uint8_t )0x9A,
      (uint8_t )0x07,
      (uint8_t )0x44,
      (uint8_t )0x65,
      (uint8_t )0x2A,
      (uint8_t )0x83,
      (uint8_t )0xE7,
      (uint8_t )0x2A,
      (uint8_t )0x9C,
      (uint8_t )0x46,
      (uint8_t )0x18,
      (uint8_t )0x76,
      (uint8_t )0xAF,
      (uint8_t )0x4D,
      (uint8_t )0x7E,
      (uint8_t )0xF1,
      (uint8_t )0xA1,
      (uint8_t )0x17
    };
__attribute__ ((aligned (16)))  uint8_t
  expected2[64] =
    {
      (uint8_t )0x57,
      (uint8_t )0xBE,
      (uint8_t )0x81,
      (uint8_t )0xF4,
      (uint8_t )0x7B,
      (uint8_t )0x17,
      (uint8_t )0xD9,
      (uint8_t )0xAE,
      (uint8_t )0x7C,
      (uint8_t )0x4F,
      (uint8_t )0xF1,
      (uint8_t )0x54,
      (uint8_t )0x29,
      (uint8_t )0xA7,
      (uint8_t )0x3E,
      (uint8_t )0x10,
      (uint8_t )0xAC,
      (uint8_t )0xF2,
      (uint8_t )0x50,
      (uint8_t )0xED,
      (uint8_t )0x3A,
      (uint8_t )0x90,
      (uint8_t )0xA9,
      (uint8_t )0x3C,
      (uint8_t )0x71,
      (uint8_t )0x13,
      (uint8_t )0x08,
      (uint8_t )0xA7,
      (uint8_t )0x4C,
      (uint8_t )0x62,
      (uint8_t )0x16,
      (uint8_t )0xA9,
      (uint8_t )0xED,
      (uint8_t )0x84,
      (uint8_t )0xCD,
      (uint8_t )0x12,
      (uint8_t )0x6D,
      (uint8_t )0xA7,
      (uint8_t )0xF2,
      (uint8_t )0x8E,
      (uint8_t )0x8A,
      (uint8_t )0xBF,
      (uint8_t )0x8B,
      (uint8_t )0xB6,
      (uint8_t )0x35,
      (uint8_t )0x17,
      (uint8_t )0xE1,
      (uint8_t )0xCA,
      (uint8_t )0x98,
      (uint8_t )0xE7,
      (uint8_t )0x12,
      (uint8_t )0xF4,
      (uint8_t )0xFB,
      (uint8_t )0x2E,
      (uint8_t )0x1A,
      (uint8_t )0x6A,
      (uint8_t )0xED,
      (uint8_t )0x9F,
      (uint8_t )0xDC,
      (uint8_t )0x73,
      (uint8_t )0x29,
      (uint8_t )0x1F,
      (uint8_t )0xAA,
      (uint8_t )0x17
    };
__attribute__ ((aligned (16)))  uint8_t
  expected3[64] =
    {
      (uint8_t )0x95,
      (uint8_t )0x82,
      (uint8_t )0x11,
      (uint8_t )0xC4,
      (uint8_t )0xBA,
      (uint8_t )0x2E,
      (uint8_t )0xBD,
      (uint8_t )0x58,
      (uint8_t )0x38,
      (uint8_t )0xC6,
      (uint8_t )0x35,
      (uint8_t )0xED,
      (uint8_t )0xB8,
      (uint8_t )0x1F,
      (uint8_t )0x51,
      (uint8_t )0x3A,
      (uint8_t )0x91,
      (uint8_t )0xA2,
      (uint8_t )0x94,
      (uint8_t )0xE1,
      (uint8_t )0x94,
      (uint8_t )0xF1,
      (uint8_t )0xC0,
      (uint8_t )0x39,
      (uint8_t )0xAE,
      (uint8_t )0xEC,
      (uint8_t )0x65,
      (uint8_t )0x7D,
      (uint8_t )0xCE,
      (uint8_t )0x40,
      (uint8_t )0xAA,
      (uint8_t )0x7E,
      (uint8_t )0x7C,
      (uint8_t )0x0A,
      (uint8_t )0xF5,
      (uint8_t )0x7C,
      (uint8_t )0xAC,
      (uint8_t )0xEF,
      (uint8_t )0xA4,
      (uint8_t )0x0C,
      (uint8_t )0x9F,
      (uint8_t )0x14,
      (uint8_t )0xB7,
      (uint8_t )0x1A,
      (uint8_t )0x4B,
      (uint8_t )0x34,
      (uint8_t )0x56,
      (uint8_t )0xA6,
      (uint8_t )0x3E,
      (uint8_t )0x16,
      (uint8_t )0x2E,
      (uint8_t )0xC7,
      (uint8_t )0xD8,
      (uint8_t )0xD1,
      (uint8_t )0x0B,
      (uint8_t )0x8F,
      (uint8_t )0xFB,
      (uint8_t )0x18,
      (uint8_t )0x10,
      (uint8_t )0xD7,
      (uint8_t )0x10,
      (uint8_t )0x01,
      (uint8_t )0xB6,
      (uint8_t )0x18
    };
__attribute__ ((aligned (16)))  uint8_t
  expected4[64] =
    {
      (uint8_t )0x69,
      (uint8_t )0x6A,
      (uint8_t )0xFC,
      (uint8_t )0xFD,
      (uint8_t )0x0C,
      (uint8_t )0xDD,
      (uint8_t )0xCC,
      (uint8_t )0x83,
      (uint8_t )0xC7,
      (uint8_t )0xE7,
      (uint8_t )0x7F,
      (uint8_t )0x11,
      (uint8_t )0xA6,
      (uint8_t )0x49,
      (uint8_t )0xD7,
      (uint8_t )0x9A,
      (uint8_t )0xCD,
      (uint8_t )0xC3,
      (uint8_t )0x35,
      (uint8_t )0x4E,
      (uint8_t )0x96,
      (uint8_t )0x35,
      (uint8_t )0xFF,
      (uint8_t )0x13,
      (uint8_t )0x7E,
      (uint8_t )0x92,
      (uint8_t )0x99,
      (uint8_t )0x33,
      (uint8_t )0xA0,
      (uint8_t )0xBD,
      (uint8_t )0x6F,
      (uint8_t )0x53,
      (uint8_t )0x77,
      (uint8_t )0xEF,
      (uint8_t )0xA1,
      (uint8_t )0x05,
      (uint8_t )0xA3,
      (uint8_t )0xA4,
      (uint8_t )0x26,
      (uint8_t )0x6B,
      (uint8_t )0x7C,
      (uint8_t )0x0D,
      (uint8_t )0x08,
      (uint8_t )0x9D,
      (uint8_t )0x08,
      (uint8_t )0xF1,
      (uint8_t )0xE8,
      (uint8_t )0x55,
      (uint8_t )0xCC,
      (uint8_t )0x32,
      (uint8_t )0xB1,
      (uint8_t )0x5B,
      (uint8_t )0x93,
      (uint8_t )0x78,
      (uint8_t )0x4A,
      (uint8_t )0x36,
      (uint8_t )0xE5,
      (uint8_t )0x6A,
      (uint8_t )0x76,
      (uint8_t )0xCC,
      (uint8_t )0x64,
      (uint8_t )0xBC,
      (uint8_t )0x84,
      (uint8_t )0x77
    };


#define TEST_LEN 512
#define TEST_KEYSIZE 32
#define TEST_NONCESIZE 32

int32_t test_salsa()
{
  /* TR: we now allocate in the free store rather than on the stack,
     because of stack overflow on Windows. */
  uint8_t * ciphertext = hacl_aligned_malloc(16, TEST_LEN);
  if (ciphertext == NULL) {
    return exit_failure;
  }
  memset(ciphertext, 0, TEST_LEN * sizeof ciphertext[0]);
  uint8_t * plaintext = hacl_aligned_malloc(16, TEST_LEN);
  if (plaintext == NULL) {
    hacl_aligned_free(ciphertext);
    return exit_failure;
  }
  memset(plaintext, 0, TEST_LEN * sizeof plaintext[0]);
  uint8_t * key = hacl_aligned_malloc(16, TEST_KEYSIZE);
  if (key == NULL) {
    hacl_aligned_free(plaintext);
    hacl_aligned_free(ciphertext);
    return exit_failure;
  }
  memset(key, 0, TEST_KEYSIZE * sizeof key[0]);
  key[(uint32_t )0] = (uint8_t )0x80;
  uint8_t * nonce = hacl_aligned_malloc(16, TEST_NONCESIZE);
  if (nonce == NULL) {
    hacl_aligned_free(key);
    hacl_aligned_free(plaintext);
    hacl_aligned_free(ciphertext);
    return exit_failure;
  }
  memset(nonce, 0, TEST_NONCESIZE * sizeof nonce[0]);


  Salsa20_salsa20(ciphertext,
                  plaintext,
                  (uint64_t )512,
                  key,
                  nonce,
                  0);
  TestLib_compare_and_print("HACL Salsa20", expected1, ciphertext + (uint32_t )0, (uint32_t )64);
  TestLib_compare_and_print("HACL Salsa20", expected2, ciphertext + (uint32_t )192, (uint32_t )64);
  TestLib_compare_and_print("HACL Salsa20", expected3, ciphertext + (uint32_t )256, (uint32_t )64);
  TestLib_compare_and_print("HACL Salsa20", expected4, ciphertext + (uint32_t )448, (uint32_t )64);

  crypto_stream_salsa20_xor(ciphertext,plaintext, 512, nonce, key);
  TestLib_compare_and_print("Sodium Salsa20", expected1, ciphertext + (uint32_t )0, (uint32_t )64);
  TestLib_compare_and_print("Sodium Salsa20", expected2, ciphertext + (uint32_t )192, (uint32_t )64);
  TestLib_compare_and_print("Sodium Salsa20", expected3, ciphertext + (uint32_t )256, (uint32_t )64);
  TestLib_compare_and_print("Sodium Salsa20", expected4, ciphertext + (uint32_t )448, (uint32_t )64);

  hacl_aligned_free(nonce);
  hacl_aligned_free(key);
  hacl_aligned_free(plaintext);
  hacl_aligned_free(ciphertext);

  return exit_success;
}

#define LEN (PLAINLEN * sizeof(char))

int32_t perf_salsa() {
  /* TR: we now allocate in the free store rather than on the stack,
     because of stack overflow on Windows. */
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint64_t res = 0;
  uint8_t * plain = malloc(LEN);
  if (plain == NULL) {
    return exit_failure;
  }
  uint8_t * cipher = hacl_aligned_malloc(16, LEN);
  if (cipher == NULL) {
    free(plain);
    return exit_failure;
  }
  if (! (read_random_bytes(LEN, plain))) {
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }

  uint8_t * key = hacl_aligned_malloc(16, TEST_KEYSIZE);
  if (key == NULL) {
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(key, 0, TEST_KEYSIZE * sizeof key[0]);
  uint8_t * subkey = hacl_aligned_malloc(16, TEST_KEYSIZE);
  if (subkey == NULL) {
    hacl_aligned_free(key);
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(subkey, 0, TEST_KEYSIZE * sizeof subkey[0]);
  key[(uint32_t )0] = (uint8_t )0x80;
  uint8_t * nonce = hacl_aligned_malloc(16, TEST_NONCESIZE);
  if (nonce == NULL) {
    hacl_aligned_free(subkey);
    hacl_aligned_free(key);
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(nonce, 0, TEST_NONCESIZE * sizeof nonce[0]);
  uint8_t * block = hacl_aligned_malloc(16, 64);
  if (block == NULL) {
    hacl_aligned_free(nonce);
    hacl_aligned_free(subkey);
    hacl_aligned_free(key);
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(block, 0, 64 * sizeof block[0]);
  uint8_t * block_ = hacl_aligned_malloc(16, 64);
  if (block_ == NULL) {
    hacl_aligned_free(block);
    hacl_aligned_free(nonce);
    hacl_aligned_free(subkey);
    hacl_aligned_free(key);
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(block_, 0, 64 * sizeof block_[0]);
  uint8_t * nonce_ = hacl_aligned_malloc(16, TEST_NONCESIZE);
  if (nonce_ == NULL) {
    hacl_aligned_free(block_);
    hacl_aligned_free(block);
    hacl_aligned_free(nonce);
    hacl_aligned_free(subkey);
    hacl_aligned_free(key);
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(nonce_, 0, TEST_NONCESIZE * sizeof nonce_[0]);
  uint8_t * subkey_ = hacl_aligned_malloc(16, TEST_KEYSIZE);
  if (subkey_ == NULL) {
    hacl_aligned_free(nonce_);
    hacl_aligned_free(block_);
    hacl_aligned_free(block);
    hacl_aligned_free(nonce);
    hacl_aligned_free(subkey);
    hacl_aligned_free(key);
    hacl_aligned_free(cipher);
    free(plain);
    return exit_failure;
  }
  memset(subkey_, 0, TEST_KEYSIZE * sizeof subkey_[0]);

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();

  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    //memcpy(block+32,plain,32);
    //Hacl_Symmetric_HSalsa20_crypto_core_hsalsa20(subkey, nonce, key);
    //    memcpy(cipher,block+32,32);
    Salsa20_salsa20(cipher, plain, LEN, key, nonce, 0);
    //Poly1305_64_crypto_onetimeauth(subkey_, cipher, len, subkey);
    //Salsa20_crypto_stream_salsa20_xor_block0(block_, block, 64, nonce_, subkey);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL Salsa20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_stream_salsa20_xor(plain,plain, LEN, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium Salsa20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    tweet_crypto_stream_salsa20_xor(plain,plain, LEN, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  tweet_cy = (double)b - a;
  tweet_utime = (double)t2 - t1;
  print_results("TweetNacl Salsa20 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < PLAINLEN; i++)
    res += (uint64_t) plain[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("SALSA20", hacl_cy, sodium_cy, 0, tweet_cy, hacl_utime, sodium_utime, 0, tweet_utime, ROUNDS, PLAINLEN);

  hacl_aligned_free(subkey_);
  hacl_aligned_free(nonce_);
  hacl_aligned_free(block_);
  hacl_aligned_free(block);
  hacl_aligned_free(nonce);
  hacl_aligned_free(subkey);
  hacl_aligned_free(key);
  hacl_aligned_free(cipher);
  free(plain);

  return exit_success;
}

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    int32_t res = test_salsa();
    if (res == exit_success) {
      printf("Before perf\n");
      res = perf_salsa();
    }
    return res;
  } else if (argc == 2 && strcmp (argv[1], "unit-test") == 0 ) {
    return test_salsa();
  } else {
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return exit_failure;
  }
}
