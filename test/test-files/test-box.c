#include "kremlib.h"
#include "testlib.h"
#include "NaCl.h"
#include "sodium.h"
#include "tweetnacl.h"
#include "hacl_test_utils.h"

#define MESSAGE_LEN 72
#define secretbox_MACBYTES   16
#define CIPHERTEXT_LEN       MESSAGE_LEN
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24

uint8_t msg[104] = {
  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  0x00, 0x01, 0x02, 0x03,  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,  0x20, 0x21, 0x22, 0x23,
  0x00, 0x01, 0x02, 0x03,  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,  0x20, 0x21, 0x22, 0x23,
  0x00, 0x01, 0x02, 0x03,  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,  0x20, 0x21, 0x22, 0x23,
};

uint8_t nonce[secretbox_NONCEBYTES] = {
  0x00, 0x01, 0x02, 0x03,
  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,
  0x20, 0x21, 0x22, 0x23,
};

uint8_t key[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};


uint8_t sk1[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};
uint8_t sk2[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

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

int32_t test_api()
{
  uint8_t ciphertext[CIPHERTEXT_LEN+32], mac[16], decrypted[MESSAGE_LEN+32],
          test1[box_PUBLICKEYBYTES], test2[box_PUBLICKEYBYTES],
          pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES],
          basepoint[box_PUBLICKEYBYTES] = {9};
  uint32_t res;
  int i;

  // Creating public/private key couples
  Hacl_Curve25519_crypto_scalarmult(pk1, sk1, basepoint);
  Hacl_Curve25519_crypto_scalarmult(pk2, sk2, basepoint);

  NaCl_crypto_box_beforenm(test1, pk1, sk2);
  res = crypto_box_beforenm(test2, pk2, sk1);
  TestLib_compare_and_print("HACL beforenm", test1, test2, 32);

  /* Testing the box primitives */
  i = NaCl_crypto_box_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = crypto_box_open_detached(decrypted, ciphertext+32, mac, MESSAGE_LEN, nonce, pk2, sk1);
  printf("Libsodium decryption of HACL box was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg+32, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  i = crypto_box_detached(ciphertext+32, mac, msg+32, MESSAGE_LEN, nonce, pk1, sk2);
  res = NaCl_crypto_box_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, pk2, sk1);
  printf("HACL decryption of Libsodium box was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg+32, decrypted+32, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  i = NaCl_crypto_box_easy(ciphertext, msg, MESSAGE_LEN, nonce, pk1, sk2);
  res = crypto_box_open_easy(decrypted, ciphertext+16, MESSAGE_LEN+16, nonce, pk2, sk1);
  printf("Libsodium decryption of HACL box_easy was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg+32, decrypted, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  i = crypto_box_easy(ciphertext+16, msg+32, MESSAGE_LEN, nonce, pk1, sk2);
  res = NaCl_crypto_box_open_easy(decrypted, ciphertext, MESSAGE_LEN, nonce, pk2, sk1);
  printf("Box decryption of libsodium box easy was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Box", msg+32, decrypted+32, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  return exit_success;
}

int32_t perf_api() {
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint32_t len = 1024*1024 * sizeof(char);
  uint64_t res = 0;
  uint8_t* plaintext = malloc(len+16*sizeof(char));
  uint8_t* ciphertext = malloc(len+16*sizeof(char));
  if (! (read_random_bytes(len, plaintext)))
    return 1;

  uint8_t mac[16],mac2[16], pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES];

  cycles a,b;
  clock_t t1,t2;

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    NaCl_crypto_box_easy(plaintext, plaintext, len, nonce, sk1, sk2);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("Hacl Box speed", (double)t2-t1,
		(double) b - a, ROUNDS, 1024 * 1024);
  for (int i = 0; i < CIPHERTEXT_LEN; i++)
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    int res = crypto_box_easy(plaintext, plaintext, len, nonce, sk1, sk2);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium Box speed", (double)t2-t1,
		(double) b - a, ROUNDS, 1024 * 1024);
  for (int i = 0; i < len + 16 * sizeof(char); i++)
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    int res = tweet_crypto_box(plaintext, plaintext, len, nonce, sk1, sk2);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  tweet_cy = (double)b - a;
  tweet_utime = (double)t2 - t1;
  print_results("TweetNacl Box speed", (double)t2-t1,
		(double) b - a, ROUNDS, 1024 * 1024);
  for (int i = 0; i < len + 16 * sizeof(char); i++)
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  flush_results("BOX", hacl_cy, sodium_cy, 0, tweet_cy, hacl_utime, sodium_utime, 0, tweet_utime, ROUNDS, PLAINLEN);

  return exit_success;
}

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    if (sodium_init() == -1) {
      printf("libsodium not installed? sodium_init failed\n");
      exit(EXIT_FAILURE);
    }
    int32_t res = test_api();
    if (res == exit_success) {
      res = perf_api();
    }
    return res;
  } else if (argc == 2 && strcmp (argv[1], "unit-test") == 0 ) {
    return test_api();
  } else {
    printf("Error: expected arguments 'perf' (default) or 'unit-test'.\n");
    return exit_failure;
  }
}
