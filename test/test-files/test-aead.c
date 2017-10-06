#include "kremlib.h"
#include "testlib.h"
#include "Chacha20Poly1305.h"
#include "sodium.h"
#include "openssl/evp.h"
#include "hacl_test_utils.h"

void ossl_chacha20poly1305(uint8_t* cipher, uint8_t* mac, uint8_t* plain, int len, uint8_t* aad, int aad_len, uint8_t* nonce, uint8_t* key){
  EVP_CIPHER_CTX *ctx;
  int clen,alen;
  ctx = EVP_CIPHER_CTX_new();
  EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, NULL, NULL);
  EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, 16, NULL);
  EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, key, nonce);
  EVP_EncryptUpdate(ctx, NULL, &alen, aad, aad_len);
  EVP_EncryptUpdate(ctx, cipher, &clen, plain, len);
  EVP_EncryptFinal_ex(ctx, cipher + clen, &clen);
  EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, mac);
  EVP_CIPHER_CTX_free(ctx);
}


#define MESSAGE_LEN 114
#define CIPHERTEXT_LEN 114
#define MACLEN   16
#define NONCELEN 12
#define KEYLEN   32

uint8_t plaintext[114] = {
    	0x4c, 0x61, 0x64, 0x69, 0x65, 0x73, 0x20, 0x61,
    	0x6e, 0x64, 0x20, 0x47, 0x65, 0x6e, 0x74, 0x6c,
    	0x65, 0x6d, 0x65, 0x6e, 0x20, 0x6f, 0x66, 0x20,
    	0x74, 0x68, 0x65, 0x20, 0x63, 0x6c, 0x61, 0x73,
    	0x73, 0x20, 0x6f, 0x66, 0x20, 0x27, 0x39, 0x39,
    	0x3a, 0x20, 0x49, 0x66, 0x20, 0x49, 0x20, 0x63,
   	0x6f, 0x75, 0x6c, 0x64, 0x20, 0x6f, 0x66, 0x66,
    	0x65, 0x72, 0x20, 0x79, 0x6f, 0x75, 0x20, 0x6f,
    	0x6e, 0x6c, 0x79, 0x20, 0x6f, 0x6e, 0x65, 0x20,
    	0x74, 0x69, 0x70, 0x20, 0x66, 0x6f, 0x72, 0x20,
    	0x74, 0x68, 0x65, 0x20, 0x66, 0x75, 0x74, 0x75,
    	0x72, 0x65, 0x2c, 0x20, 0x73, 0x75, 0x6e, 0x73,
    	0x63, 0x72, 0x65, 0x65, 0x6e, 0x20, 0x77, 0x6f,
    	0x75, 0x6c, 0x64, 0x20, 0x62, 0x65, 0x20, 0x69,
    	0x74, 0x2e
};

uint8_t nonce[12] = {0x07,0x00,0x00,0x00,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47};

uint8_t key[32] = {
    	0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
	0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f
};

uint8_t aad[12] = {
        0x50,0x51,0x52,0x53,0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7
};

uint8_t xciphertext[114] = {
        0xd3,0x1a,0x8d,0x34,0x64,0x8e,0x60,0xdb,0x7b,0x86,0xaf,0xbc,0x53,0xef,0x7e,0xc2,
	0xa4,0xad,0xed,0x51,0x29,0x6e,0x08,0xfe,0xa9,0xe2,0xb5,0xa7,0x36,0xee,0x62,0xd6,
	0x3d,0xbe,0xa4,0x5e,0x8c,0xa9,0x67,0x12,0x82,0xfa,0xfb,0x69,0xda,0x92,0x72,0x8b,
	0x1a,0x71,0xde,0x0a,0x9e,0x06,0x0b,0x29,0x05,0xd6,0xa5,0xb6,0x7e,0xcd,0x3b,0x36,
	0x92,0xdd,0xbd,0x7f,0x2d,0x77,0x8b,0x8c,0x98,0x03,0xae,0xe3,0x28,0x09,0x1b,0x58,
	0xfa,0xb3,0x24,0xe4,0xfa,0xd6,0x75,0x94,0x55,0x85,0x80,0x8b,0x48,0x31,0xd7,0xbc,
	0x3f,0xf4,0xde,0xf0,0x8e,0x4b,0x7a,0x9d,0xe5,0x76,0xd2,0x65,0x86,0xce,0xc6,0x4b,
	0x61,0x16
};

uint8_t xmac[16] = {
        0x1a,0xe1,0x0b,0x59,0x4f,0x09,0xe2,0x6a,0x7e,0x90,0x2e,0xcb,0xd0,0x60,0x06,0x91

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
  uint8_t ciphertext[CIPHERTEXT_LEN],
          mac[MACLEN], decrypted[MESSAGE_LEN];
  uint32_t res;
  int i;
  Chacha20Poly1305_aead_encrypt(ciphertext, mac, plaintext, MESSAGE_LEN, aad, 12, key, nonce);
  TestLib_compare_and_print("HACL aead cipher", xciphertext, ciphertext, MESSAGE_LEN);
  TestLib_compare_and_print("HACL aead mac", xmac, mac, MACLEN);

  long long unsigned maclen;
  res = crypto_aead_chacha20poly1305_ietf_encrypt_detached(ciphertext, mac, &maclen, plaintext, MESSAGE_LEN, aad, 12, NULL, nonce, key);
  TestLib_compare_and_print("Sodium aead cipher", xciphertext, ciphertext, MESSAGE_LEN);
  TestLib_compare_and_print("Sodium aead mac", xmac, mac, MACLEN);


  ossl_chacha20poly1305(ciphertext, mac, plaintext, MESSAGE_LEN, aad, 12, nonce, key);
  TestLib_compare_and_print("OpenSSL aead cipher", xciphertext, ciphertext, MESSAGE_LEN);
  TestLib_compare_and_print("OpenSSL aead mac", xmac, mac, MACLEN);
  return exit_success;
}


int32_t perf_api() {
  double hacl_cy, sodium_cy, ossl_cy, tweet_cy, hacl_utime, sodium_utime, ossl_utime, tweet_utime;
  uint8_t mac[16] = {0};
  uint32_t len = 1024*1024 * sizeof(char);
  uint64_t res = 0;
  uint8_t* plaintext = malloc(len+16*sizeof(char));
  uint8_t* ciphertext = malloc(2*len);
  if (! (read_random_bytes(len, plaintext)))
    return 1;

  cycles a,b;
  clock_t t1,t2;

  long long unsigned maclen;
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    int res = crypto_aead_chacha20poly1305_ietf_encrypt_detached(ciphertext, mac, &maclen, plaintext, len, aad, 12, NULL, nonce, key);
    plaintext[0] = mac[0];
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  sodium_cy = (double)b - a;
  sodium_utime = (double)t2 - t1;
  print_results("Sodium ChachaPoly speed", (double)t2-t1,
		(double) b - a, ROUNDS, 1024 * 1024);
  for (int i = 0; i < len + 16 * sizeof(char); i++)
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);


  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    ossl_chacha20poly1305(ciphertext, mac, plaintext, len, aad, 12, nonce, key);
    plaintext[0] = mac[0];
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  ossl_cy = (double)b - a;
  ossl_utime = (double)t2 - t1;
  print_results("OpenSSL ChachaPoly speed", (double)t2-t1,
		(double) b - a, ROUNDS, 1024 * 1024);
  for (int i = 0; i < len + 16 * sizeof(char); i++)
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %" PRIx64 "\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    Chacha20Poly1305_aead_encrypt(ciphertext, mac, plaintext, len, aad, 12, key, nonce);
    plaintext[0] = mac[0];
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("Hacl ChachaPoly speed", (double)t2-t1,
		(double) b - a, ROUNDS, 1024 * 1024);
  for (int i = 0; i < CIPHERTEXT_LEN; i++)
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %" PRIx64 "x\n", res);

  flush_results("AEAD IETF", hacl_cy, sodium_cy, ossl_cy, 0, hacl_utime, sodium_utime, ossl_utime, 0, ROUNDS, PLAINLEN);

  return exit_success;
}

int32_t main(int argc, char *argv[])
{
  if (argc < 2 || strcmp(argv[1], "perf") == 0 ) {
    if (sodium_init() == -1) {
      printf("libsodium not installed? sodium_init failed\n");
      exit(EXIT_FAILURE);
    }
    int32_t res;
    res = test_api();
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
