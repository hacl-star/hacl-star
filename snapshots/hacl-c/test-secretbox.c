#include "kremlib.h"
#include "testlib.h"
#include "NaCl.h"
#include "sodium.h"
#include "tweetnacl.h"


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

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times 2^20 bytes: %llu (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times 2^20 bytes: %f (%fus/byte)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}

#define PLAINLEN (16*1024)
#define ROUNDS 3000

int32_t test_api()
{
  uint8_t    ciphertext[CIPHERTEXT_LEN+32] = {0};
  uint8_t    mac[16] = {0}; 
  uint8_t    decrypted[MESSAGE_LEN+32] = {0};
  uint32_t res;
  int i;

  /* Testing the secret box primitives */  
  crypto_secretbox_detached(ciphertext+32, mac, msg+32, MESSAGE_LEN, nonce, key); 
  res = NaCl_crypto_secretbox_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, key); 
  printf("HACL decryption of libsodium encryption was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("HACL secretbox", msg+32, decrypted+32, MESSAGE_LEN);
  memset(decrypted,0,MESSAGE_LEN);

  NaCl_crypto_secretbox_easy(ciphertext, msg, MESSAGE_LEN, nonce, key);
  res = crypto_secretbox_open_easy(decrypted, ciphertext+16, MESSAGE_LEN+16, nonce, key);
  printf("Libsodium decryption of HACL encryption was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("HACL secretbox", msg+32, decrypted, MESSAGE_LEN-32);
  return exit_success;
}

int32_t perf_api() {
  uint32_t len = PLAINLEN * sizeof(char);
  uint8_t* plaintext = malloc(len+16*sizeof(char));
  uint8_t* ciphertext = malloc(len+16*sizeof(char));
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plaintext, len);
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }

  cycles a,b;
  clock_t t1,t2;

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    NaCl_crypto_secretbox_easy(plaintext, plaintext, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("Hacl SecretBox speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < CIPHERTEXT_LEN; i++) 
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %llx\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    int res = crypto_secretbox_easy(plaintext, plaintext, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("Sodium SecretBox speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < len + 16 * sizeof(char); i++) 
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %llx\n", res);

  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    int res = tweet_crypto_secretbox(plaintext, plaintext, len, nonce, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("TweetNacl SecretBox speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < len + 16 * sizeof(char); i++) 
    res += (uint64_t) ciphertext[i];
  printf("Composite result (ignore): %llx\n", res);

  return exit_success;
}

int32_t main()
{
  if (sodium_init() == -1) {
    printf("libsodium not installed? sodium_init failed\n");
    exit(EXIT_FAILURE);
  }
  int32_t res = test_api();
  if (res == exit_success) {
    res = perf_api();
  }
  return res;
}
  
