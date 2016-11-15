#include "testlib.h"
#include "Hacl_Box.h"
#include "Hacl_Symmetric_XSalsa20.h"
#include <time.h>
#include "testutils.h"

#define MESSAGE_LEN 44
#define secretbox_MACBYTES   16
#define CIPHERTEXT_LEN (secretbox_MACBYTES + MESSAGE_LEN)
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24

uint8_t *msg = (uint8_t*) "testtesttesttesttesttesttesttesttesttesttest";

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

uint8_t sk[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

#define SIZE (1024*1024)
#define ROUNDS 1000

void test_box() {
  void *plain = malloc(SIZE), *cipher = malloc(SIZE);
  uint8_t mac[16];
  clock_t c1, c2;
  double t1, t2;
  unsigned long long a,b,d1,d2;
  int i;
  c1 = clock();
  a = rdtsc();
  for (i=0; i<ROUNDS; i++) Hacl_SecretBox_crypto_secretbox_detached(cipher, mac, plain, SIZE, nonce, key);
  b = rdtsc();
  c2 = clock();
  d1 = b - a;
  printf("[Box] No of cycles for HACL: %llu\n", d1);
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("[Box] User time for HACL: %f\n", t1);
  printf("[Box] Cycles/byte ratio HACL): %lf\n", (double)d1/SIZE/ROUNDS);
  free(plain);
  free(cipher);
}

void test_poly1305() {
  void *plain = malloc(SIZE);
  uint8_t mac[16];
  clock_t c1, c2;
  double t1, t2, t3;
  unsigned long long a,b,d1,d2,d3;
  int i;
  c1 = clock();
  a = rdtsc();
  for (i=0; i<ROUNDS; i++) Hacl_Symmetric_Poly1305_64_crypto_onetimeauth(mac, plain, SIZE, key);
  b = rdtsc();
  c2 = clock();
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  d1 = b - a;
  printf("[Poly1305] User time for HACL 64bit: %f\n", t1);
  printf("[Poly1305] Cycles/byte ratio HACL64: %lf\n", (double)d1/SIZE/ROUNDS);
  free(plain);
}

void test_xsalsa20() {
  void *plain = malloc(SIZE), *cipher = malloc(SIZE);
  uint8_t mac[16];
  clock_t c1, c2;
  double t1, t2;
  unsigned long long a, b, d;
  int i;
  c1 = clock();
  a = rdtsc();
  for (i=0; i<ROUNDS; i++) Hacl_Symmetric_XSalsa20_crypto_stream_xsalsa20_xor(cipher, plain, SIZE, nonce, key);
  b = rdtsc();
  c2 = clock();
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  d = b - a;
  printf("[XSalsa20] User time for HACL: %f\n", t1);
  printf("[XSalsa20] Cycles/byte ratio HACL64: %lf\n", (double)d/SIZE/ROUNDS);
  free(plain);
  free(cipher);
}

void test_curve25519() {
  void *plain = malloc(SIZE), *cipher = malloc(SIZE);
  uint8_t pk[32];
  clock_t c1, c2;
  double t1, t2;
  unsigned long long a, b, d1, d2;
  int i;
  c1 = clock();
  a = rdtsc ();
  for (i = 0; i < ROUNDS; i++) Hacl_EC_Curve25519_exp(pk, key, sk);
  b = rdtsc ();
  c2 = clock();
  d1 = b - a;
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("[Curve25519] User time for HACL: %f\n", t1);
  printf("[Curve25519] User time/rounds for HACL: %f\n", t1/ROUNDS);
  printf("[Curve25519] Cycles/rounds ratio HACL64: %lf\n", (double)d1/ROUNDS);
  free(plain);
  free(cipher);
}

int main(int argc, char *argv[]){
  if (argc == 2 && strcmp(argv[1], "box") == 0) {
    test_box();
  } else if (argc == 2 && strcmp(argv[1], "poly1305") == 0) {
    test_poly1305();
  } else if (argc == 2 && strcmp(argv[1], "xsalsa20") == 0) {
    test_xsalsa20();
  } else if (argc == 2 && strcmp(argv[1], "curve25519") == 0) {
    test_curve25519();
  }
}
