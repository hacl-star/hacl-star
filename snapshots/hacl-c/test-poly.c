#include "kremlib.h"
#include "testlib.h"
#include "Poly1305_64.h"
#include "sodium.h"
#include "internal/poly1305.h"
#include "poly1305_local.h"

void ossl_poly1305(uint8_t* mac, uint8_t* plain, int len, uint8_t* key){
  POLY1305 state;
  Poly1305_Init(&state,key);
  Poly1305_Update(&state,plain,len);
  Poly1305_Final(&state,mac);
}

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times 2^20 bytes: %llu (%.2fcycles/byte)\n", rounds, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times 2^20 bytes: %f (%fus/byte)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}

#define PLAINLEN (1024*1024)
#define ROUNDS 1000
#define MACSIZE 32

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
  uint32_t macsize = (uint32_t )16;
  uint8_t mac[macsize];
  memset(mac, 0, macsize * sizeof mac[0]);
  Poly1305_64_crypto_onetimeauth(mac, plaintext, len_, key);
  TestLib_compare_and_print("HACL Poly1305", expected, mac, macsize);
  Poly1305_64_crypto_onetimeauth(mac, plaintext, len_, key);
  TestLib_compare_and_print("Sodium Poly1305", expected, mac, macsize);
  return exit_success;
}

int32_t perf_poly() {
  uint32_t len = PLAINLEN * sizeof(char);
  uint8_t* plain = malloc(len);
  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, plain, len);
  uint8_t* macs = malloc(ROUNDS * MACSIZE * sizeof(char));
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }

  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    Poly1305_64_crypto_onetimeauth(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("HACL Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %llx\n", res);
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    crypto_onetimeauth(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("Sodium Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %llx\n", res);


  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++){
    ossl_poly1305(macs + MACSIZE * i, plain, len, key);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
  print_results("OpenSSL Poly1305 speed", (double)t2-t1,
		(double) b - a, ROUNDS, PLAINLEN);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
				     + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);
  printf("Composite result (ignore): %llx\n", res);

  return exit_success;
}

int32_t main()
{
  int32_t res = test_poly();
  if (res == exit_success) {
    res = perf_poly();
  }
  return res;
}
  
