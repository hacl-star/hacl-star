#include "kremlib.h"
#include "testlib.h"
#include "Curve25519.h"
#include "sodium.h"
#include "ec_lcl.h"


void ossl_curve25519(uint8_t* result, uint8_t* scalar, uint8_t* input){
  X25519(result, scalar, input);
}



unsigned long long median(unsigned long long* a, int rounds) {
  int i, j, temp;
  for (i = 0; i < rounds - 1; ++i)
    {
      for (j = 0; j < rounds - 1 - i; ++j )
	{
	  if (a[j] > a[j+1])
	    {
	      temp = a[j+1];
	      a[j+1] = a[j];
	      a[j] = temp;
	    }
	}
    }
  return a[rounds/8];
}

void print_results(char *txt, double t1, unsigned long long d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d scalar mults: %llu (%.2fcycles/mul)\n", rounds, d1, (double)d1/rounds);
  printf("User time for %d scalar mults: %f (%fus/mul)\n", rounds, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/rounds);
}

#define KEYSIZE 32
#define ROUNDS 1000

  uint8_t
  scalar1[32] =
    {
      (uint8_t )0xa5,
      (uint8_t )0x46,
      (uint8_t )0xe3,
      (uint8_t )0x6b,
      (uint8_t )0xf0,
      (uint8_t )0x52,
      (uint8_t )0x7c,
      (uint8_t )0x9d,
      (uint8_t )0x3b,
      (uint8_t )0x16,
      (uint8_t )0x15,
      (uint8_t )0x4b,
      (uint8_t )0x82,
      (uint8_t )0x46,
      (uint8_t )0x5e,
      (uint8_t )0xdd,
      (uint8_t )0x62,
      (uint8_t )0x14,
      (uint8_t )0x4c,
      (uint8_t )0x0a,
      (uint8_t )0xc1,
      (uint8_t )0xfc,
      (uint8_t )0x5a,
      (uint8_t )0x18,
      (uint8_t )0x50,
      (uint8_t )0x6a,
      (uint8_t )0x22,
      (uint8_t )0x44,
      (uint8_t )0xba,
      (uint8_t )0x44,
      (uint8_t )0x9a,
      (uint8_t )0xc4
    };
  uint8_t
  scalar2[32] =
    {
      (uint8_t )0x4b,
      (uint8_t )0x66,
      (uint8_t )0xe9,
      (uint8_t )0xd4,
      (uint8_t )0xd1,
      (uint8_t )0xb4,
      (uint8_t )0x67,
      (uint8_t )0x3c,
      (uint8_t )0x5a,
      (uint8_t )0xd2,
      (uint8_t )0x26,
      (uint8_t )0x91,
      (uint8_t )0x95,
      (uint8_t )0x7d,
      (uint8_t )0x6a,
      (uint8_t )0xf5,
      (uint8_t )0xc1,
      (uint8_t )0x1b,
      (uint8_t )0x64,
      (uint8_t )0x21,
      (uint8_t )0xe0,
      (uint8_t )0xea,
      (uint8_t )0x01,
      (uint8_t )0xd4,
      (uint8_t )0x2c,
      (uint8_t )0xa4,
      (uint8_t )0x16,
      (uint8_t )0x9e,
      (uint8_t )0x79,
      (uint8_t )0x18,
      (uint8_t )0xba,
      (uint8_t )0x0d
    };
  uint8_t
  input1[32] =
    {
      (uint8_t )0xe6,
      (uint8_t )0xdb,
      (uint8_t )0x68,
      (uint8_t )0x67,
      (uint8_t )0x58,
      (uint8_t )0x30,
      (uint8_t )0x30,
      (uint8_t )0xdb,
      (uint8_t )0x35,
      (uint8_t )0x94,
      (uint8_t )0xc1,
      (uint8_t )0xa4,
      (uint8_t )0x24,
      (uint8_t )0xb1,
      (uint8_t )0x5f,
      (uint8_t )0x7c,
      (uint8_t )0x72,
      (uint8_t )0x66,
      (uint8_t )0x24,
      (uint8_t )0xec,
      (uint8_t )0x26,
      (uint8_t )0xb3,
      (uint8_t )0x35,
      (uint8_t )0x3b,
      (uint8_t )0x10,
      (uint8_t )0xa9,
      (uint8_t )0x03,
      (uint8_t )0xa6,
      (uint8_t )0xd0,
      (uint8_t )0xab,
      (uint8_t )0x1c,
      (uint8_t )0x4c
    };
  uint8_t
  input2[32] =
    {
      (uint8_t )0xe5,
      (uint8_t )0x21,
      (uint8_t )0x0f,
      (uint8_t )0x12,
      (uint8_t )0x78,
      (uint8_t )0x68,
      (uint8_t )0x11,
      (uint8_t )0xd3,
      (uint8_t )0xf4,
      (uint8_t )0xb7,
      (uint8_t )0x95,
      (uint8_t )0x9d,
      (uint8_t )0x05,
      (uint8_t )0x38,
      (uint8_t )0xae,
      (uint8_t )0x2c,
      (uint8_t )0x31,
      (uint8_t )0xdb,
      (uint8_t )0xe7,
      (uint8_t )0x10,
      (uint8_t )0x6f,
      (uint8_t )0xc0,
      (uint8_t )0x3c,
      (uint8_t )0x3e,
      (uint8_t )0xfc,
      (uint8_t )0x4c,
      (uint8_t )0xd5,
      (uint8_t )0x49,
      (uint8_t )0xc7,
      (uint8_t )0x15,
      (uint8_t )0xa4,
      (uint8_t )0x93
    };
  uint8_t
  expected1[32] =
    {
      (uint8_t )0xc3,
      (uint8_t )0xda,
      (uint8_t )0x55,
      (uint8_t )0x37,
      (uint8_t )0x9d,
      (uint8_t )0xe9,
      (uint8_t )0xc6,
      (uint8_t )0x90,
      (uint8_t )0x8e,
      (uint8_t )0x94,
      (uint8_t )0xea,
      (uint8_t )0x4d,
      (uint8_t )0xf2,
      (uint8_t )0x8d,
      (uint8_t )0x08,
      (uint8_t )0x4f,
      (uint8_t )0x32,
      (uint8_t )0xec,
      (uint8_t )0xcf,
      (uint8_t )0x03,
      (uint8_t )0x49,
      (uint8_t )0x1c,
      (uint8_t )0x71,
      (uint8_t )0xf7,
      (uint8_t )0x54,
      (uint8_t )0xb4,
      (uint8_t )0x07,
      (uint8_t )0x55,
      (uint8_t )0x77,
      (uint8_t )0xa2,
      (uint8_t )0x85,
      (uint8_t )0x52
    };
  uint8_t
  expected2[32] =
    {
      (uint8_t )0x95,
      (uint8_t )0xcb,
      (uint8_t )0xde,
      (uint8_t )0x94,
      (uint8_t )0x76,
      (uint8_t )0xe8,
      (uint8_t )0x90,
      (uint8_t )0x7d,
      (uint8_t )0x7a,
      (uint8_t )0xad,
      (uint8_t )0xe4,
      (uint8_t )0x5c,
      (uint8_t )0xb4,
      (uint8_t )0xb8,
      (uint8_t )0x73,
      (uint8_t )0xf8,
      (uint8_t )0x8b,
      (uint8_t )0x59,
      (uint8_t )0x5a,
      (uint8_t )0x68,
      (uint8_t )0x79,
      (uint8_t )0x9f,
      (uint8_t )0xa1,
      (uint8_t )0x52,
      (uint8_t )0xe6,
      (uint8_t )0xf8,
      (uint8_t )0xf7,
      (uint8_t )0x64,
      (uint8_t )0x7a,
      (uint8_t )0xac,
      (uint8_t )0x79,
      (uint8_t )0x57
    };

int32_t test_curve()
{
  uint32_t keysize = (uint32_t )32;
  uint8_t result[keysize];
  memset(result, 0, keysize * sizeof result[0]);

  Curve25519_crypto_scalarmult(result, scalar1, input1);
  TestLib_compare_and_print("HACL Curve25519", expected1, result, keysize);
  Curve25519_crypto_scalarmult(result, scalar2, input2);
  TestLib_compare_and_print("HACL Curve25519", expected2, result, keysize);

  int res = crypto_scalarmult_curve25519(result, scalar1, input1);
  TestLib_compare_and_print("Sodium Curve25519", expected1, result, keysize);
  res = crypto_scalarmult_curve25519(result, scalar2, input2);
  TestLib_compare_and_print("Sodium Curve25519", expected2, result, keysize);
  
  return exit_success;
}

int32_t perf_curve() {
  uint32_t len = KEYSIZE * ROUNDS * sizeof(char);

  unsigned char *pk, *sk, *mul;

  pk = malloc(KEYSIZE * ROUNDS * sizeof(char));
  sk = malloc(KEYSIZE * ROUNDS * sizeof(char));
  mul = malloc(KEYSIZE * ROUNDS * sizeof(char));

  int fd = open("/dev/urandom", O_RDONLY);
  uint64_t res = read(fd, sk, len);
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }
  res = read(fd, pk, len);
  if (res != len) {
    printf("Error on reading, got %llu bytes\n", res);
    return 1;
  }

  unsigned long long d[ROUNDS];
  cycles a,b;
  clock_t t1,t2;
  t1 = clock();
  for (int i = 0; i < ROUNDS; i++){
    a = TestLib_cpucycles();
    Curve25519_crypto_scalarmult(mul + KEYSIZE * i, sk + KEYSIZE * i, pk + KEYSIZE * i);
    b = TestLib_cpucycles();
    d[i] = b - a;
  }
  t2 = clock();
  print_results("HACL Curve25519 speed", (double)t2-t1, (double) median(d,ROUNDS), ROUNDS, 1);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(mul+KEYSIZE*i) + (uint64_t)*(mul+KEYSIZE*i+8)
                                 + (uint64_t)*(mul+KEYSIZE*i+16) + (uint64_t)*(mul+KEYSIZE*i+24);
  printf("Composite result (ignore): %llx\n", res);

  t1 = clock();
  for (int i = 0; i < ROUNDS; i++){
    a = TestLib_cpucycles();
    res = crypto_scalarmult_curve25519(mul + KEYSIZE * i, sk + KEYSIZE * i, pk + KEYSIZE * i);
    b = TestLib_cpucycles();
    d[i] = b - a;
  }
  t2 = clock();
  print_results("Sodium Curve25519 speed", (double)t2-t1, (double) median(d,ROUNDS), ROUNDS, 1);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(mul+KEYSIZE*i) + (uint64_t)*(mul+KEYSIZE*i+8)
                                 + (uint64_t)*(mul+KEYSIZE*i+16) + (uint64_t)*(mul+KEYSIZE*i+24);
  printf("Composite result (ignore): %llx\n", res);

  t1 = clock();
  for (int i = 0; i < ROUNDS; i++){
    a = TestLib_cpucycles();
    ossl_curve25519(mul + KEYSIZE * i, sk + KEYSIZE * i, pk + KEYSIZE * i);
    b = TestLib_cpucycles();
    d[i] = b - a;
  }
  t2 = clock();
  print_results("OpenSSL Curve25519 speed", (double)t2-t1, (double) median(d,ROUNDS), ROUNDS, 1);
  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(mul+KEYSIZE*i) + (uint64_t)*(mul+KEYSIZE*i+8)
                                 + (uint64_t)*(mul+KEYSIZE*i+16) + (uint64_t)*(mul+KEYSIZE*i+24);
  printf("Composite result (ignore): %llx\n", res);

  return exit_success;
}

int32_t main()
{
  int32_t res = test_curve();
  if (res == exit_success) {
    res = perf_curve();
  }
  return res;
}
  
