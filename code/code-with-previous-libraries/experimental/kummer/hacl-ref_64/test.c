#include "smult.h"

#include <string.h>
#include <stdint.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>

#define SCALARSIZE 32
#define KEYSIZE 48
#define ROUNDS (64 * 1024)
static const unsigned char base[48] = {
  6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0x68,0x30,0x1e,0x6b,0x4d,0xaf,0xc7,0x56,0x9d,0x1f,0xa7,0xf8,0x71,0x39,0x37,0x6b,
  1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
} ;



static __inline__ unsigned long long rdtsc(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
  return ( (unsigned long long)lo)|( ((unsigned long long)hi)<<32 );
}

int32_t main()
{
  uint32_t keysize = (uint32_t )32;
  uint8_t result[keysize];
  memset(result, 0, keysize * sizeof result[0]);
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
  //crypto_scalarmult(result, scalar1, input1);
  //crypto_scalarmult(result, scalar2, input2);
  // TestLib_compare_and_print(curve25519, expected2, result, keysize);
  int i;
  unsigned char *pk, *sk, *mypk, *in;
  int fd = open("/dev/random", O_RDONLY);
  uint64_t res;
  in = malloc(2 * KEYSIZE * ROUNDS * sizeof(char));
  res = read(fd, in, 2 * KEYSIZE * ROUNDS * sizeof(char));
  if (res != 2 * KEYSIZE * ROUNDS * sizeof(char)) {
    printf("Error on reading, got read = %lu\n", res);
    return 1;
  }
  pk = malloc(KEYSIZE * ROUNDS * sizeof(char));
  sk = malloc(KEYSIZE * ROUNDS * sizeof(char));
  mypk = malloc(KEYSIZE * ROUNDS * sizeof(char));
  memcpy(sk, in, KEYSIZE * ROUNDS * sizeof (char));
  memcpy(mypk, in + KEYSIZE * ROUNDS, KEYSIZE * ROUNDS * sizeof (char));

  unsigned long long a, b;
  a = rdtsc();
  for (i = 0; i < ROUNDS; i++){
    crypto_scalarmult(pk + KEYSIZE * i, sk + KEYSIZE * i, mypk + KEYSIZE * i);
  }
  b = rdtsc();
  printf("Cycles for kummer ref5u: %f\n", (float)(b - a) / ROUNDS);
  for (i = 0; i < ROUNDS; i++) res += (uint64_t)*(pk+KEYSIZE*i) + (uint64_t)*(pk+KEYSIZE*i+8)
                                 + (uint64_t)*(pk+KEYSIZE*i+16) + (uint64_t)*(pk+KEYSIZE*i+24);
  printf("%llx\n", res);
  return 0;
}
