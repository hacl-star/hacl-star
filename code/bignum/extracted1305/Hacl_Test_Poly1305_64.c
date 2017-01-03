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
#include "Hacl_EC.h"
#include "kremlib.h"
#include "testlib.h"
#include "Prims.h"
#include "Hacl_Poly1305.h"

#define ROUNDS (1024)
#define MACSIZE 32

static __inline__ unsigned long long rdtsc(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
  return ( (unsigned long long)lo)|( ((unsigned long long)hi)<<32 );
}

int32_t main()
{
  uint64_t len_ = (uint64_t )34;
  uint32_t macsize = (uint32_t )16;
  uint8_t mac[macsize];
  memset(mac, 0, macsize * sizeof mac[0]);
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
  Hacl_MAC_Poly1305_64_crypto_onetimeauth(mac, plaintext, len_, key);
  int8_t poly1305[1] = { (int8_t )0 };
  TestLib_compare_and_print(poly1305, expected, mac, macsize);

  uint8_t* macs = malloc(ROUNDS * MACSIZE * sizeof(char));
  int fd = open("1GB.bin", O_RDONLY);
  uint64_t res;
  len_ = 1024 * 1024 * sizeof(char);
  uint8_t* plain = malloc(len_);
  res = read(fd, plain, len_);
  if (res != len_) {
    printf("Error on reading, got read = %lu\n", res);
    return 1;
  }

  unsigned long long a, b;
  a = rdtsc();
  for (int i = 0; i < ROUNDS; i++){
    Hacl_MAC_Poly1305_64_crypto_onetimeauth(macs + MACSIZE * i, plain, len_, key);
  }
  b = rdtsc();
  printf("Cycles/byte for the polymac: %f\n", (float)(b - a) / (ROUNDS * len_));

  for (int i = 0; i < ROUNDS; i++) res += (uint64_t)*(macs+MACSIZE*i) + (uint64_t)*(macs+MACSIZE*i+8)
                                 + (uint64_t)*(macs+MACSIZE*i+16) + (uint64_t)*(macs+MACSIZE*i+24);

  printf("%llx\n", res);

  return exit_success;
}

