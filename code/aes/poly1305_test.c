#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>

typedef uint64_t cycles;

static __inline__ cycles cpucycles_begin(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
  //  unsigned hi, lo;
  //__asm__ __volatile__ ("CPUID\n\t"  "RDTSC\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t": "=r" (hi), "=r" (lo):: "%rax", "%rbx", "%rcx", "%rdx");
  //return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

static __inline__ cycles cpucycles_end(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
  //  unsigned hi, lo;
  //__asm__ __volatile__ ("RDTSCP\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t"  "CPUID\n\t": "=r" (hi), "=r" (lo)::     "%rax", "%rbx", "%rcx", "%rdx");
  //return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

extern void Hacl_Poly1305_64_poly1305_mac(uint8_t* out, uint8_t* in, int in_len, uint8_t* k);
extern void Hacl_Poly1305_32_poly1305_mac(uint8_t* out, uint8_t* in, int in_len, uint8_t* k);

#define ROUNDS 10240
#define SIZE   16384

int main() {
  int in_len = 34;
  uint8_t in[34] = {
    0x43, 0x72, 0x79, 0x70, 0x74, 0x6f, 0x67, 0x72,
    0x61, 0x70, 0x68, 0x69, 0x63, 0x20, 0x46, 0x6f,
    0x72, 0x75, 0x6d, 0x20, 0x52, 0x65, 0x73, 0x65,
    0x61, 0x72, 0x63, 0x68, 0x20, 0x47, 0x72, 0x6f,
    0x75, 0x70};
  uint8_t key[32] = {
    0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33,
    0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
    0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd,
    0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b
  };
  uint8_t exp[16] = {
    0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6,
    0xc2, 0x2b, 0x8b, 0xaf, 0x0c, 0x01, 0x27, 0xa9
  };

  int in_len2 = 16;
  uint8_t in2[16] = {
		     0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
		    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
  };
  uint8_t key2[32] = {
		    0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
  };
  uint8_t exp2[16] = {
		    0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
  };

  uint8_t comp[16] = {0};
  bool ok = true;

  Hacl_Poly1305_64_poly1305_mac(comp,in,34,key);
  printf("Poly1305 (64-bit) Result:\n");
  printf("computed:");
  for (int i = 0; i < 16; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 16; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 16; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");
  
  Hacl_Poly1305_32_poly1305_mac(comp,in,in_len,key);
  printf("Poly1305 (32-bit) Result:\n");
  printf("computed:");
  for (int i = 0; i < 16; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 16; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 16; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");


  Hacl_Poly1305_64_poly1305_mac(comp,in2,in_len2,key2);
  printf("Poly1305 (64-bit) Result:\n");
  printf("computed:");
  for (int i = 0; i < 16; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 16; i++)
    printf("%02x",exp2[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 16; i++)
    ok = ok & (exp2[i] == comp[i]);
  if (ok) printf("Success!\n");
  
  Hacl_Poly1305_32_poly1305_mac(comp,in2,in_len2,key2);
  printf("Poly1305 (32-bit) Result:\n");
  printf("computed:");
  for (int i = 0; i < 16; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (int i = 0; i < 16; i++)
    printf("%02x",exp2[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 16; i++)
    ok = ok & (exp2[i] == comp[i]);
  if (ok) printf("Success!\n");

  uint8_t plain[SIZE];
  uint64_t res = 0;
  uint8_t tag[16];
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS * SIZE;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_64_poly1305_mac(plain,plain,SIZE,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_64_poly1305_mac(tag,plain,SIZE,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  memset(plain,'P',SIZE);
  memset(key,'K',16);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(plain,plain,SIZE,key);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Poly1305_32_poly1305_mac(tag,plain,SIZE,key);
    res ^= tag[0] ^ tag[15];
  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;

  printf("Poly1305 (64-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff1,(double)cdiff1/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff1,(double)tdiff1/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff1 / CLOCKS_PER_SEC) * 1000000.0));

  printf("Poly1305 (32-bit) PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff2,(double)cdiff2/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff2,(double)tdiff2/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff2 / CLOCKS_PER_SEC) * 1000000.0));
}
