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

extern void Hacl_AES_128_BitSlice_aes128_ctr_encrypt(int in_len, uint8_t* out, uint8_t* in, uint8_t* k, uint8_t* n, uint32_t c);
extern void Hacl_AES_128_BitSlice_aes128_init(uint64_t *ctx, uint8_t *key, uint8_t *nonce);
extern void
Hacl_AES_128_BitSlice_aes_ctr(
  uint32_t len,
  uint8_t *out,
  uint8_t *inp,
  uint64_t *ctx,
  uint32_t counter,
  uint32_t rounds);

#define ROUNDS 40960
#define SIZE   16384

int main() {
  int in_len = 32;
  uint8_t in[32] = {
    0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
    0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
    0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
    0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F};
  uint8_t k[16] = {
    0x7E,0x24,0x06,0x78,0x17,0xFA,0xE0,0xD7,
    0x43,0xD6,0xCE,0x1F,0x32,0x53,0x91,0x63};
  uint8_t n[12] = {
    0x00,0x6C,0xB6,0xDB,0xC0,0x54,0x3B,0x59,
    0xDA,0x48,0xD9,0x0B};
  uint8_t exp[32] = {
    0x51,0x04,0xA1,0x06,0x16,0x8A,0x72,0xD9,
    0x79,0x0D,0x41,0xEE,0x8E,0xDA,0xD3,0x88,
    0xEB,0x2E,0x1E,0xFC,0x46,0xDA,0x57,0xC8,
    0xFC,0xE6,0x30,0xDF,0x91,0x41,0xBE,0x28};
  uint8_t comp[32] = {0};
  bool ok = true;

  uint64_t ctx[(uint32_t)8U + (uint32_t)15U * (uint32_t)8U] = {0};

  Hacl_AES_128_BitSlice_aes128_ctr_encrypt(in_len,comp,in,k,n,1);

  printf("AES-BitSlice computed:");
  for (int i = 0; i < 32; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("AES-BitSlice expected:");
  for (int i = 0; i < 32; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 32; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Success!\n");

  uint64_t len = SIZE;
  uint8_t plain[SIZE];
  uint8_t key[16];
  uint8_t nonce[12];
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS * SIZE;
  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  for (int j = 0; j < ROUNDS; j++) {
    Hacl_AES_128_BitSlice_aes128_ctr_encrypt(SIZE,plain,plain,key,nonce,1);
  }

  t1 = clock();
  a = cpucycles_begin();
  for (int j = 0; j < ROUNDS; j++) {
   Hacl_AES_128_BitSlice_aes128_ctr_encrypt(SIZE,plain,plain,key,nonce,1);
 //   Hacl_AES_128_BitSlice_aes128_init(ctx,key,nonce);
 //   Hacl_AES_128_BitSlice_aes_ctr(SIZE,plain,plain,ctx,1,10);

  }
  b = cpucycles_end();
  t2 = clock();
  clock_t tdiff2 = t2 - t1;
  cycles cdiff2 = b - a;

  printf("AES-BitSlice PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff2,(double)cdiff2/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff2,(double)tdiff2/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff2 / CLOCKS_PER_SEC) * 1000000.0));


}
