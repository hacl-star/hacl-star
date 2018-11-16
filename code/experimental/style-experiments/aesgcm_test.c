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
#include <vec128.h>

typedef uint64_t cycles;

static __inline__ cycles cpucycles(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}


extern void Hacl_Impl_AesGCM_aes128_gcm_init(Lib_Vec128_vec128* ctx, uint8_t* k, uint8_t* n);
extern void Hacl_Impl_AesGCM_aes128_gcm_encrypt(Lib_Vec128_vec128* ctx, uint8_t* out, uint8_t* in, int in_len, uint8_t* aad, int aad_len);
extern int Hacl_Impl_AesGCM_aes128_gcm_decrypt(Lib_Vec128_vec128* ctx, uint8_t* out, uint8_t* in, int in_len, uint8_t* aad, int aad_len);

#define ROUNDS 10240
#define SIZE   16384

int main() {
  uint8_t in[60] = {
    0xd9, 0x31, 0x32, 0x25, 0xf8, 0x84, 0x06, 0xe5,
    0xa5, 0x59, 0x09, 0xc5, 0xaf, 0xf5, 0x26, 0x9a,
    0x86, 0xa7, 0xa9, 0x53, 0x15, 0x34, 0xf7, 0xda,
    0x2e, 0x4c, 0x30, 0x3d, 0x8a, 0x31, 0x8a, 0x72,
    0x1c, 0x3c, 0x0c, 0x95, 0x95, 0x68, 0x09, 0x53,
    0x2f, 0xcf, 0x0e, 0x24, 0x49, 0xa6, 0xb5, 0x25,
    0xb1, 0x6a, 0xed, 0xf5, 0xaa, 0x0d, 0xe6, 0x57,
    0xba, 0x63, 0x7b, 0x39};
  uint8_t k[16] = {
    0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c,
    0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83, 0x08
  };
  uint8_t n[12] = {
    0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce, 0xdb, 0xad,
    0xde, 0xca, 0xf8, 0x88
  };
  uint8_t aad[20] = {
    0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef,
    0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef,
    0xab, 0xad, 0xda, 0xd2
  };
  uint8_t exp[76] = {
    0x42, 0x83, 0x1e, 0xc2, 0x21, 0x77, 0x74, 0x24,
    0x4b, 0x72, 0x21, 0xb7, 0x84, 0xd0, 0xd4, 0x9c,
    0xe3, 0xaa, 0x21, 0x2f, 0x2c, 0x02, 0xa4, 0xe0,
    0x35, 0xc1, 0x7e, 0x23, 0x29, 0xac, 0xa1, 0x2e,
    0x21, 0xd5, 0x14, 0xb2, 0x54, 0x66, 0x93, 0x1c,
    0x7d, 0x8f, 0x6a, 0x5a, 0xac, 0x84, 0xaa, 0x05,
    0x1b, 0xa3, 0x0b, 0x39, 0x6a, 0x0a, 0xac, 0x97,
    0x3d, 0x58, 0xe0, 0x91, 0x5b, 0xc9, 0x4f, 0xbc,
    0x32, 0x21, 0xa5, 0xdb, 0x94, 0xfa, 0xe9, 0x5a,
    0xe7, 0x12, 0x1a, 0x47
  };
  uint8_t comp[76] = {0};
  bool ok = true;

  Lib_Vec128_vec128 ctx[22] = {0};
  Hacl_Impl_AesGCM_aes128_gcm_init(ctx,k,n);
  Hacl_Impl_AesGCM_aes128_gcm_encrypt(ctx,comp,in,60,aad,20);
  printf("AESGCM-NI computed:");
  for (int i = 0; i < 76; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("AESGCM_NI expected:");
  for (int i = 0; i < 76; i++)
    printf("%02x",exp[i]);
  printf("\n");
  ok = true;
  for (int i = 0; i < 76; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok) printf("Encrypt Success!\n");
  else printf("Encrypt FAILURE!\n");

  int res = Hacl_Impl_AesGCM_aes128_gcm_decrypt(ctx,comp,exp,76,aad,20);
  if (res == 0) 
    printf("AESGCM-NI Decrypt failed!");
  else {
    printf("AESGCM-NI Decrypt computed:");
    for (int i = 0; i < 60; i++)
      printf("%02x",comp[i]);
    printf("\n");
    printf("AESGCM_NI Decrypt expected:");
    for (int i = 0; i < 60; i++)
      printf("%02x",in[i]);
    printf("\n");
    ok = true;
    for (int i = 0; i < 60; i++)
      ok = ok & (in[i] == comp[i]);
    if (ok) printf("Decrypt Success!\n");
    else printf("Decrypt FAILURE!\n");
  }

  uint64_t len = SIZE;
  uint8_t plain[SIZE+16];
  uint8_t key[16];
  uint8_t nonce[12];
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS * SIZE;
  memset(plain,'P',SIZE);
  memset(key,'K',16);
  memset(nonce,'N',12);

  Hacl_Impl_AesGCM_aes128_gcm_init(ctx,key,nonce);
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_AesGCM_aes128_gcm_encrypt(ctx,plain,plain,SIZE,aad,20);
  }

  t1 = clock();
  a = cpucycles();
  for (int j = 0; j < ROUNDS; j++) {
    Hacl_Impl_AesGCM_aes128_gcm_encrypt(ctx,plain,plain,SIZE,aad,20);
  }
  b = cpucycles();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  printf("AES-NI PERF:\n");
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",count,(uint64_t)cdiff1,(double)cdiff1/count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",count,(uint64_t)tdiff1,(double)tdiff1/count);
  printf("bw %8.2f MB/s\n",(double)count/(((double)tdiff1 / CLOCKS_PER_SEC) * 1000000.0));
  
}
