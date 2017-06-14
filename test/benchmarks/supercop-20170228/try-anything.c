/*
 * try-anything.c version 20140425
 * D. J. Bernstein
 * Some portions adapted from TweetNaCl by Bernstein, Janssen, Lange, Schwabe.
 * Public domain.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/resource.h>
#include "cpucycles.h"
#include "crypto_uint8.h"
#include "crypto_uint32.h"
#include "crypto_uint64.h"
#include "try.h"

typedef crypto_uint8 u8;
typedef crypto_uint32 u32;
typedef crypto_uint64 u64;

#define FOR(i,n) for (i = 0;i < n;++i)

static u32 L32(u32 x,int c) { return (x << c) | ((x&0xffffffff) >> (32 - c)); }

static u32 ld32(const u8 *x)
{
  u32 u = x[3];
  u = (u<<8)|x[2];
  u = (u<<8)|x[1];
  return (u<<8)|x[0];
}

static void st32(u8 *x,u32 u)
{
  int i;
  FOR(i,4) { x[i] = u; u >>= 8; }
}

static const u8 sigma[17] = "expand 32-byte k";

static void core(u8 *out,const u8 *in,const u8 *k)
{
  u32 w[16],x[16],y[16],t[4];
  int i,j,m;

  FOR(i,4) {
    x[5*i] = ld32(sigma+4*i);
    x[1+i] = ld32(k+4*i);
    x[6+i] = ld32(in+4*i);
    x[11+i] = ld32(k+16+4*i);
  }

  FOR(i,16) y[i] = x[i];

  FOR(i,20) {
    FOR(j,4) {
      FOR(m,4) t[m] = x[(5*j+4*m)%16];
      t[1] ^= L32(t[0]+t[3], 7);
      t[2] ^= L32(t[1]+t[0], 9);
      t[3] ^= L32(t[2]+t[1],13);
      t[0] ^= L32(t[3]+t[2],18);
      FOR(m,4) w[4*j+(j+m)%4] = t[m];
    }
    FOR(m,16) x[m] = w[m];
  }

  FOR(i,16) st32(out + 4 * i,x[i] + y[i]);
}

static void salsa20(u8 *c,u64 b,const u8 *n,const u8 *k)
{
  u8 z[16],x[64];
  u32 u,i;
  if (!b) return;
  FOR(i,16) z[i] = 0;
  FOR(i,8) z[i] = n[i];
  while (b >= 64) {
    core(x,z,k);
    FOR(i,64) c[i] = x[i];
    u = 1;
    for (i = 8;i < 16;++i) {
      u += (u32) z[i];
      z[i] = u;
      u >>= 8;
    }
    b -= 64;
    c += 64;
  }
  if (b) {
    core(x,z,k);
    FOR(i,b) c[i] = x[i];
  }
}

static void increment(u8 *n)
{
  if (!++n[0])
    if (!++n[1])
      if (!++n[2])
        if (!++n[3])
          if (!++n[4])
            if (!++n[5])
              if (!++n[6])
                if (!++n[7])
                  ;
}

void randombytes(unsigned char *x,unsigned long long xlen)
{
  const static unsigned char randombytes_k[33] = "answer randombytes from crypto_*";
  static unsigned char randombytes_n[8];
  salsa20(x,xlen,randombytes_n,randombytes_k);
  increment(randombytes_n);
}

static void testvector(unsigned char *x,unsigned long long xlen)
{
  const static unsigned char testvector_k[33] = "generate inputs for test vectors";
  static unsigned char testvector_n[8];
  salsa20(x,xlen,testvector_n,testvector_k);
  increment(testvector_n);
}

unsigned long long myrandom(void)
{
  unsigned char x[8];
  unsigned long long result;
  testvector(x,8);
  result = x[7];
  result = (result<<8)|x[6];
  result = (result<<8)|x[5];
  result = (result<<8)|x[4];
  result = (result<<8)|x[3];
  result = (result<<8)|x[2];
  result = (result<<8)|x[1];
  result = (result<<8)|x[0];
  return result;
}

static void canary(unsigned char *x,unsigned long long xlen)
{
  const static unsigned char canary_k[33] = "generate pad to catch overwrites";
  static unsigned char canary_n[8];
  salsa20(x,xlen,canary_n,canary_k);
  increment(canary_n);
}

void double_canary(unsigned char *x2,unsigned char *x,unsigned long long xlen)
{
  canary(x - 16,16);
  canary(x + xlen,16);
  memcpy(x2 - 16,x - 16,16);
  memcpy(x2 + xlen,x + xlen,16);
}

void input_prepare(unsigned char *x2,unsigned char *x,unsigned long long xlen)
{
  testvector(x,xlen);
  canary(x - 16,16);
  canary(x + xlen,16);
  memcpy(x2 - 16,x - 16,xlen + 32);
}

void input_compare(const unsigned char *x2,const unsigned char *x,unsigned long long xlen,const char *fun)
{
  if (memcmp(x2 - 16,x - 16,xlen + 32)) {
    printf("%s overwrites input\n",fun);
    exit(111);
  }
}

void output_prepare(unsigned char *x2,unsigned char *x,unsigned long long xlen)
{
  canary(x - 16,xlen + 32);
  memcpy(x2 - 16,x - 16,xlen + 32);
}

void output_compare(const unsigned char *x2,const unsigned char *x,unsigned long long xlen,const char *fun)
{
  if (memcmp(x2 - 16,x - 16,16)) {
    printf("%s writes before output\n",fun);
    exit(111);
  }
  if (memcmp(x2 + xlen,x + xlen,16)) {
    printf("%s writes after output\n",fun);
    exit(111);
  }
}

static unsigned char checksum_state[64];
static char checksum_hex[65];

void checksum(const unsigned char *x,unsigned long long xlen)
{
  u8 block[16];
  int i;
  while (xlen >= 16) {
    core(checksum_state,x,checksum_state);
    x += 16;
    xlen -= 16;
  }
  FOR(i,16) block[i] = 0;
  FOR(i,xlen) block[i] = x[i];
  block[xlen] = 1;
  checksum_state[0] ^= 1;
  core(checksum_state,block,checksum_state);
}

static void printword(const char *s)
{
  if (!*s) putchar('-');
  while (*s) {
    if (*s == ' ') putchar('_');
    else if (*s == '\t') putchar('_');
    else if (*s == '\r') putchar('_');
    else if (*s == '\n') putchar('_');
    else putchar(*s);
    ++s;
  }
  putchar(' ');
}

static void printnum(long long x)
{
  printf("%lld ",x);
}

void fail(const char *why)
{
  printf("%s\n",why);
  exit(111);
}

unsigned char *alignedcalloc(unsigned long long len)
{
  unsigned char *x = (unsigned char *) calloc(1,len + 256);
  long long i;
  if (!x) fail("out of memory");
  /* will never deallocate so shifting is ok */
  for (i = 0;i < len + 256;++i) x[i] = random();
  x += 64;
  x += 63 & (-(unsigned long) x);
  for (i = 0;i < len;++i) x[i] = 0;
  return x;
}

#define TIMINGS 63
static long long cycles[TIMINGS + 1];

void limits()
{
#ifdef RLIM_INFINITY
  struct rlimit r;
  r.rlim_cur = 0;
  r.rlim_max = 0;
#ifdef RLIMIT_NOFILE
  setrlimit(RLIMIT_NOFILE,&r);
#endif
#ifdef RLIMIT_NPROC
  setrlimit(RLIMIT_NPROC,&r);
#endif
#ifdef RLIMIT_CORE
  setrlimit(RLIMIT_CORE,&r);
#endif
#endif
}

int main()
{
  long long i;
  long long j;
  long long abovej;
  long long belowj;
  long long checksumcycles;
  long long cyclespersecond;

  cycles[0] = cpucycles();
  cycles[1] = cpucycles();
  cyclespersecond = cpucycles_persecond();

  preallocate();
  limits();

  allocate();
  srandom(getpid());

  cycles[0] = cpucycles();
  test();
  cycles[1] = cpucycles();
  checksumcycles = cycles[1] - cycles[0];

  predoit();
  for (i = 0;i <= TIMINGS;++i) {
    cycles[i] = cpucycles();
  }
  for (i = 0;i <= TIMINGS;++i) {
    cycles[i] = cpucycles();
    doit();
  }
  for (i = 0;i < TIMINGS;++i) cycles[i] = cycles[i + 1] - cycles[i];
  for (j = 0;j < TIMINGS;++j) {
    belowj = 0;
    for (i = 0;i < TIMINGS;++i) if (cycles[i] < cycles[j]) ++belowj;
    abovej = 0;
    for (i = 0;i < TIMINGS;++i) if (cycles[i] > cycles[j]) ++abovej;
    if (belowj * 2 < TIMINGS && abovej * 2 < TIMINGS) break;
  }

  for (i = 0;i < 32;++i) {
    checksum_hex[2 * i] = "0123456789abcdef"[15 & (checksum_state[i] >> 4)];
    checksum_hex[2 * i + 1] = "0123456789abcdef"[15 & checksum_state[i]];
  }
  checksum_hex[2 * i] = 0;

  printword(checksum_hex);
  printnum(cycles[j]);
  printnum(checksumcycles);
  printnum(cyclespersecond);
  printword(primitiveimplementation);
  printf("\n");
  return 0;
}
