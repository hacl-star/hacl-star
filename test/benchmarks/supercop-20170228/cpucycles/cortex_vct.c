/*
cpucycles/cortex_vct.c version 20101203
D. J. Bernstein
Romain Dolbeau
Public domain.
*/

#define SCALE 1
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include <stdlib.h>

#if defined(__aarch64__)
static inline unsigned long long aarch64_timer_get_cntfrq(void) {
  unsigned long long val;
  asm volatile("mrs %0, CNTFRQ_EL0" : "=r" (val));
  return val;
}

#define V8FREQ 1
long long cpucycles_cortex_vct(void)
{
  long long Rt;
  asm volatile("mrs %0,  CNTVCT_EL0" : "=r" (Rt));
  return Rt * V8FREQ;
}
long long cpucycles_cortex_vct_persecond(void) {
  struct timeval t0,t1;
  long long c0,c1;
  unsigned long long f;
  long long r;
  double d0,d1;
  gettimeofday(&t0,(struct timezone *) 0);
  c0 = cpucycles_cortex_vct();
  sleep(1);
  gettimeofday(&t1,(struct timezone *) 0);
  c1 = cpucycles_cortex_vct();
  d0 = (double) t0.tv_sec;
  d0 += ((double) t0.tv_usec) / 1000000.0;
  d1 = (double) t1.tv_sec;
  d1 += ((double) t1.tv_usec) / 1000000.0;
  r = (c1-c0)/(d1-d0);
  f = aarch64_timer_get_cntfrq();
  if (llabs(f-r) < 100)
	return f;
  /* something is wrong here, fixme ? */
  return r;
}
#endif
