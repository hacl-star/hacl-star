#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/sysctl.h>
#include <mach/mach_time.h>
#include "osfreq.c"

#define timebase mach_absolute_time

static int tbmib[2] = { CTL_HW, HW_TB_FREQ } ;

static long myround(double u)
{
  long result = u;
  while (result + 0.5 < u) result += 1;
  while (result - 0.5 > u) result -= 1;
  return result;
}

static long long cpufrequency = 0;
static long tbcycles = 0;

static void init(void)
{
  unsigned int tbfrequency = 0; size_t tbfrequencylen = sizeof(unsigned int);
  cpufrequency = osfreq();
  sysctl(tbmib,2,&tbfrequency,&tbfrequencylen,0,0);
  if (tbfrequency > 0)
    tbcycles = myround(64 * (double) (unsigned long long) cpufrequency
                          / (double) (unsigned long long) tbfrequency);
}

long long cpucycles_apple(void)
{
  if (!cpufrequency) init();
  return (timebase() * tbcycles) >> 6;
}

long long cpucycles_apple_persecond(void)
{
  if (!cpufrequency) init();
  return cpufrequency;
}
