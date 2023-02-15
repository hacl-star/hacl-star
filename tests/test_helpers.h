// This header contains test helpers to avoid ridiculous copy-paste between
// various test files. Keep everything in there static inline.

#pragma once

static inline bool
compare_and_print(size_t len, uint8_t* comp, uint8_t* exp)
{
  printf("computed:");
  for (size_t i = 0; i < len; i++)
    printf("%02x", comp[i]);
  printf("\n");
  printf("expected:");
  for (size_t i = 0; i < len; i++)
    printf("%02x", exp[i]);
  printf("\n");
  bool ok = true;
  for (size_t i = 0; i < len; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok)
    printf("Success!\n");
  else
    printf("**FAILED**\n");
  return ok;
}

static inline bool
compare(size_t len, uint8_t* comp, uint8_t* exp)
{
  bool ok = true;
  for (size_t i = 0; i < len; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok)
    printf("Success!\n");
  else
    printf("**FAILED**\n");
  return ok;
}

// For __ppc_get_timebase - note used for now: see below comment
#if defined(__powerpc64__)
#include <sys/platform/ppc.h>
#endif

typedef uint64_t cycles;

static __inline__ cycles
cpucycles_get(void)
{

#if defined(__x86_64__) || defined(_M_X64)

  uint64_t rax, rdx, aux;
  asm volatile("rdtscp\n" : "=a"(rax), "=d"(rdx), "=c"(aux) : :);
  return (rdx << 32) + rax;

#elif defined(__s390x__)

  uint64_t tsc;
  asm("\tstck\t%0\n" : "=Q"(tsc) : : "cc");
  return (tsc);

#elif defined(__powerpc64__)

  // Computing the CPU cycles for PowerPC is non-trivial.
  // A possibility is to use the __ppc_get_timebase() function. However, this
  // doesn't give the number of cpu cycles, but the current timebase, which
  // is independent from the CPU frequency and is meant to be converted to
  // seconds. It is possible to retrieve the time base increments per
  // cycle by doing something similar to this:
  // https://scm.gforge.inria.fr/anonscm/svn/cfs-signature/trunk/cpucycles-20060326/powerpclinux.c
  // which exploits the fact that the "/proc/cpuinfo" file contains the CPU
  // frequencies (you thus need to count how many time base increments happened
  // in, say, one second).
  // We don't do it for now because it is a bit tricky, we don't really
  // need it for now, and it requires an init() function.
  //
  // If you're interested in computing the number of time base increments
  // per byte, you can uncomment the following line:
  // return __ppc_get_timebase();
  // By then doing [cat /proc/cpuinfo | grep "MHz"], you can retrieve the
  // CPU frequency (one line per logical CPU). With the additional information
  // printed by the benchmarks, you can compute the cycles per processed byte.
  return 0;

#elif defined(__aarch64__) || defined(_M_ARM64) || defined(__arm__) ||         \
  defined(_M_ARM)

  // No implementation for ARM
  return 0;

#else

#error cpucycles_get(): missing implementation

#endif
}

static __inline__ cycles
cpucycles_begin(void)
{
  return cpucycles_get();
}

static __inline__ cycles
cpucycles_end(void)
{
  return cpucycles_get();
}

static inline void
print_time(uint64_t count, clock_t tdiff, uint64_t cdiff)
{
  printf("cycles for %" PRIu64 " bytes: %" PRIu64 " (%.2fcycles/byte)\n",
         count,
         (uint64_t)cdiff,
         (double)cdiff / count);
  printf("time for %" PRIu64 " bytes: %" PRIu64 " (%.2fus/byte)\n",
         count,
         (uint64_t)tdiff,
         (double)tdiff / count);
  printf("bw %8.2f MB/s\n",
         (double)count / (((double)tdiff / CLOCKS_PER_SEC) * 1000000.0));
}
