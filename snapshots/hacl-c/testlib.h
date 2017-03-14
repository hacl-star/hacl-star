#ifndef __TESTLIB_H
#define __TESTLIB_H

#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <time.h>
#include <string.h>

// This file has a hand-written .h file so that test files written in C (e.g.
// main-Poly1305.c) can use the functions from this file too (e.g.
// [compare_and_print]).

// Functions for F*-written tests, exposed via TestLib.fsti
void TestLib_touch(int32_t);
void TestLib_check(int32_t, int32_t);

// These functions are also called by HACL
void TestLib_compare_and_print(const char *txt, uint8_t *reference, uint8_t *output, int size);

void *TestLib_unsafe_malloc(size_t size);
void TestLib_print_clock_diff(clock_t t1, clock_t t2);
void TestLib_perr(unsigned int err_code);

#define TestLib_uint8_p_null NULL
#define TestLib_uint32_p_null NULL
#define TestLib_uint64_p_null NULL

typedef uint64_t cycles;

#if defined(__GNUC__) || defined(__clang__)
#if defined(__x86_64__) || defined(__amd64__) || defined(__i386__)
static inline cycles TestLib_cpucycles(void)
{
  uint32_t hi, lo;
  __asm__ __volatile__ ("rdtscp" : "=a"(lo), "=d"(hi) : : "%rcx" );
  return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

static inline cycles TestLib_cpucycles_begin(void)
{
  uint32_t hi, lo;
  __asm__ __volatile__ ("CPUID\n\t"  "RDTSC\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t": "=r" (hi), "=r" (lo):: "%rax", "%rbx", "%rcx", "%rdx");
  return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

static inline cycles TestLib_cpucycles_end(void)
{
  uint32_t hi, lo;
  __asm__ __volatile__ ("RDTSCP\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t" 	"CPUID\n\t": "=r" (hi), "=r" (lo):: 	"%rax", "%rbx", "%rcx", "%rdx");
  return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}
void TestLib_print_cycles_per_round(cycles c1, cycles c2, uint32_t rounds);
#else 
#if defined(__ARM_ARCH)) 
static inline cycles TestLib_cpucycles(void)
{
  uint32_t pmccntr;
  uint32_t pmuseren;
  uint32_t pmcntenset;
  // Read the user mode perf monitor counter access permissions.
  asm volatile("mrc p15, 0, %0, c9, c14, 0" : "=r"(pmuseren));
  if (pmuseren & 1) {  // Allows reading perfmon counters for user mode code.
    asm volatile("mrc p15, 0, %0, c9, c12, 1" : "=r"(pmcntenset));
    if (pmcntenset & 0x80000000ul) {  // Is it counting?
      asm volatile("mrc p15, 0, %0, c9, c13, 0" : "=r"(pmccntr));
      // The counter is set up to count every 64th cycle
      return static_cast<int64_t>(pmccntr) * 64;  // Should optimize to << 6
    }
  }
}

static inline cycles TestLib_cpucycles_begin(void)
{
  return (TestLib_cpucycles());
}

static inline cycles TestLib_cpucycles_end(void)
{
  return (TestLib_cpucycles());
}
#endif
#endif
#else
static inline cycles TestLib_cpucycles(void){ return 0; }
static inline cycles TestLib_cpucycles_begin(void){ return 0; }
static inline cycles TestLib_cpucycles_end(void){ return 0; }
#endif

#endif
