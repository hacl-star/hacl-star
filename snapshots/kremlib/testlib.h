#ifndef __TESTLIB_H
#define __TESTLIB_H

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

// This file has a hand-written .h file so that test files written in C (e.g.
// main-Poly1305.c) can use the functions from this file too (e.g.
// [compare_and_print]).

// Functions for F*-written tests, exposed via TestLib.fsti
void TestLib_touch(int32_t);
void TestLib_check(int32_t, int32_t);

// These functions are also called by HACL
void TestLib_compare_and_print(const char *txt, uint8_t *reference,
                               uint8_t *output, int size);

void *TestLib_unsafe_malloc(size_t size);
void TestLib_print_clock_diff(clock_t t1, clock_t t2);
void TestLib_perr(unsigned int err_code);

#define TestLib_uint8_p_null NULL
#define TestLib_uint32_p_null NULL
#define TestLib_uint64_p_null NULL

typedef unsigned long long TestLib_cycles, cycles;

#if defined(__COMPCERT__)
static __inline__ TestLib_cycles TestLib_cpucycles(void) {
  return 0;
}

static __inline__ TestLib_cycles TestLib_cpucycles_begin(void)
{
  return 0;
}

static __inline__ TestLib_cycles TestLib_cpucycles_end(void)
{
  return 0;
}

#else

#ifndef _MSC_VER
static __inline__ TestLib_cycles TestLib_cpucycles(void) {
  unsigned hi, lo;
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  return ((unsigned long long)lo) | (((unsigned long long)hi) << 32);
}

static __inline__ TestLib_cycles TestLib_cpucycles_begin(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("CPUID\n\t"  "RDTSC\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t": "=r" (hi), "=r" (lo):: "%rax", "%rbx", "%rcx", "%rdx");
  return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}

static __inline__ TestLib_cycles TestLib_cpucycles_end(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("RDTSCP\n\t"  "mov %%edx, %0\n\t"  "mov %%eax, %1\n\t"  "CPUID\n\t": "=r" (hi), "=r" (lo)::     "%rax", "%rbx", "%rcx", "%rdx");
  return ( (uint64_t)lo)|( ((uint64_t)hi)<<32 );
}
#endif
#endif

void TestLib_print_cycles_per_round(TestLib_cycles c1, TestLib_cycles c2, uint32_t rounds);


#endif
