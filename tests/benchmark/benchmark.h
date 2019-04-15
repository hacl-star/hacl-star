
#ifndef _HACL_PERFTEST_H_
#define _HACL_PERFTEST_H_

#include <string>

#include <stddef.h>
#include <stdint.h>

#define ABORT_BENCHMARK(msg, rv) { printf("\nABORT: %s\n", msg); return rv; }

typedef uint64_t cycles;

extern void b_init();

extern void b_randomize(char *buf, size_t buf_sz);

static __inline__ cycles b_cpucycles_begin(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}

static __inline__ cycles b_cpucycles_end(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}

class Benchmark
{
  public:
  std::string name;

  Benchmark() {}
  ~Benchmark() {}

  virtual void run(size_t samples) = 0;
  virtual void b_func() = 0;
};

#endif