
#ifndef _HACL_PERFTEST_H_
#define _HACL_PERFTEST_H_

#include <stddef.h>
#include <stdint.h>

#include <string>
#include <iostream>
#include <set>

#define ABORT_BENCHMARK(msg, rv) { printf("\nABORT: %s\n", msg); return rv; }

typedef uint64_t cycles;

extern void b_init();

extern void b_randomize(char *buf, size_t buf_sz);

inline void b_randomize(unsigned char *buf, size_t buf_sz)
{
  b_randomize((char*)buf, buf_sz);
}

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
  protected:
    std::string name;
    unsigned int seed;
    size_t samples;

    static void escape(char c, std::string & str);

  public:
    Benchmark();
    Benchmark(std::string & name);
    virtual ~Benchmark() {}

    void set_seed(unsigned int seed) { this->seed = seed; }
    void set_samples(size_t samples) { this->samples = samples; }

    virtual void run() = 0;
    virtual void b_func() = 0;
    virtual void report(std::ostream & rs) = 0;

    static std::string get_runtime_config();
    static void set_runtime_config(int shaext, int aesni, int pclmulqdq, int avx, int avx2, int bmi2, int adx, int hacl, int vale);
    static std::pair<std::string, std::string> & get_build_config(bool escaped=false);

    void set_name(const std::string & name);
    std::string get_name() const { return name; }
};

extern void b_run(unsigned int seed,
                  size_t samples,
                  const std::string & data_header,
                  const std::string & data_filename,
                  std::set<Benchmark*> & benchmarks);

extern void b_make_plot(unsigned int seed,
                        size_t samples,
                        const std::string & terminal,
                        const std::string & title,
                        const std::string & units,
                        const std::string & data_filename,
                        const std::string & plot_filename,
                        const std::string & plot_extras,
                        const std::string & plot_spec,
                        bool add_key = false);

#endif