#include <unistd.h>

#include <benchmark.h>

#include "bench_hash.h"
#include "bench_aead.h"

int main(int argc, char const **argv)
{
  unsigned int seed = 0;
  size_t samples = 20480;

  b_init();

  //EverCrypt_AutoConfig2_disable_vale();

  Benchmark::set_runtime_config(1, 1, 1, 1, 1, 1, 1, 1, 1);

  bench_hash(seed, samples);
  bench_aead(seed, samples);

  return 0;
}