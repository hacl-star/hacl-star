#include <stdint.h>
#include "cpucycles.h"

// XXX call also cpuid?
// cf http://www.intel.com/content/www/us/en/embedded/training/ia-32-ia-64-benchmark-code-execution-paper.html
int64_t cpucycles(void) {
  unsigned int hi, lo;

  __asm__ volatile("rdtsc\n\t" : "=a"(lo), "=d"(hi));
  return ((int64_t)lo) | (((int64_t)hi) << 32);
}
