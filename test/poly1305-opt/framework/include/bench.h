#ifndef BENCH_H
#define BENCH_H

#include "asmopt_internal.h"
#include "cpuid.h"

typedef void (*impl_bench)(const void *impl);

/* a 32k, 64 byte aligned buffer to bench with */
unsigned char *bench_get_buffer(void);

int bench(const void *impls, size_t impl_size, impl_test test_fn, impl_bench bench_fn, size_t units_count, const char *units_desc);

#endif /* BENCH_H */

