#include <stdio.h>
#include <time.h>
#include "cpucycles.h"
#include "cpuid.h"
#include "bench.h"

/* a 32k, 64 byte aligned buffer to bench with */
unsigned char *
bench_get_buffer(void) {
	static unsigned char buffer[0x8000 + 0x40 + 0x40];
	unsigned char *p = buffer;
	p += 0x3f;
	p -= (size_t)p & 0x3f;
	return p;
}

static cycles_t smallest_timeslice = ~(cycles_t)0;
static int have_global_stats = 0;
static cycles_t cycles_per_second = 1;
static size_t global_dummy = 0;

static void
bench_gather_global_stats(void) {
	const char *cpu_units = LOCAL_PREFIX(cpucycles_units)();
	size_t delay = 0;
	size_t dummy = 55;
	clock_t start;
	cycles_t delta;
	size_t j;

	/* find the smallest one and run with that, this isn't an exact science */
	do {
		delta = LOCAL_PREFIX(cpucycles)();
		for (j = 0; j < delay; j++) {
			dummy ^= (dummy << 1) + j;
			dummy += (dummy >> 3);
		}
		delta = LOCAL_PREFIX(cpucycles)() - delta;
		delay++;
	} while (!delta);

	/* run until at least one second has passed AND smallest_timeslice has been set */
	start = clock();
	do {
		delta = LOCAL_PREFIX(cpucycles)();
		for (j = 0; j < delay; j++) {
			dummy ^= (dummy << 1) + j;
			dummy += (dummy >> 3);
		}
		delta = LOCAL_PREFIX(cpucycles)() - delta;

		/* 2 is as good as 1 cycle_t, and should avoid some burps that gettimeofday has with erroneously reporting 1 cycle_t */
		if ((delta > 1) && (delta < smallest_timeslice))
			smallest_timeslice = delta;
	} while (((clock() - start) < CLOCKS_PER_SEC) && (smallest_timeslice == ~(cycles_t)0));

	/* 1/2 of a second back of the hand calculation for cycles_t per second */
	cycles_per_second = LOCAL_PREFIX(cpucycles)();
	start = clock();
	while ((clock() - start) < (CLOCKS_PER_SEC / 2)) {
		dummy ^= (dummy << 1) + 19;
		dummy += (dummy >> 3);
	}
	cycles_per_second = LOCAL_PREFIX(cpucycles)() - cycles_per_second;
	cycles_per_second <<= 1;


	printf("time granularity: %.0f %s, %.0f %s/second\n\n", (double)smallest_timeslice, cpu_units, (double)cycles_per_second, cpu_units);

	global_dummy = dummy & 1;
}

int
bench(const void *impls, size_t impl_size, impl_test test_fn, impl_bench bench_fn, size_t units_count, const char *units_desc) {
	unsigned long cpu_flags = LOCAL_PREFIX(cpuid)();
	const char *cpu_units = LOCAL_PREFIX(cpucycles_units)();
	const unsigned char *p;
	int first_item = 1, err = 0;

	if (!have_global_stats) {
		bench_gather_global_stats();
		have_global_stats = 1;
	}

	/* validate all implementations */
	p = (const unsigned char *)impls;
	for (;;) {
		const cpu_specific_impl_t *impl = (const cpu_specific_impl_t *)p;
		if (impl->cpu_flags == (impl->cpu_flags & cpu_flags)) {
			if (test_fn(impl) != 0) {
				printf("%s: error in implementation!\n", impl->desc);
				err = 1;
			}
		}
		if (impl->cpu_flags == CPUID_GENERIC)
			break;
		p += impl_size;
	}

	if (err)
		return 1;

	p = (const unsigned char *)impls;
	for (;;) {
		const cpu_specific_impl_t *impl = (const cpu_specific_impl_t *)p;

		if (impl->cpu_flags == (impl->cpu_flags & cpu_flags)) {
			cycles_t tbest = ~(cycles_t)0;
			size_t batch_size = 1, trials = 1;
			size_t i;

			/* get a rough estimate for batch size and # of trials */
			for (;;) {
				cycles_t tbest = ~(cycles_t)0;
				size_t i, j;
				for (i = 0; i < 100; i++) {
					cycles_t t1 = LOCAL_PREFIX(cpucycles)();
					for (j = 0; j < batch_size; j++)
						bench_fn(impl);
					t1 = LOCAL_PREFIX(cpucycles)() - t1;
					if (t1 < tbest)
						tbest = t1;
				}
				if (tbest > smallest_timeslice * 25) {
					trials = (cycles_per_second / tbest);
					if (trials < 1)
						trials = 1;
					break;
				}
				batch_size = (batch_size == 1) ? 2 : (((batch_size * 4) / 3)  + 1);
			}

			

			/* measure! */
			for (i = 0; i < trials; i++) {
				cycles_t t1 = LOCAL_PREFIX(cpucycles)();
				size_t j;
				for (j = 0; j < batch_size; j++)
					bench_fn(impl);
				t1 = LOCAL_PREFIX(cpucycles)() - t1;
				if (t1 < tbest)
					tbest = t1;
			}

			if (first_item) {
				printf("%u %s(s):\n", (unsigned int)units_count, units_desc);
				first_item = 0;
			}

			printf("  %12s, %8.2f %s per call, %8.4f %s/%s\n",
				impl->desc, 
				(double)tbest / batch_size, cpu_units,
				((double)tbest / batch_size) / units_count, cpu_units, units_desc
			);
		}

		if (impl->cpu_flags == CPUID_GENERIC)
			return 0;
		p += impl_size;
	}
}
