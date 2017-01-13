#ifndef CPUID_H
#define CPUID_H

#include "asmopt_internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

enum cpuid_flags_generic_t {
	CPUID_GENERIC = (0)
};

#include "cpuid_flags.inc"

unsigned long LOCAL_PREFIX(cpuid)(void);

/* runtime dispatching based on current cpu */
typedef struct cpu_specific_impl_t {
	unsigned long cpu_flags;
	const char *desc;
	/* additional information, pointers to methods, etc... */
} cpu_specific_impl_t;

typedef int (*impl_test)(const void *impl);

const void *LOCAL_PREFIX(cpu_select)(const void *impls, size_t impl_size, impl_test test_fn);

#if defined(__cplusplus)
}
#endif

#endif /* CPUID_H */
