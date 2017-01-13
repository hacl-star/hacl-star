#include "cpuid.h"

#include "cpuid_impl.inc"

static unsigned long cpuid_flags = CPUID_GENERIC;
static unsigned long cpuid_mask = ~(unsigned long)0;

unsigned long
LOCAL_PREFIX(cpuid)(void) {
	if (cpuid_flags == CPUID_GENERIC)
		cpuid_flags = cpuid_impl();
	return cpuid_flags & cpuid_mask;
}

const void *
LOCAL_PREFIX(cpu_select)(const void *impls, size_t impl_size, impl_test test_fn) {
	unsigned long cpu_flags = LOCAL_PREFIX(cpuid)();
	const unsigned char *p = (const unsigned char *)impls;
	for (;;) {
		const cpu_specific_impl_t *impl = (const cpu_specific_impl_t *)p;
		if (impl->cpu_flags == (impl->cpu_flags & cpu_flags)) {
			if (test_fn(impl) == 0)
				return impl;
		}
		if (impl->cpu_flags == CPUID_GENERIC)
			return NULL;
		p += impl_size;
	}
}
