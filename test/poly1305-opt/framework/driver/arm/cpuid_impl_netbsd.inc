#if defined(__NetBSD__)

#include <sys/sysctl.h>

static unsigned long
cpuid_specific_impl(void) {
	unsigned long flags = CPUID_ARM;
	size_t len;
	int flag;

	len = sizeof(flag);
	if (!sysctlbyname("machdep.simdex_present", &flag, &len, NULL, 0) && flag)
		flags |= CPUID_ARMv6;

	len = sizeof(flag);
	if (!sysctlbyname("machdep.neon_present", &flag, &len, NULL, 0) && flag)
		flags |= CPUID_NEON;

	/* should use machdep.cpu_id as well.. */

	return flags;
}

#endif