#include "cpuid_impl_linux.inc"
#include "cpuid_impl_msvc.inc"
#include "cpuid_impl_netbsd.inc"


static unsigned long
cpuid_impl(void) {
	unsigned long flags = cpuid_specific_impl();
	if (flags & CPUID_ARMv8)
		flags |= (CPUID_ARMv7 | CPUID_ARMv6);
	if (flags & CPUID_ARMv7)
		flags |= (CPUID_ARMv6);
	if (flags & CPUID_NEON)
		flags |= (CPUID_ARMv7 | CPUID_ARMv6 | CPUID_VFP3);
	/* vfp3d16 is used for both vfp3 & vfp4 */
	if (flags & CPUID_VFP3D16)
		flags &= ~(CPUID_VFP3 | CPUID_VFP4);
	return flags;
}

