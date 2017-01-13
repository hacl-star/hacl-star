#if defined(_MSC_VER)

static unsigned long
cpuid_specific_impl(void) {
	unsigned long flags = CPUID_ARM;

	#define CPUID_TEST_FEATURE(feature, value)      \
		if (IsProcessorFeaturePresent(feature)) \
			flags |= (value);

	#if defined(PF_NX_ENABLED)
		CPUID_TEST_FEATURE(PF_NX_ENABLED, CPUID_ARMv6)
	#endif

	#if defined(PF_ARM_V6)
		CPUID_TEST_FEATURE(PF_ARM_V6, CPUID_ARMv6)
	#endif

	#if defined(PF_ARM_V7)
		CPUID_TEST_FEATURE(PF_ARM_V7, CPUID_ARMv7)
	#endif

	#if defined(PF_ARM_DIVIDE_INSTRUCTION_AVAILABLE)
		CPUID_TEST_FEATURE(PF_ARM_DIVIDE_INSTRUCTION_AVAILABLE, CPUID_IDIVT | CPUID_IDIVA)
	#endif

	#if defined(PF_ARM_NEON_INSTRUCTIONS_AVAILABLE)
		CPUID_TEST_FEATURE(PF_ARM_NEON_INSTRUCTIONS_AVAILABLE, CPUID_NEON)
	#endif

	#if defined(PF_ARM_NEON)
		CPUID_TEST_FEATURE(PF_ARM_NEON, CPUID_NEON)
	#endif

	#if defined(PF_ARM_VFP_32_REGISTERS_AVAILABLE)
		CPUID_TEST_FEATURE(PF_ARM_VFP_32_REGISTERS_AVAILABLE, CPUID_VFP3 | CPUID_NEON)
	#endif

	return flags;
}

#endif

