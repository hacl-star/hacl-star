enum cpuid_flags_arm_t {
	CPUID_ARM       = (1 <<  0),
	CPUID_ARMv6     = (1 <<  1),
	CPUID_ARMv7     = (1 <<  2),
	CPUID_ARMv8     = (1 <<  3),

	CPUID_ASIMD     = (1 << 18),
	CPUID_TLS       = (1 << 19),
	CPUID_AES       = (1 << 20),
	CPUID_PMULL     = (1 << 21),
	CPUID_SHA1      = (1 << 22),
	CPUID_SHA2      = (1 << 23),
	CPUID_CRC32     = (1 << 24),
	CPUID_IWMMXT    = (1 << 25),
	CPUID_IDIVT     = (1 << 26),
	CPUID_IDIVA     = (1 << 27),
	CPUID_VFP3D16   = (1 << 28),
	CPUID_VFP3      = (1 << 29),
	CPUID_VFP4      = (1 << 30),
	CPUID_NEON      = (1 << 31)
};
