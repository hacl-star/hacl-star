enum cpuid_flags_x86_t {
	CPUID_X86       = (1 <<  0),
	CPUID_MMX       = (1 <<  1),
	CPUID_SSE       = (1 <<  2),
	CPUID_SSE2      = (1 <<  3),
	CPUID_SSE3      = (1 <<  4),
	CPUID_SSSE3     = (1 <<  5),
	CPUID_SSE4_1    = (1 <<  6),
	CPUID_SSE4_2    = (1 <<  7),
	CPUID_AVX       = (1 <<  8),
	CPUID_XOP       = (1 <<  9),
	CPUID_AVX2      = (1 << 10),
	CPUID_AVX512    = (1 << 11),

	CPUID_RDTSC     = (1 << 25),
	CPUID_RDRAND    = (1 << 26),
	CPUID_POPCNT    = (1 << 27),
	CPUID_FMA4      = (1 << 28),
	CPUID_FMA3      = (1 << 29),
	CPUID_PCLMULQDQ = (1 << 30),
	CPUID_AES       = (1 << 31)
};

