extern uint32_t LOCAL_PREFIX(cpuid_x86)(void);

static uint32_t
cpuid_impl(void) {
	return LOCAL_PREFIX(cpuid_x86)();
}

