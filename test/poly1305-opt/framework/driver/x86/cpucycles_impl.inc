typedef cycles_t (*cpucycles_x86_fn)(void);

extern cycles_t LOCAL_PREFIX(cpucycles_x86)(void);
static cycles_t cpucycles_select(void);

static cpucycles_x86_fn cpucycles_impl = cpucycles_select;

#if defined(HAVE_GETTIMEOFDAY)
#include <sys/time.h>

static cycles_t
cpucycles_x86_fallback(void) {
	struct timeval t;
	gettimeofday(&t, NULL);
	return ((cycles_t)t.tv_sec * 1000000) + (cycles_t)t.tv_usec;
}
#else
/* what can a 386/486 use for this otherwise? */
static cycles_t
cpucycles_x86_fallback(void) {
	printf("no suitable timing mechanism found\n");
	exit(1);
}
#endif

static cycles_t
cpucycles_select(void) {
	cpucycles_impl = (LOCAL_PREFIX(cpuid)() & CPUID_RDTSC) ? LOCAL_PREFIX(cpucycles_x86) : cpucycles_x86_fallback;
	return cpucycles_impl();
}

static const char *
cpucycles_units_impl(void) {
	if ((LOCAL_PREFIX(cpuid)() & CPUID_RDTSC))
		return "cycles";
	else
#if defined(HAVE_GETTIMEOFDAY)
		return "us";
#else
		return "";
#endif
}

