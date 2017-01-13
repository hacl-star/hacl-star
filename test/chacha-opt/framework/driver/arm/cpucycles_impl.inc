#if defined(HAVE_GETTIMEOFDAY)
#include <sys/time.h>
#endif

static cycles_t
cpucycles_impl(void) {
#if defined(HAVE_GETTIMEOFDAY)
	struct timeval t;
	gettimeofday(&t, NULL);
	return ((cycles_t)t.tv_sec * 1000000) + (cycles_t)t.tv_usec;
#else
	printf("no suitable timing mechanism found\n");
	exit(1);
	return 0;
#endif
}

static const char *
cpucycles_units_impl(void) {
#if defined(HAVE_GETTIMEOFDAY)
	return "us";
#else
	return "";
#endif
}

