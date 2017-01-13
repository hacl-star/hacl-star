#include <stdlib.h>
#include <stdio.h>
#include "cpuid.h"
#include "cpucycles.h"


#include "cpucycles_impl.inc"

cycles_t
LOCAL_PREFIX(cpucycles)(void) {
	return cpucycles_impl();
}

const char *LOCAL_PREFIX(cpucycles_units)(void) {
	return cpucycles_units_impl();
}

