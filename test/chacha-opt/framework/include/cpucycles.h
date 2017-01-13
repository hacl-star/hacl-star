#ifndef CPUCYCLES_H
#define CPUCYCLES_H

#include "asmopt_internal.h"

#if defined(HAVE_INT64)
typedef uint64_t cycles_t;
#elif defined(HAVE_INT32)
typedef uint32_t cycles_t;
#else
typedef unsigned long cycles_t;
#endif

cycles_t LOCAL_PREFIX(cpucycles)(void);
const char *LOCAL_PREFIX(cpucycles_units)(void);

#endif /* CPUCYCLES_H */

