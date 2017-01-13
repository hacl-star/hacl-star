#ifndef ASMOPT_INTERNAL_H
#define ASMOPT_INTERNAL_H

#include "asmopt.h"

#define LOCAL_PREFIX3(a,b) a##_##b
#define LOCAL_PREFIX2(a,b) LOCAL_PREFIX3(a,b)
#define LOCAL_PREFIX(n) LOCAL_PREFIX2(PROJECT_NAME,n)
#define PROJECT_NAME chacha

/* yasm */
#if (0)
%define PROJECT_NAME chacha
#endif

#endif /* ASMOPT_INTERNAL_H */
