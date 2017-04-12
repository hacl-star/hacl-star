#ifndef __Vec32xN_H
#define __Vec32xN_H

#ifdef __AVX2__
#include "vec256.h"
#else
#ifdef __SSSE3__
#include "vec128.h"
#else
#include "vec_buf.h"
#endif
#endif
#endif
