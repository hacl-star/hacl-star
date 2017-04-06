#ifndef __U128_H
#define __U128_H

#include "kremlib.h"

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
#include "uint128-gcc.h"
#define uint128_add(r,x,y) r = uint128_add_(x,y)
#define uint128_add64(r,x,y) r = uint128_add64_(x,y)
#define uint128_mul_wide(r,x,y) r = uint128_mul_wide_(x,y)
#define uint128_split_high(r,x,y) r = uint128_split_high_(x,y)
#define uint128_split_low(r,x,y) r = uint128_split_low_(x,y)
#define uint128_copy(r,x) r = x

#else 
#include "uint128-cc.h"
#endif


#endif
