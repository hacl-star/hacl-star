#ifndef __U128_H
#define __U128_H

#include "kremlib.h"

#if defined(__GNUC__) && defined(__SIZEOF_INT128__) && defined(INT128_NATIVE)
#include "uint128-int128.h"
#define uint128_logand(r,x,y) r = uint128_logand_(x,y)
#define uint128_add(r,x,y) r = uint128_add_(x,y)
#define uint128_add_mod(r,x,y) r = uint128_add_(x,y)
#define uint128_add64(r,x,y) r = uint128_add64_(x,y)
#define uint128_mul_wide(r,x,y) r = uint128_mul_wide_(x,y)
#define uint128_mul_add(r,x,y) r = uint128_mul_add_(r,x,y)
#define uint128_split_high(r,x,y) r = uint128_split_high_(x,y)
#define uint128_split_low(r,x,y) r = uint128_split_low_(x,y)
#define uint128_copy(r,x) r = x
#define load128_64(r,x,y) r = load128_64_(x,y)
#define load128_le(r,x) r = load128_le_(x)
#define store128_le(r,x) store128_le_(r,x)

#elif defined(INT128_STRUCT)
#include "uint128-struct.h"
#define uint128_add(r,x,y) r = uint128_add_(x,y)
#define uint128_add64(r,x,y) r = uint128_add64_(x,y)
#define uint128_mul_wide(r,x,y) r = uint128_mul_wide_(x,y)
#define uint128_split_high(r,x,y) r = uint128_split_high_(x,y)
#define uint128_split_low(r,x,y) r = uint128_split_low_(x,y)
#define uint128_copy(r,x) r = x

#elif defined(INT128_ARRAY)
#include "uint128-array.h"
//#include "uint128-cc.h"

#elif defined(INT128_ARRAY32)
#include "uint128-array32.h"
//#include "uint128-array32x4.h"

#elif defined(INT128_64x2)
#include "uint128-64x2.h"

#endif


#endif
