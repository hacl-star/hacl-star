#include "libkremlin.h"

typedef unsigned __int128 uint128;


inline uint64_t uint128_mul_wide_int(uint64_t* lo, uint64_t x, uint64_t y) {
  uint128 m = (uint128)(x) * y;
  *lo = (uint64_t) m;
  return ((uint64_t) (m >> 64)); 
}
