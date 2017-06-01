#ifndef __U128_GCC_H
#define __U128_GCC_H

#include "kremlib.h"

typedef unsigned __int128 uint128_t;

static inline uint128_t load128_64_(uint64_t x, uint64_t y) {
  uint128_t r = (((uint128_t) y) << 64) | ((uint128_t)x);
  return r;
}

static inline uint128_t uint128_copy_(uint128_t x) {
  return x;
}

static inline uint128_t load128_le_(uint8_t *b) {
  uint64_t x = load64_le(b);
  uint64_t y = load64_le(b + 8);
  return (load128_64_(x,y));
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  uint64_t x = (uint64_t) n;
  uint64_t y = (uint64_t) (n >> 64);
  store64_le(b, x);
  store64_le(b + 8, y);
}

static inline uint128_t load128_be_(uint8_t *b) {
  uint64_t y = load64_le(b);
  uint64_t x = load64_le(b + 8);
  return (load128_64_(x,y));
}

static inline void store128_be_(uint8_t *b, uint128_t n) {
  uint64_t y = (uint64_t) n;
  uint64_t x = (uint64_t) (n >> 64);
  store64_le(b, x);
  store64_le(b + 8, y);
}


static inline uint128_t uint128_add_(uint128_t x, uint128_t y) {
  return (x + y);
}

static inline uint128_t uint128_add64_(uint128_t x, uint64_t y) {
  return (x + (uint128_t) y);
}

static inline uint128_t uint128_add_mod_(uint128_t x, uint128_t y) {
  return (uint128_add_(x, y));
}

static inline uint128_t uint128_split_low_(uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = (uint64_t) src;
    return ((uint128_t) (src & m));
  } else if (idx < 128) {
    idx = idx - 64;
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = (uint64_t) src;
    uint64_t src1 = (uint64_t) (src >> 64);
    return ((((uint128_t)(src1 & m)) << 64) ^ src0);
  }
}

static inline uint128_t uint128_split_high_(uint128_t src, uint32_t idx) {
    return (src >> idx);
}

static inline uint64_t uint128_split_low64(uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = (uint64_t) src;
    return ((src & m));
  } else if (idx < 128) {
    uint64_t src0 = (uint64_t) src;
    return (src0);
  }
}

static inline uint64_t uint128_split_high64(uint128_t src, uint32_t idx) {
  return ((uint64_t) uint128_split_high_(src,idx));
}

static inline uint128_t uint128_sub_(uint128_t x, uint128_t y) {
  return (x - y);
}

static inline uint128_t uint128_sub_mod_(uint128_t x, uint128_t y) {
  return (uint128_sub_(x, y));
}

static inline uint128_t uint128_logand_(uint128_t x, uint128_t y) {
  return (x & y);
}

static inline uint128_t uint128_logor_(uint128_t x, uint128_t y) {
  return (x | y);
}

static inline uint128_t uint128_logxor_(uint128_t x, uint128_t y) {
  return (x ^ y);
}

static inline uint128_t uint128_lognot_(uint128_t x) {
  return (~x);
}

static inline uint128_t FStar_Int_Cast_uint64_to_uint128_(uint64_t x) {
  return ((uint128_t) x);
}

static inline uint64_t FStar_Int_Cast_uint128_to_uint64(uint128_t x) {
  return ((uint64_t) x);
}

static inline uint128_t uint128_mul_wide_(uint64_t x, uint64_t y) {
  return (((uint128_t)x)*y);
}

#endif
