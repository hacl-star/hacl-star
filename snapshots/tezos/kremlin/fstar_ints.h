#ifndef __KREMLIN_INTS_H
#define __KREMLIN_INTS_H

#include <inttypes.h>

/******************************************************************************/
/* Implementation of machine integers                                         */
/******************************************************************************/

/* Integer types */
typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

static inline uint32_t rotate32_left(uint32_t x, uint32_t n) {
  /*  assert (n<32); */
  return (x << n) | (x >> (-n & 31));
}
static inline uint32_t rotate32_right(uint32_t x, uint32_t n) {
  /*  assert (n<32); */
  return (x >> n) | (x << (-n & 31));
}

/* Constant time comparisons */
static inline uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  x = ~(x ^ y);
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int8_t)x >> 7;
}

static inline uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y) {
  return ~(uint8_t)(((int32_t)x - y) >> 31);
}

static inline uint16_t FStar_UInt16_eq_mask(uint16_t x, uint16_t y) {
  x = ~(x ^ y);
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int16_t)x >> 15;
}

static inline uint16_t FStar_UInt16_gte_mask(uint16_t x, uint16_t y) {
  return ~(uint16_t)(((int32_t)x - y) >> 31);
}

static inline uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y) {
  x = ~(x ^ y);
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int32_t)x) >> 31;
}

static inline uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y) {
  return ~((uint32_t)(((int64_t)x - y) >> 63));
}

static inline uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  x = ~(x ^ y);
  x &= x << 32;
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int64_t)x) >> 63;
}

static inline uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  uint64_t low63 = ~((uint64_t)(
      (int64_t)(
          (int64_t)(x & UINT64_C(0x7fffffffffffffff)) -
          (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >>
      63));
  uint64_t high_bit = ~((uint64_t)(
      (int64_t)(
          (int64_t)(x & UINT64_C(0x8000000000000000)) -
          (int64_t)(y & UINT64_C(0x8000000000000000))) >>
      63));
  return low63 & high_bit;
}


#endif
