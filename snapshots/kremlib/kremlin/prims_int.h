#ifndef __KREMLIN__COMPAT_H
#define __KREMLIN__COMPAT_H

#include <inttypes.h>

#include "kremlin/fstar_char.h"

/******************************************************************************/
/* NOT LOW*: implementing Prims.int as runtime checked integers               */
/******************************************************************************/

typedef int32_t Prims_pos, Prims_nat, Prims_nonzero, Prims_int,
    krml_checked_int_t;

static inline FStar_Char_char FStar_Char_char_of_int(krml_checked_int_t x) {
  return x;
}

inline static bool Prims_op_GreaterThanOrEqual(int32_t x, int32_t y) {
  return x >= y;
}

inline static bool Prims_op_LessThanOrEqual(int32_t x, int32_t y) {
  return x <= y;
}

inline static bool Prims_op_GreaterThan(int32_t x, int32_t y) {
  return x > y;
}

inline static bool Prims_op_LessThan(int32_t x, int32_t y) {
  return x < y;
}

#define RETURN_OR(x)                                                           \
  do {                                                                         \
    int64_t __ret = x;                                                         \
    if (__ret < INT32_MIN || INT32_MAX < __ret) {                              \
      KRML_HOST_PRINTF(                                                        \
          "Prims.{int,nat,pos} integer overflow at %s:%d\n", __FILE__,         \
          __LINE__);                                                           \
      KRML_HOST_EXIT(252);                                                     \
    }                                                                          \
    return (int32_t)__ret;                                                     \
  } while (0)

inline static int32_t Prims_pow2(int32_t x) {
  RETURN_OR((int64_t)1 << (int64_t)x);
}

inline static int32_t Prims_op_Multiply(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x * (int64_t)y);
}

inline static int32_t Prims_op_Addition(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x + (int64_t)y);
}

inline static int32_t Prims_op_Subtraction(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x - (int64_t)y);
}

inline static int32_t Prims_op_Division(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x / (int64_t)y);
}

inline static int32_t Prims_op_Modulus(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x % (int64_t)y);
}

inline static uint8_t FStar_UInt8_uint_to_t(krml_checked_int_t x) {
  return x;
}
inline static uint16_t FStar_UInt16_uint_to_t(krml_checked_int_t x) {
  return x;
}
inline static uint32_t FStar_UInt32_uint_to_t(krml_checked_int_t x) {
  return x;
}
inline static uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x) {
  return x;
}

inline static krml_checked_int_t FStar_UInt8_v(uint8_t x) {
  return x;
}
inline static krml_checked_int_t FStar_UInt16_v(uint16_t x) {
  return x;
}
inline static krml_checked_int_t FStar_UInt32_v(uint32_t x) {
  RETURN_OR(x);
}
inline static krml_checked_int_t FStar_UInt64_v(uint64_t x) {
  RETURN_OR(x);
}

inline static krml_checked_int_t FStar_Int32_v(int32_t x) {
  return x;
}
inline static krml_checked_int_t FStar_Int64_v(int64_t x) {
  return x;
}

#endif
