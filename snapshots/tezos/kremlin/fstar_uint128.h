#ifndef __KREMLIN_INT128_H
#define __KREMLIN_INT128_H

#include "kremlin/internal/target.h"
#include "kremlin/c_endianness.h"
#include "kremlin/fstar_ints.h"

/******************************************************************************/
/* Machine integers (128-bit arithmetic)                                      */
/******************************************************************************/

/* This header makes KreMLin-generated C code work with:
 * - the default setting where we assume the target compiler define __int128
 * - the setting where we use FStar.UInt128's implementation instead, a.k.a.
 *   "-fnouint128"; in that case, generated C files must be compiled with
 *   -DKRML_NOUINT128, which KreMLin does automatically
 * - a refinement of the case above, wherein all structures are passed by
 *   reference, a.k.a. "-fnostruct-passing", meaning that the KreMLin-generated
 *   must be compiled with -DKRML_NOSTRUCT_PASSING
 */

#ifndef KRML_NOUINT128
typedef unsigned __int128 FStar_UInt128_t, FStar_UInt128_t_, uint128_t,
    FStar_UInt128_uint128;

static inline void print128(const char *where, uint128_t n) {
  KRML_HOST_PRINTF(
      "%s: [%" PRIu64 ",%" PRIu64 "]\n", where, (uint64_t)(n >> 64),
      (uint64_t)n);
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t l = (uint128_t)load64_le(b);
  uint128_t h = (uint128_t)load64_le(b + 8);
  return (h << 64 | l);
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store64_le(b, (uint64_t)n);
  store64_le(b + 8, (uint64_t)(n >> 64));
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t h = (uint128_t)load64_be(b);
  uint128_t l = (uint128_t)load64_be(b + 8);
  return (h << 64 | l);
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_be(b, (uint64_t)(n >> 64));
  store64_be(b + 8, (uint64_t)n);
}

#  define FStar_UInt128_add(x, y) ((x) + (y))
#  define FStar_UInt128_mul(x, y) ((x) * (y))
#  define FStar_UInt128_add_mod(x, y) ((x) + (y))
#  define FStar_UInt128_sub(x, y) ((x) - (y))
#  define FStar_UInt128_sub_mod(x, y) ((x) - (y))
#  define FStar_UInt128_logand(x, y) ((x) & (y))
#  define FStar_UInt128_logor(x, y) ((x) | (y))
#  define FStar_UInt128_logxor(x, y) ((x) ^ (y))
#  define FStar_UInt128_lognot(x) (~(x))
#  define FStar_UInt128_shift_left(x, y) ((x) << (y))
#  define FStar_UInt128_shift_right(x, y) ((x) >> (y))
#  define FStar_UInt128_uint64_to_uint128(x) ((uint128_t)(x))
#  define FStar_UInt128_uint128_to_uint64(x) ((uint64_t)(x))
#  define FStar_UInt128_mul_wide(x, y) ((uint128_t)(x) * (y))
#  define FStar_UInt128_op_Hat_Hat(x, y) ((x) ^ (y))

static inline uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y) {
  uint64_t mask =
      FStar_UInt64_eq_mask((uint64_t)(x >> 64), (uint64_t)(y >> 64)) &
      FStar_UInt64_eq_mask(x, y);
  return ((uint128_t)mask) << 64 | mask;
}

static inline uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y) {
  uint64_t mask =
      (FStar_UInt64_gte_mask(x >> 64, y >> 64) &
       ~(FStar_UInt64_eq_mask(x >> 64, y >> 64))) |
      (FStar_UInt64_eq_mask(x >> 64, y >> 64) & FStar_UInt64_gte_mask(x, y));
  return ((uint128_t)mask) << 64 | mask;
}

static inline uint128_t FStar_Int_Cast_Full_uint64_to_uint128(uint64_t x) {
  return x;
}

static inline uint64_t FStar_Int_Cast_Full_uint128_to_uint64(uint128_t x) {
  return x;
}

#  else /* !defined(KRML_NOUINT128) */

#    ifdef KRML_SEPARATE_UINT128
#      include <FStar_UInt128.h>
#    else
    /* This is a bad circular dependency... should fix it properly. */
#      include "FStar.h"
#    endif

typedef FStar_UInt128_uint128 FStar_UInt128_t_, uint128_t;

/* A series of definitions written using pointers. */
static inline void print128_(const char *where, uint128_t *n) {
  KRML_HOST_PRINTF(
      "%s: [0x%08" PRIx64 ",0x%08" PRIx64 "]\n", where, n->high, n->low);
}

static inline void load128_le_(uint8_t *b, uint128_t *r) {
  r->low = load64_le(b);
  r->high = load64_le(b + 8);
}

static inline void store128_le_(uint8_t *b, uint128_t *n) {
  store64_le(b, n->low);
  store64_le(b + 8, n->high);
}

static inline void load128_be_(uint8_t *b, uint128_t *r) {
  r->high = load64_be(b);
  r->low = load64_be(b + 8);
}

static inline void store128_be_(uint8_t *b, uint128_t *n) {
  store64_be(b, n->high);
  store64_be(b + 8, n->low);
}

static inline void
FStar_Int_Cast_Full_uint64_to_uint128_(uint64_t x, uint128_t *dst) {
  /* C89 */
  dst->low = x;
  dst->high = 0;
}

static inline uint64_t FStar_Int_Cast_Full_uint128_to_uint64_(uint128_t *x) {
  return x->low;
}

#    ifndef KRML_NOSTRUCT_PASSING

static inline void print128(const char *where, uint128_t n) {
  print128_(where, &n);
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t r;
  load128_le_(b, &r);
  return r;
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store128_le_(b, &n);
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t r;
  load128_be_(b, &r);
  return r;
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store128_be_(b, &n);
}

static inline uint128_t FStar_Int_Cast_Full_uint64_to_uint128(uint64_t x) {
  uint128_t dst;
  FStar_Int_Cast_Full_uint64_to_uint128_(x, &dst);
  return dst;
}

static inline uint64_t FStar_Int_Cast_Full_uint128_to_uint64(uint128_t x) {
  return FStar_Int_Cast_Full_uint128_to_uint64_(&x);
}

#    else /* !defined(KRML_STRUCT_PASSING) */

#      define print128 print128_
#      define load128_le load128_le_
#      define store128_le store128_le_
#      define load128_be load128_be_
#      define store128_be store128_be_
#      define FStar_Int_Cast_Full_uint128_to_uint64                            \
        FStar_Int_Cast_Full_uint128_to_uint64_
#      define FStar_Int_Cast_Full_uint64_to_uint128                            \
        FStar_Int_Cast_Full_uint64_to_uint128_

#    endif /* KRML_STRUCT_PASSING */
#  endif   /* KRML_UINT128 */

#endif
