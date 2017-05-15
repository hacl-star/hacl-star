#ifndef __KREMLIB_32_H
#define __KREMLIB_32_H

#include <inttypes.h>
#include <stdlib.h>

#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

// Define __cdecl and friends when using GCC, so that we can safely compile code
// that contains __cdecl on all platforms.
#include "gcc_compat.h"

// GCC-specific attribute syntax; everyone else gets the standard C inline
// attribute.
#ifdef __GNU_C__
#ifndef __clang__
#define force_inline inline __attribute__((always_inline))
#else
#define force_inline inline
#endif
#else
#define force_inline inline
#endif

// Uppercase issue; we have to define lowercase version of the C macros (as we
// have no way to refer to an uppercase *variable* in F*).
extern int exit_success;
extern int exit_failure;

void print_string(const char *s);
void print_bytes(uint8_t *b, uint32_t len);

// Buffers (FIXME remove eqb!)
#define FStar_Buffer_eqb(b1, b2, n)                                            \
  (memcmp((b1), (b2), (n) * sizeof((b1)[0])) == 0)
#define FStar_Buffer_to_seq_full(x) 0
void FStar_Buffer_recall(void *x);

// Some types that KreMLin has no special knowledge of; many of them appear in
// signatures of ghost functions, meaning that it suffices to give them (any)
// definition.
typedef void *Prims_pos, *Prims_nat, *Prims_nonzero, *FStar_Seq_Base_seq,
    *Prims_int, *Prims_prop, *FStar_HyperStack_mem, *FStar_Set_set,
    *Prims_st_pre_h, *FStar_Heap_heap, *Prims_all_pre_h, *FStar_TSet_set,
    *Prims_string, *Prims_list, *FStar_Map_t, *FStar_UInt63_t_, *FStar_Int63_t_,
    *FStar_UInt63_t, *FStar_Int63_t, *FStar_UInt_uint_t, *FStar_Int_int_t,
    *FStar_HyperStack_stackref, *FStar_Bytes_bytes, *FStar_HyperHeap_rid,
    *FStar_Heap_aref;

// Prims; all of the functions below abort;
bool Prims_op_GreaterThanOrEqual(Prims_int x, Prims_int y);
bool Prims_op_LessThanOrEqual(Prims_int x, Prims_int y);
bool Prims_op_GreaterThan(Prims_int x, Prims_int y);
bool Prims_op_LessThan(Prims_int x, Prims_int y);
Prims_int Prims_pow2(Prims_int x);
Prims_int Prims_op_Multiply(Prims_int x, Prims_int y);
Prims_int Prims_op_Addition(Prims_int x, Prims_int y);
Prims_int Prims_op_Subtraction(Prims_int x, Prims_int y);
Prims_int Prims_op_Division(Prims_int x, Prims_int y);
Prims_int Prims_op_Modulus(Prims_int x, Prims_int y);
void *Prims_magic(void *_);
void *Prims_admit(void *x);
void *Prims____Cons___tl(void *_);

// In statement position, exiting is easy.
#define KRML_EXIT                                                              \
  do {                                                                         \
    printf("Unimplemented function at %s:%d\n", __FILE__, __LINE__);           \
    exit(254);                                                                 \
  } while (0)

// In expression position, use the comma-operator and a malloc to return an
// expression of the right size. KreMLin passes t as the parameter to the macro.
#define KRML_EABORT(t) (exit(255), *((t*)malloc(sizeof(t))))

#define KRML_CHECK_SIZE(elt, size)                                             \
  if ((size) > INTPTR_MAX / sizeof(elt)) {                                     \
    printf("Maximum allocatable size exceeded, aborting before overflow at "   \
           "%s:%d\n",                                                          \
           __FILE__, __LINE__);                                                \
    exit(253);                                                                 \
  }

// Stubs to make ST happy. Important note: you must generate a use of the macro
// argument, otherwise, you may have FStar_ST_recall(f) as the only use of f;
// KreMLin will think that this is a valid use, but then the C compiler, after
// macro expansion, will error out.
bool FStar_HyperStack_is_eternal_color(Prims_int x0);
#define FStar_ST_op_Colon_Equals(x, v) KRML_EXIT
#define FStar_ST_op_Bang(x) 0
#define FStar_ST_salloc(x) 0
#define FStar_ST_ralloc(x, y) 0
#define FStar_ST_new_region(x) 0
#define FStar_ST_recall(x)                                                     \
  do {                                                                         \
    (void)(x);                                                                 \
  } while (0)
#define FStar_ST_recall_region(x)                                              \
  do {                                                                         \
    (void)(x);                                                                 \
  } while (0)

#define FStar_Monotonic_RRef_m_recall(x1,x2,x3,x4)                             \
  do {                                                                         \
    (void)(x1);                                                                \
    (void)(x2);                                                                \
    (void)(x3);                                                                \
    (void)(x4);                                                                \
  } while (0)
#define FStar_Monotonic_RRef_m_write(x1,x2,x3,x4,x5)                           \
  do {                                                                         \
    (void)(x1);                                                                \
    (void)(x2);                                                                \
    (void)(x3);                                                                \
    (void)(x4);                                                                \
    (void)(x5);                                                                \
  } while (0)
#define FStar_Monotonic_RRef_m_alloc(...)                                      \
  { 0 }

#define FStar_HyperHeap_root 0

// Misc; many of these are polymorphic, hence not extracted (yet) by Kremlin,
// which means that a macro is the "right" way to make sure they don't generate
// a compilation error.
#define Prims_fst(x) (x).fst
#define Prims_snd(x) (x).snd
#define FStar_Seq_Base_createEmpty(x) 0
#define FStar_Seq_Base_create(len, init) 0
#define FStar_Seq_Base_upd(s, i, e) 0
#define FStar_Seq_Base_eq(l1, l2) 0
FStar_Seq_Base_seq FStar_Seq_Base_append(FStar_Seq_Base_seq x,
                                         FStar_Seq_Base_seq y);
FStar_Seq_Base_seq FStar_Seq_Base_slice(FStar_Seq_Base_seq x,
                                        FStar_Seq_Base_seq y, Prims_nat z);
#define FStar_Seq_Properties_snoc(x, y) 0
#define FStar_Seq_Properties_cons(x, y) 0
#define FStar_Seq_Base_index(x, y) 0

// Endian-ness

// ... for Linux
#if defined(__linux__) || defined(__CYGWIN__)
#include <endian.h>

// ... for OSX
#elif defined(__APPLE__)
#include <libkern/OSByteOrder.h>
#define htole64(x) OSSwapHostToLittleInt64(x)
#define le64toh(x) OSSwapLittleToHostInt64(x)
#define htobe64(x) OSSwapHostToBigInt64(x)
#define be64toh(x) OSSwapBigToHostInt64(x)

#define htole16(x) OSSwapHostToLittleInt16(x)
#define le16toh(x) OSSwapLittleToHostInt16(x)
#define htobe16(x) OSSwapHostToBigInt16(x)
#define be16toh(x) OSSwapBigToHostInt16(x)

#define htole32(x) OSSwapHostToLittleInt32(x)
#define le32toh(x) OSSwapLittleToHostInt32(x)
#define htobe32(x) OSSwapHostToBigInt32(x)
#define be32toh(x) OSSwapBigToHostInt32(x)

// ... for Windows
#elif (defined(_WIN16) || defined(_WIN32) || defined(_WIN64)) &&               \
    !defined(__WINDOWS__)
#include <windows.h>

#if BYTE_ORDER == LITTLE_ENDIAN

#if defined(_MSC_VER)
#include <stdlib.h>
#define htobe16(x) _byteswap_ushort(x)
#define htole16(x) (x)
#define be16toh(x) _byteswap_ushort(x)
#define le16toh(x) (x)

#define htobe32(x) _byteswap_ulong(x)
#define htole32(x) (x)
#define be32toh(x) _byteswap_ulong(x)
#define le32toh(x) (x)

#define htobe64(x) _byteswap_uint64(x)
#define htole64(x) (x)
#define be64toh(x) _byteswap_uint64(x)
#define le64toh(x) (x)

#elif defined(__GNUC__) || defined(__clang__)

#define htobe16(x) __builtin_bswap16(x)
#define htole16(x) (x)
#define be16toh(x) __builtin_bswap16(x)
#define le16toh(x) (x)

#define htobe32(x) __builtin_bswap32(x)
#define htole32(x) (x)
#define be32toh(x) __builtin_bswap32(x)
#define le32toh(x) (x)

#define htobe64(x) __builtin_bswap64(x)
#define htole64(x) (x)
#define be64toh(x) __builtin_bswap64(x)
#define le64toh(x) (x)
#endif

#elif BYTE_ORDER == BIG_ENDIAN

/* that would be xbox 360 */
#define htobe16(x) (x)
#define htole16(x) __builtin_bswap16(x)
#define be16toh(x) (x)
#define le16toh(x) __builtin_bswap16(x)

#define htobe32(x) (x)
#define htole32(x) __builtin_bswap32(x)
#define be32toh(x) (x)
#define le32toh(x) __builtin_bswap32(x)

#define htobe64(x) (x)
#define htole64(x) __builtin_bswap64(x)
#define be64toh(x) (x)
#define le64toh(x) __builtin_bswap64(x)

#endif

#endif

// Loads and stores

#define load16(b) (*((uint16_t *)(b)))
#define store16(b, i) (*((uint16_t *)(b)) = i)
#define load32(b) (*((uint32_t *)(b)))
#define store32(b, i) (*((uint32_t *)(b)) = i)
#define load64(b) (*((uint64_t *)(b)))
#define store64(b, i) (*((uint64_t *)(b)) = i)

#define load16_le(b) (le16toh(load16(b)))
#define store16_le(b, i) (store16(b, htole16(i)))
#define load16_be(b) (be16toh(load16(b)))
#define store16_be(b, i) (store16(b, htobe16(i)))

#define load32_le(b) (le32toh(load32(b)))
#define store32_le(b, i) (store32(b, htole32(i)))
#define load32_be(b) (be32toh(load32(b)))
#define store32_be(b, i) (store32(b, htobe32(i)))

#define load64_le(b) (le64toh(load64(b)))
#define store64_le(b, i) (store64(b, htole64(i)))
#define load64_be(b) (be64toh(load64(b)))
#define store64_be(b, i) (store64(b, htobe64(i)))

// Integer types
typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

// Random functions that may show up.
Prims_int FStar_UInt32_v(uint32_t x);
FStar_UInt32_t FStar_UInt32_uint_to_t(Prims_nat x);

static inline uint32_t rotate32_left(uint32_t x, uint32_t n) {
  //  assert (n<32);
  return (x << n) | (x >> (-n & 31));
}
static inline uint32_t rotate32_right(uint32_t x, uint32_t n) {
  //  assert (n<32);
  return (x >> n) | (x << (-n & 31));
}

// Constant time comparisons
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
  uint64_t low63 =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x7fffffffffffffff)) -
                             (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >>
                   63));
  uint64_t high_bit =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x8000000000000000)) -
                             (int64_t)(y & UINT64_C(0x8000000000000000))) >>
                   63));
  return low63 & high_bit;
}

static const uint64_t two51_1 = 2251799813685247;

// Platform-specific 128-bit arithmetic. These are static functions in a header,
// so that each translation unit gets its own copy and the C compiler can
// optimize.

#if defined(__GNUC__) || defined(__clang__)
#include "x86intrin.h"
#endif 

#define inline __attribute__((always_inline))
typedef struct {uint64_t low; uint64_t high;} uint128_t, FStar_UInt128_t;

#define CONSTANT_TIME_CARRY(a, b)                                              \
  ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))

static inline uint128_t load128_64(uint64_t x, uint64_t y) {
  uint128_t r;
  r.low = x;
  r.high = y;
  return r;
}

static inline uint128_t uint128_copy(uint128_t x) {
  uint128_t r;
  r.low = x.low;
  r.high = x.high;
  return r;
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t r;
  r.low = load64_le(b);
  r.high = load64_le(b + 8);
  return r;
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store64_le(b, n.low);
  store64_le(b + 8, n.high);
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t r;
  r.high = load64_le(b);
  r.low = load64_le(b + 8);
  return r;
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_le(b, n.high);
  store64_le(b + 8, n.low);
}

static inline uint128_t uint128_add(uint128_t x, uint128_t y) {
#if 0
  //defined(__GNUC__) || defined(__clang__)
  uint128_t r;
  uint32_t x0 = (uint32_t) x.low;
  uint32_t x1 = (uint32_t) (x.low>>32);
  uint32_t x2 = (uint32_t) (x.high);
  uint32_t x3 = (uint32_t) (x.high>>32);
  uint32_t y0 = (uint32_t) y.low;
  uint32_t y1 = (uint32_t) (y.low>>32);
  uint32_t y2 = (uint32_t) (y.high);
  uint32_t y3 = (uint32_t) (y.high>>32);

  
  /*
  uint32_t r0,r1,r2,r3;
  char c = 0;
  c = _addcarry_u32(c,x0,y0,&r0);
  c = _addcarry_u32(c,x1,y1,&r1);
  c = _addcarry_u32(c,x2,y2,&r2);
  c = _addcarry_u32(c,x3,y3,&r3);
  r.low = (((uint64_t)r1) << 32) ^ r0;
  r.high = (((uint64_t)r3) << 32) ^ r2;
  */
  
  asm("addl %[x0], %[y0]; adcl %[x1], %[y1]; adcl %[x2], %[y2]; adcl %[x3], %[y3];":
       [y0] "=r" (y0),
       [y1] "=r" (y1),
       [y2] "=r" (y2),
       [y3] "=r" (y3) :
       [x0] "r" (x0),
       [x1] "r" (x1),
       [x2] "r" (x2),
       [x3] "r" (x3));
  r.low = (((uint64_t)y1) << 32) ^ y0;
  r.high = (((uint64_t)y3) << 32) ^ y2;
  
  return r;
#else
  uint128_t r;
  uint64_t x0 = x.low;
  r.low = x0 + y.low;
  r.high = x.high + y.high + CONSTANT_TIME_CARRY(r.low,x0);//(r.low < x0);
  return r;
#endif
}

static inline uint128_t uint128_add_mod(uint128_t x, uint128_t y) {
  return uint128_add(x, y);
}


static inline uint128_t uint128_split_low(uint128_t src, uint32_t idx) {
  uint128_t snd;
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src.low;
    snd.low = src0 & m;
    snd.high = 0;
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src.low;
    uint64_t src1 = src.high;
    snd.low = src0;
    snd.high = src1 & m;
  }
  return snd;
}

static inline uint128_t uint128_split_high(uint128_t src, uint32_t idx) {
  uint128_t fst;
  if (idx < 64) {
    uint64_t src0 = src.low;
    uint64_t src1 = src.high;
    fst.low = (src0 >> idx) ^ (src1 << (64-idx));
    fst.high = src1 >> idx;
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t src1 = src.high;
    fst.low = (src1 >> idx);
    fst.high = 0;
  }
  return fst;
}

static inline uint64_t uint128_split_low64(uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t m = (((uint64_t)1) << idx) - 1;
    uint64_t src0 = src.low;
    return (src0 & m);
  } else if (idx < 128) {
    uint64_t src0 = src.low;
    return (src0);
  }
  else return(0);
}

static inline uint64_t uint128_split_high64(uint128_t src, uint32_t idx) {
  if (idx < 64) {
    uint64_t src0 = src.low;
    uint64_t src1 = src.high;
    return ((src0 >> idx) ^ (src1 << (64-idx)));
  } else if (idx < 128) {
    idx = idx-64;
    uint64_t src1 = src.high;
    return (src1 >> idx);
  }
  else return(0);
}

static inline uint128_t uint128_sub(uint128_t x, uint128_t y) {
#if defined(__GNUC__) || defined(__clang__)
  uint128_t r;
  uint32_t x0 = (uint32_t) x.low;
  uint32_t x1 = (uint32_t) (x.low>>32);
  uint32_t x2 = (uint32_t) (x.high);
  uint32_t x3 = (uint32_t) (x.high>>32);
  uint32_t y0 = (uint32_t) y.low;
  uint32_t y1 = (uint32_t) (y.low>>32);
  uint32_t y2 = (uint32_t) (y.high);
  uint32_t y3 = (uint32_t) (y.high>>32);

  /*
  uint32_t r0,r1,r2,r3;
  char c = 0;
  c = _addcarry_u32(c,x0,y0,&r0);
  c = _addcarry_u32(c,x1,y1,&r1);
  c = _addcarry_u32(c,x2,y2,&r2);
  c = _addcarry_u32(c,x3,y3,&r3);
  r.low = (((uint64_t)r1) << 32) ^ r0;
  r.high = (((uint64_t)r3) << 32) ^ r2;
  */
  asm("subl %[x0], %[y0]; sbbl %[x1], %[y1]; sbbl %[x2], %[y2]; sbbl %[x3], %[y3];":
       [y0] "=r" (y0),
       [y1] "=r" (y1),
       [y2] "=r" (y2),
      [y3] "=r" (y3):
       [x0] "r" (x0),
       [x1] "r" (x1),
       [x2] "r" (x2),
      [x3] "r" (x3));
  r.low = (((uint64_t)y1) << 32) + y0;
  r.high = (((uint64_t)y3) << 32) + y2;
  return r;
#else
  uint128_t r;
  uint64_t x0 = x.low;
  r.low = x0 - y.low;
  r.high = x.high - y.high - CONSTANT_TIME_CARRY(x0,r.low);//(x0 < r0);
  return r;
#endif
}


static inline uint128_t uint128_sub_mod(uint128_t x, uint128_t y) {
  return uint128_sub(x, y);
}

static inline uint128_t uint128_logand(uint128_t x, uint128_t y) {
  uint128_t r;
  r.low = x.low & y.low;
  r.high = x.high & y.high;
  return r;
}

static inline uint128_t uint128_logor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.low = x.low | y.low;
  r.high = x.high | y.high;
  return r;
}

static inline uint128_t uint128_logxor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.low = x.low ^ y.low;
  r.high = x.high ^ y.high;
  return r;
}

static inline uint128_t uint128_lognot(uint128_t x) {
  uint128_t r;
  r.low = ~x.low;
  r.high = ~x.high;
  return r;
}

static inline uint128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x) {
  uint128_t r;
  r.low = x;
  r.high = 0;
  return r;
}

static inline uint64_t FStar_Int_Cast_uint128_to_uint64(uint128_t x) {
  return x.low;
}

static inline uint128_t uint128_mul_wide(uint64_t x, uint64_t y) {
  uint64_t u1, v1, t, w3, k, w1, lo, hi;
  u1 = (x & 0xffffffff);
  v1 = (y & 0xffffffff);
  t = (u1 * v1);
  w3 = (t & 0xffffffff);
  k = (t >> 32);
  x >>= 32;
  t = (x * v1) + k;
  k = (t & 0xffffffff);
  w1 = (t >> 32);
  y >>= 32;
  t = (u1 * y) + k;
  k = (t >> 32);
  hi = (x * y) + w1 + k;
  lo = (t << 32) + w3;
  uint128_t r;
  r.low = lo;
  r.high = hi;
  return r;
  
  /*
  uint32_t x0 = (uint32_t) x;
  uint32_t x1 = (uint32_t) (x>>32);
  uint32_t y0 = (uint32_t) y;
  uint32_t y1 = (uint32_t) (y>>32);

  uint64_t x0y0 = x0 * y0;
  uint64_t x0y1 = x0 * y1;
  uint64_t x1y0 = x1 * y0;
  uint64_t x1y1 = x1 * y1;

  uint32_t r0,r1,r2,r3;
  r0 = (uint32_t) x0y0;
  uint32_t r1_0 = x0y0 >> 32;
  uint32_t r1_1 = x0y1;
  uint32_t r1_2 = x1y0;

  uint32_t r2_0 = x1y1; 
  uint32_t r2_1 = x0y1 >> 32;
  uint32_t r2_2 = x1y0 >> 32;

  r3 = x1y1 >> 32;

  char c1 = 0;
  char c2 = 0;
  c1 = _addcarry_u32(0,r1_0,r1_1,&r1);
  c2 = _addcarry_u32(0,r1,r1_2,&r1);
  c1 = _addcarry_u32(c1,r2_0,r2_1,&r2);
  c2 = _addcarry_u32(c2,r2,r2_2,&r2);
  c1 = _addcarry_u32(c1,r3,0,&r3);
  c2 = _addcarry_u32(c2,r3,0,&r3);

  r.low = (((uint64_t)r1) << 32) + r0;
  r.high = (((uint64_t)r3) << 32) + r2;

  */

}

#define FStar_UInt128_add uint128_add
#define FStar_UInt128_add_mod uint128_add_mod
#define FStar_UInt128_sub uint128_sub
#define FStar_UInt128_sub_mod uint128_sub_mod
#define FStar_UInt128_logand uint128_logand
#define FStar_UInt128_logor uint128_logor
#define FStar_UInt128_logxor uint128_logxor
#define FStar_UInt128_lognot uint128_lognot
#define FStar_UInt128_mul_wide uint128_mul_wide
#define FStar_UInt128_split_high uint128_split_high
#define FStar_UInt128_split_low uint128_split_low
#define FStar_UInt128_split_high64 uint128_split_high64
#define FStar_UInt128_split_low64 uint128_split_low64

#endif // __KREMLIB_H
