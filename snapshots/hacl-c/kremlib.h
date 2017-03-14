#ifndef __KREMLIB_H
#define __KREMLIB_H

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

// Note: it's possible to define a statement that always exits cleanly, but
// Kremlin generates calls to KRML_EABORT and it's not possible (as far as I
// know) to define an expression that has a "universal size" and aborts when
// evaluated...
#define KRML_EXIT                                                              \
  do {                                                                         \
    printf("Unimplemented function at %s:%d\n", __FILE__, __LINE__);           \
    exit(254);                                                                 \
  } while (0)

#define KRML_EABORT (exit(252), 0)

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
    (void)x;                                                                   \
  } while (0)
#define FStar_ST_recall_region(x)                                              \
  do {                                                                         \
  } while (0)

#define FStar_Monotonic_RRef_m_recall(...)                                     \
  do {                                                                         \
  } while (0)
#define FStar_Monotonic_RRef_m_write(...)                                      \
  do {                                                                         \
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

#define load32(b) (*((uint32_t *)(b)))
#define store32(b, i) (*((uint32_t *)(b)) = i)
#define load64(b) (*((uint64_t *)(b)))
#define store64(b, i) (*((uint64_t *)(b)) = i)

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
#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
typedef unsigned __int128 FStar_UInt128_t, FStar_UInt128_t_, uint128_t;

static inline void print128(unsigned char *where, uint128_t n) {
  printf("%s: [%" PRIu64 ",%" PRIu64 "]\n", where, (uint64_t)(n >> 64), (uint64_t)n);
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
  uint128_t h = (uint128_t)load64_le(b);
  uint128_t l = (uint128_t)load64_le(b + 8);
  return (h << 64 | l);
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_le(b, (uint64_t)(n >> 64));
  store64_le(b + 8, (uint64_t)n);
}

#define FStar_UInt128_add(x, y) ((x) + (y))
#define FStar_UInt128_mul(x, y) ((x) * (y))
#define FStar_UInt128_add_mod(x, y) ((x) + (y))
#define FStar_UInt128_sub(x, y) ((x) - (y))
#define FStar_UInt128_sub_mod(x, y) ((x) - (y))
#define FStar_UInt128_logand(x, y) ((x) & (y))
#define FStar_UInt128_logor(x, y) ((x) | (y))
#define FStar_UInt128_logxor(x, y) ((x) ^ (y))
#define FStar_UInt128_lognot(x) (~(x))
#define FStar_UInt128_shift_left(x, y) ((x) << (y))
#define FStar_UInt128_shift_right(x, y) ((x) >> (y))
#define FStar_Int_Cast_uint64_to_uint128(x) ((__int128)(x))
#define FStar_Int_Cast_uint128_to_uint64(x) ((uint64_t)(x))
#define FStar_UInt128_mul_wide(x, y) ((__int128)(x) * (y))

#define FStar_UInt128_op_Hat_Hat(x, y) ((x) ^ (y))

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

static inline uint128_t FStar_UInt128_split51(uint128_t *src) {
  uint128_t res = (*src) >> 51;
  *src = (*src) & two51_1;
  return res;
}

static inline uint128_t FStar_UInt128_mul32(uint64_t x, uint32_t y) {
  return ((uint128_t)x * y);
}

#else 

#if defined(__x86_64__) || defined(__amd64__) || defined(__i386__)

typedef struct {
  uint64_t n1;
  uint64_t n0;
} FStar_UInt128_t, FStar_UInt128_t_, uint128_t;

static inline void print128(unsigned char *where, uint128_t n) {
  printf("%s: [%" PRIu64 ",%" PRIu64 "]\n", where, n.n1, n.n0);
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t r;
  r.n0 = load64_le(b);
  r.n1 = load64_le(b + 8);
  return r;
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store64_le(b, n.n0);
  store64_le(b + 8, n.n1);
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t r;
  r.n1 = load64_le(b);
  r.n0 = load64_le(b + 8);
  return r;
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_le(b, n.n1);
  store64_le(b + 8, n.n0);
}

#include <x86intrin.h>
static inline uint128_t FStar_UInt128_add(uint128_t x, uint128_t y) {
  uint128_t r;
  uint32_t r0,r1,r2,r3;
  uint8_t c = 0;
  c = _addcarry_u32(c,(uint32_t)x.n0,(uint32_t)y.n0,&r0);
  c = _addcarry_u32(c,(uint32_t)(x.n0>>32),(uint32_t)(y.n0>>32),&r1);
  c = _addcarry_u32(c,(uint32_t)x.n1,(uint32_t)y.n1,&r2);
  c = _addcarry_u32(c,(uint32_t)(x.n1>>32),(uint32_t)(y.n1>>32),&r3);
  r.n0 = (uint64_t)r0 | (((uint64_t)r1) << 32);
  r.n1 = (uint64_t)r2 | (((uint64_t)r3) << 32);
  return r;
}

static inline uint128_t FStar_UInt128_add_mod(uint128_t x, uint128_t y) {
  return FStar_UInt128_add(x, y);
}

static inline uint128_t FStar_UInt128_split51(uint128_t *src) {
  uint128_t x;
  uint128_t y;
  x.n0 = (src->n0) & 0x7ffffffffffff;
  x.n1 = 0;
  y.n0 = ((src->n0) >> 51) ^ ((src->n1) << 13);
  y.n1 = (src->n1) >> 51;
  *src = x;
  return y;
}

static inline uint128_t FStar_UInt128_split42(uint128_t *src) {
  uint128_t x;
  uint128_t y;
  x.n0 = src->n0 & 0x3ffffffffff;
  x.n1 = 0;
  y.n0 = ((src->n0) >> 42) ^ ((src->n1) << 22);
  y.n1 = ((src->n1) >> 42);
  *src = x;
  return y;
}

static inline uint128_t FStar_UInt128_split44(uint128_t *src) {
  uint128_t x;
  uint128_t y;
  x.n0 = src->n0 & 0xfffffffffff;
  x.n1 = 0;
  y.n0 = ((src->n0) >> 44) ^ ((src->n1)<<20);
  y.n1 = ((src->n1) >> 44);
  *src = x;
  return y;
}


static inline uint128_t FStar_UInt128_sub(uint128_t x, uint128_t y) {
  uint128_t r;
  uint32_t r0,r1,r2,r3;
  uint8_t c = 0;
  c = _subborrow_u32(c,(uint32_t)x.n0,(uint32_t)y.n0,&r0);
  c = _subborrow_u32(c,(uint32_t)(x.n0>>32),(uint32_t)(y.n0>>32),&r1);
  c = _subborrow_u32(c,(uint32_t)x.n1,(uint32_t)y.n1,&r2);
  c = _subborrow_u32(c,(uint32_t)(x.n1>>32),(uint32_t)(y.n1>>32),&r3);
  r.n0 = (uint64_t)r0 | (((uint64_t)r1) << 32);
  r.n1 = (uint64_t)r2 | (((uint64_t)r3) << 32);
  return r;
}

static inline uint128_t FStar_UInt128_sub_mod(uint128_t x, uint128_t y) {
  return FStar_UInt128_sub(x, y);
}

static inline uint128_t FStar_UInt128_logand(uint128_t x, uint128_t y) {
  uint128_t r;
  r.n0 = x.n0 & y.n0;
  r.n1 = x.n1 & y.n1;
  return r;
}

static inline uint128_t FStar_UInt128_logor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.n0 = x.n0 | y.n0;
  r.n1 = x.n1 | y.n1;
  return r;
}

static inline uint128_t FStar_UInt128_logxor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.n0 = x.n0 ^ y.n0;
  r.n1 = x.n1 ^ y.n1;
  return r;
}

static inline uint128_t FStar_UInt128_lognot(uint128_t x) {
  uint128_t r;
  r.n0 = ~x.n0;
  r.n1 = ~x.n1;
  return r;
}

static inline uint128_t FStar_UInt128_shift_left(uint128_t x, uint32_t n) {
  uint128_t r;
  if (n == 64) {
    r.n0 = 0;
    r.n1 = x.n0;
  } else if (n < 64) {
    r.n0 = x.n0 << n;
    r.n1 = (x.n1 << n) | (x.n0 >> (64-n));
  }
  else {
    n = n - 64;
    r.n0 = 0;
    r.n1 = (x.n0 << n);
  }
  return r;
}

static inline uint128_t FStar_UInt128_shift_right(uint128_t x, uint32_t n) {
  uint128_t r;
  if (n == 64) {
    r.n1 = 0;
    r.n0 = x.n1;
  } else if (n < 64) {
    r.n1 = x.n1 >> n;
    r.n0 = (x.n0 >> n) | (x.n1 << (64-n));
  }
  else {
    n = n - 64;
    r.n1 = 0;
    r.n0 = (x.n1 >> n);
  }
  return r;
}

/* Conversions */
static inline uint128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x) {
  return (uint128_t){.n1 = 0, .n0 = x};
}

static inline uint128_t FStar_Int_Cast_uint64x2_to_uint128(uint64_t x,uint64_t y) {
  return (uint128_t){.n1 = y, .n0 = x};
}

static inline uint64_t FStar_Int_Cast_uint128_to_uint64(uint128_t x) {
  return (x.n0);
}

static inline uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y) {
  uint32_t mask = 
    FStar_UInt64_eq_mask(x.n1, y.n1) &
    FStar_UInt64_eq_mask(x.n0, y.n0);
  return (uint128_t) {.n1 = mask,.n0 = mask};
}

static inline uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y) {
  uint32_t mask = 
    (FStar_UInt64_gte_mask(x.n1, y.n1) & ~(FStar_UInt64_eq_mask(x.n1, y.n1))) |
    (FStar_UInt32_eq_mask(x.n1, y.n1) & FStar_UInt32_gte_mask(x.n0, y.n0));
  return (uint128_t) {.n1 = mask,.n0 = mask};
}

static inline uint128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y) {
  uint64_t u1, v1, t, w3, k, w1;
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
  return (uint128_t){.n1 = (x * y) + w1 + k, .n0 = (t << 32) + w3};
}

static inline uint128_t FStar_UInt128_mul_wide_new(uint64_t x, uint64_t y) {
  uint32_t x0 = (uint32_t)x;
  uint32_t x1 = x >> 32;
  uint32_t y0 = (uint32_t)y;
  uint32_t y1 = y >> 32;
  uint64_t x0y0 = ((uint64_t)x0) * ((uint64_t)y0);
  uint64_t x0y1 = ((uint64_t)x0) * ((uint64_t)y1);
  uint64_t x1y0 = ((uint64_t)x1) * ((uint64_t)y0);
  uint64_t x1y1 = ((uint64_t)x1) * ((uint64_t)y1);
  uint64_t rm = (x0y0 >> 32) + ((uint32_t) x0y1) + ((uint32_t) x1y0);
  uint64_t r0 = (uint32_t)x0y0 | (rm << 32);
  uint64_t r1 = (rm >> 32) + x1y1 + (x0y1 >> 32) + (x1y0 >> 32);
  return (uint128_t){.n1 = r1, .n0 = r0};
}

static inline uint128_t FStar_UInt128_mul32(uint64_t x, uint32_t y) {
  uint32_t x0 = (uint32_t) x;
  uint32_t x1 = (uint32_t) (x >> 32);
  uint64_t x0y = ((uint64_t)x0) * ((uint64_t)y);
  uint32_t x0yl = (uint32_t)x0y;
  uint32_t x0yh = (uint32_t)(x0y >> 32);
  uint64_t x1y = (((uint64_t)x1) * ((uint64_t)y)) + x0yh;
  uint64_t r0 = (uint64_t)x0yl ^ (x1y << 32);
  uint32_t r1 = (uint32_t) (x1y >> 32);
  return (uint128_t){.n1 = r1, .n0 = (uint64_t) r0};
}

#else //using 32-bits here
#if defined(__ARM_ARCH) 

typedef struct {
  uint32_t n3;
  uint32_t n2;
  uint32_t n1;
  uint32_t n0;
} FStar_UInt128_t, FStar_UInt128_t_, uint128_t;

static inline void print128(unsigned char *where, uint128_t n) {
  printf("%s: [%" PRIu32 ",%" PRIu32 ",%" PRIu32 ",%" PRIu32 "]\n", where, n.n3, n.n2, n.n1, n.n0);
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t r;
  r.n0 = load32_le(b);
  r.n1 = load32_le(b + 4);
  r.n2 = load32_le(b + 8);
  r.n3 = load32_le(b + 12);
  return r;
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store64_le(b, n.n0);
  store64_le(b + 4, n.n1);
  store64_le(b + 8, n.n2);
  store64_le(b + 12, n.n3);
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t r;
  r.n3 = load32_le(b);
  r.n2 = load32_le(b + 4);
  r.n1 = load32_le(b + 8);
  r.n0 = load32_le(b + 12);
  return r;
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_le(b, n.n3);
  store64_le(b + 4, n.n2);
  store64_le(b + 8, n.n1);
  store64_le(b + 12, n.n0);
}

static inline uint128_t FStar_UInt128_add(uint128_t x, uint128_t y) {
  uint128_t r;
  asm ("add %[r0], %[x0], %[y0]"
       "adc %[r1], %[x1], %[y1]"
       "adc %[r2], %[x2], %[y2]"
       "adc %[r3], %[x3], %[y3]"
       : [r0] "=r" (r.n0), [r1] "=r" (r.n1), [r2] "=r" (r.n2), [r3] "=r" (r.n3) 
       : [x0] "r" (x.n0), [x1] "r" (x.n1), [x2] "r" (r.n2), [x3] "=r" (x.n3), 
       [y0] "r" (y.n0), [y1] "r" (y.n1), [y2] "r" (r.n2), [y3] "=r" (y.n3));
  return r;
}

static inline uint128_t FStar_UInt128_add_mod(uint128_t x, uint128_t y) {
  return FStar_UInt128_add(x, y);
}

static inline uint128_t FStar_UInt128_split51(uint128_t *src) {
  uint128_t x;
  uint128_t y;
  x.n0 = src->n0;
  x.n1 = (src->n1) & 0x7ffff;
  x.n2 = x.n3 = 0;
  y.n0 = ((src->n1) >> 19) ^ ((src->n2) << 13);
  y.n1 = ((src->n2) >> 19) ^ ((src->n3) << 13);
  y.n2 = (src->n3) >> 19;
  *src = x;
  return y;
}

static inline uint128_t FStar_UInt128_split42(uint128_t *src) {
  uint128_t x;
  uint128_t y;
  x.n0 = src->n0;
  x.n1 = (src->n1) & 0x3ff;
  x.n2 = x.n3 = 0;
  y.n0 = ((src->n1) >> 10) ^ ((src->n2) << 22);
  y.n1 = ((src->n2) >> 10) ^ ((src->n3) << 22);
  y.n2 = (src->n3) >> 10;
  y.n3 = 0;
  *src = x;
  return y;
}

static inline uint128_t FStar_UInt128_split44(uint128_t *src) {
  uint128_t x;
  uint128_t y;
  x.n0 = src->n0;
  x.n1 = (src->n1) & 0xfff;
  x.n2 = x.n3 = 0;
  y.n0 = ((src->n1) >> 12) ^ ((src->n2) << 20);
  y.n1 = ((src->n2) >> 12) ^ ((src->n3) << 20);
  y.n2 = (src->n3) >> 12;
  y.n3 = 0;
  *src = x;
  return y;
}


static inline uint128_t FStar_UInt128_sub(uint128_t x, uint128_t y) {
  uint128_t r;
  asm ("sub %[o], %[i1], %[i2]": [o] "=r" (r.n0) : [i1] "r" (x.n0), [i2] "r" (y.n0));
  asm ("sbb %[o], %[i1], %[i2]": [o] "=r" (r.n1) : [i1] "r" (x.n1), [i2] "r" (y.n1));
  asm ("sbb %[o], %[i1], %[i2]": [o] "=r" (r.n2) : [i1] "r" (x.n2), [i2] "r" (y.n2));
  asm ("sbb %[o], %[i1], %[i2]": [o] "=r" (r.n3) : [i1] "r" (x.n3), [i2] "r" (y.n3));
  return r;
}

static inline uint128_t FStar_UInt128_sub_mod(uint128_t x, uint128_t y) {
  return FStar_UInt128_sub(x, y);
}

static inline uint128_t FStar_UInt128_logand(uint128_t x, uint128_t y) {
  uint128_t r;
  r.n0 = x.n0 & y.n0;
  r.n1 = x.n1 & y.n1;
  r.n2 = x.n2 & y.n2;
  r.n3 = x.n3 & y.n3;
  return r;
}

static inline uint128_t FStar_UInt128_logor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.n0 = x.n0 | y.n0;
  r.n1 = x.n1 | y.n1;
  r.n2 = x.n2 | y.n2;
  r.n3 = x.n3 | y.n3;
  return r;
}

static inline uint128_t FStar_UInt128_logxor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.n0 = x.n0 ^ y.n0;
  r.n1 = x.n1 ^ y.n1;
  r.n2 = x.n2 ^ y.n2;
  r.n3 = x.n3 ^ y.n3;
  return r;
}

static inline uint128_t FStar_UInt128_lognot(uint128_t x) {
  uint128_t r;
  r.n0 = ~x.n0;
  r.n1 = ~x.n1;
  r.n2 = ~x.n2;
  r.n3 = ~x.n3;
  return r;
}

static inline uint128_t FStar_UInt128_shift_left(uint128_t x, uint32_t n) {
  uint128_t r;
  if (n == 64) {
    r.n0 = 0;
    r.n1 = 0;
    r.n2 = x.n0;
    r.n3 = x.n1;
  } else if (n < 32) {
    r.n0 = x.n0 << n;
    r.n1 = (x.n1 << n) | (x.n0 >> (32-n));
    r.n2 = (x.n2 << n) | (x.n1 >> (32-n));
    r.n3 = (x.n3 << n) | (x.n2 >> (32-n));
  }
  else if (n < 64) {
    n = n - 32;
    r.n0 = 0;
    r.n1 = (x.n0 << n);
    r.n2 = (x.n1 << n) | (x.n0 >> (32-n));
    r.n3 = (x.n2 << n) | (x.n1 >> (32-n));
  }
  else if (n < 96) {
    n = n - 64;
    r.n0 = 0;
    r.n1 = 0;
    r.n2 = (x.n0 << n);
    r.n3 = (x.n1 << n) | (x.n0 >> (32-n));
  }
  else {
    n = n - 96;
    r.n0 = 0;
    r.n1 = 0;
    r.n2 = 0;
    r.n3 = (x.n0 << n);
  }
  return r;
}

static inline uint128_t FStar_UInt128_shift_right(uint128_t x, uint32_t n) {
  uint128_t r;
  if (n == 64) {
    r.n3 = 0;
    r.n2 = 0;
    r.n1 = x.n3;
    r.n0 = x.n2;
  } else if (n < 32) {
    r.n3 = x.n3 << n;
    r.n2 = (x.n2 >> n) | (x.n3 << (32-n));
    r.n1 = (x.n1 >> n) | (x.n2 << (32-n));
    r.n0 = (x.n0 >> n) | (x.n1 << (32-n));
  }
  else if (n < 64) {
    n = n - 32;
    r.n3 = 0;
    r.n2 = (x.n3 >> n);
    r.n1 = (x.n2 >> n) | (x.n3 << (32-n));
    r.n0 = (x.n1 >> n) | (x.n2 << (32-n));
  }
  else if (n < 96) {
    n = n - 64;
    r.n3 = 0;
    r.n2 = 0;
    r.n1 = (x.n3 >> n);
    r.n0 = (x.n2 >> n) | (x.n3 << (32-n));
  }
  else {
    n = n - 96;
    r.n3 = 0;
    r.n2 = 0;
    r.n1 = 0;
    r.n0 = (x.n3 >> n);
  }
  return r;
}

/* Conversions */
static inline uint128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x) {
  return (uint128_t){.n3 = 0, .n2 = 0, .n1 = x >> 32, .n0 = (uint32_t) x};
}

static inline uint128_t FStar_Int_Cast_uint64x2_to_uint128(uint64_t x,uint64_t y) {
  return (uint128_t){.n3 = y>>32, .n2 = (uint32_t)y, .n1 = x >> 32, .n0 = (uint32_t) x};
}

static inline uint64_t FStar_Int_Cast_uint128_to_uint64(uint128_t x) {
  return ((uint64_t)x.n1) << 32 ^ ((uint64_t)x.n0);
}

static inline uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y) {
  uint32_t mask = 
    FStar_UInt32_eq_mask(x.n3, y.n3) &
    FStar_UInt32_eq_mask(x.n2, y.n2)&
    FStar_UInt32_eq_mask(x.n1, y.n1) &
    FStar_UInt32_eq_mask(x.n0, y.n0);
  return (uint128_t) {.n3 = mask,.n2 = mask,.n1 = mask,.n0 = mask};
}

static inline uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y) {
  uint32_t mask = 
    (FStar_UInt32_gte_mask(x.n3, y.n3) & ~(FStar_UInt32_eq_mask(x.n3, y.n3))) |
    (FStar_UInt32_eq_mask(x.n3, y.n3) & FStar_UInt32_gte_mask(x.n2, y.n2) & ~(FStar_UInt32_eq_mask(x.n2, y.n2))) |
    (FStar_UInt32_eq_mask(x.n3, y.n3) & FStar_UInt32_eq_mask(x.n2, y.n2) & FStar_UInt32_gte_mask(x.n1, y.n1) & ~(FStar_UInt32_eq_mask(x.n1, y.n1))) |
    (FStar_UInt32_eq_mask(x.n3, y.n3) & FStar_UInt32_eq_mask(x.n2, y.n2) & FStar_UInt32_eq_mask(x.n1, y.n1) & FStar_UInt32_gte_mask(x.n0, y.n0));
  return (uint128_t) {.n3 = mask,.n2 = mask,.n1 = mask,.n0 = mask};
}

static inline uint128_t FStar_UInt128_mul_wide_new(uint64_t x, uint64_t y) {
  uint32_t x0 = (uint32_t)x;
  uint32_t x1 = x >> 32;
  uint32_t y0 = (uint32_t)y;
  uint32_t y1 = y >> 32;
  uint64_t x0y0 = ((uint64_t)x0) * ((uint64_t)y0);
  uint64_t x0y1 = ((uint64_t)x0) * ((uint64_t)y1);
  uint64_t x1y0 = ((uint64_t)x1) * ((uint64_t)y0);
  uint64_t x1y1 = ((uint64_t)x1) * ((uint64_t)y1);
  uint32_t r0 = (uint32_t)x0y0;
  uint64_t r1d = (x0y0 >> 32) + ((uint32_t) x0y1) + ((uint32_t) x1y0);
  uint32_t r1 = (uint32_t) r1d;
  uint64_t r2d = (r1d >> 32) + ((uint32_t) x1y1) + (x0y1 >> 32) + (x1y0 >> 32);
  uint32_t r2 = (uint32_t) r2d;
  uint32_t r3 = (x1y1 >> 32) + (r2d >> 32);
  return (uint128_t){.n3 = r3, .n2 = r2, .n1 = r1, .n0 = r0};
}

static inline uint128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y) {
  uint32_t u1 = (uint32_t)x;
  uint32_t v1 = (uint32_t)y;
  uint64_t t = ((uint64_t)u1) * ((uint64_t)v1);
  uint32_t w3 = (uint32_t)t;
  uint32_t k = (uint32_t) (t >> 32);
  uint32_t xx = x >> 32;
  t = (((uint64_t)xx) * ((uint64_t)v1)) + k;
  k = (uint32_t) t;
  uint32_t w1 = (uint32_t) (t >> 32);
  uint32_t yy = (uint32_t) (y >> 32);
  t = (((uint64_t)u1) * ((uint64_t)yy)) + k;
  k = (uint32_t) (t >> 32);
  uint64_t h = (((uint64_t)xx) * ((uint64_t)yy)) + w1 + k;
  uint64_t l = (t << 32) + w3;
  return (uint128_t){.n3 = h >> 32, .n2 = (uint32_t) h, .n1 = l >> 32, .n0 = (uint32_t) l};
}

static inline uint128_t FStar_UInt128_mul32(uint64_t x, uint32_t y) {
  uint32_t x0 = (uint32_t) x;
  uint32_t x1 = (uint32_t) (x >> 32);
  uint64_t x0y = ((uint64_t)x0) * ((uint64_t)y);
  uint32_t x0yl = (uint32_t)x0y;
  uint32_t x0yh = (uint32_t)(x0y >> 32);
  uint64_t x1y = (((uint64_t)x1) * ((uint64_t)y)) + x0yh;
  uint64_t r0 = (uint64_t)x0yl ^ (x1y << 32);
  uint32_t r1 = (uint32_t) (x1y >> 32);
  return (uint128_t){.n3 = 0, .n2 = r1, .n1 = (uint32_t)(r0 >> 32), .n0 = (uint32_t)r0};
}

#endif
#endif
#endif

#endif // __KREMLIB_H
