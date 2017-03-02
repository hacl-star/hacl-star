#ifndef __KREMLIB_H
#define __KREMLIB_H

#include <inttypes.h>
#include <stdlib.h>


#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>

#undef force_inline
#ifdef __clang__
#define force_inline inline 
#else
#define force_inline inline __attribute__((always_inline))
#endif

// For types and values from C.fsti that do not exactly have the same name as
// their C counterparts
extern int exit_success;
extern int exit_failure;

typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;


// Endian-ness

#if defined(__linux__) || defined(__CYGWIN__)

#include <endian.h>

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

#elif (defined(_WIN16) || defined(_WIN32) || defined(_WIN64)) && !defined(__WINDOWS__)
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

#define load32(b) (*((uint32_t*)(b)))
#define store32(b,i) (*((uint32_t*)(b))=i)
#define load64(b) (*((uint64_t*)(b)))
#define store64(b,i) (*((uint64_t*)(b))=i)

#define load32_le(b) (le32toh(load32(b)))
#define store32_le(b, i) (store32(b,htole32(i)))
#define load32_be(b) (be32toh(load32(b)))
#define store32_be(b, i) (store32(b,htobe32(i)))

#define load64_le(b) (le64toh(load64(b)))
#define store64_le(b, i) (store64(b,htole64(i)))
#define load64_be(b) (be64toh(load64(b)))
#define store64_be(b, i) (store64(b,htobe64(i)))

// Constant time comparisons
static inline   uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  x = ~(x ^ y);
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int8_t)x >> 7;
}
static inline   uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y) {
  return ~(uint8_t)(((int32_t)x - y) >> 31);
}

static inline   uint16_t FStar_UInt16_eq_mask(uint16_t x, uint16_t y) {
  x = ~(x ^ y);
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int16_t)x >> 15;
}

static inline   uint16_t FStar_UInt16_gte_mask(uint16_t x, uint16_t y) {
  return ~(uint16_t)(((int32_t)x - y) >> 31);
}

static inline   uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y) {
  x = ~(x ^ y);
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int32_t)x) >> 31;
}

static inline   uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y) {
  return ~((uint32_t)(((int64_t)x - y) >> 63));
}

static inline   uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  x = ~(x ^ y);
  x &= x << 32;
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int64_t)x) >> 63;
}

static inline   uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
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
static const uint64_t two51_19 = 2251799813685229;

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
typedef unsigned __int128 FStar_UInt128_t, FStar_UInt128_t_,uint128_t;
static inline void print128(unsigned char* where, uint128_t n) {
  printf("%s: [%llu,%llu]\n",where,(uint64_t)(n>>64),(uint64_t)n);
}

#define htole128(i) i
//(((uint128_t)htole64((uint64_t) i)) << 64 | (uint128_t)htole64((uint64_t) (i >> 64)))
#define le128toh(i) i
//(((uint128_t)le64toh((uint64_t) i)) << 64 | (uint128_t)le64toh((uint64_t) (i >> 64)))
#define htobe128(i) (((uint128_t)htobe64((uint64_t) i)) | ((uint128_t)htobe64((uint64_t)(i >> 64)) << 64))
#define be128toh(i) (((uint128_t)be64toh((uint64_t) i)) | ((uint128_t)be64toh((uint64_t)(i >> 64)) << 64))
#define load128(b) (*((uint128_t *)(b)))
#define store128(b, i) (*((uint128_t *)(b)) = i)
#define load128_le(b) (le128toh(load128(b)))
#define store128_le(b, i) (store128(b,htole128(i)))
#define load128_be(b) (be128toh(load128(b)))
#define store128_be(b, i) (store128(b,htobe128(i)))


#define FStar_UInt128_add(x,y) ((x) + (y))
#define FStar_UInt128_mul(x,y) ((x) * (y))
#define FStar_UInt128_add_mod(x,y) ((x) + (y))
#define FStar_UInt128_sub(x,y) ((x) - (y))
#define FStar_UInt128_sub_mod(x,y) ((x) - (y))
#define FStar_UInt128_logand(x,y) ((x) & (y))
#define FStar_UInt128_logor(x,y) ((x) | (y))
#define FStar_UInt128_logxor(x,y) ((x) ^ (y))
#define FStar_UInt128_lognot(x) (~(x))
#define FStar_UInt128_shift_left(x, y) ((x) << (y))
#define FStar_UInt128_shift_right(x, y) ((x) >> (y))
#define FStar_Int_Cast_uint64_to_uint128(x) ((__int128)(x))
#define FStar_Int_Cast_uint128_to_uint64(x) ((uint64_t)(x))
#define FStar_UInt128_mul_wide(x, y) ((__int128)(x) * (y))

#define FStar_UInt128_op_Hat_Hat(x,y) ((x) ^ (y))

static inline   uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y) {
  uint64_t mask =
      FStar_UInt64_eq_mask((uint64_t)(x >> 64), (uint64_t)(y >> 64)) &
      FStar_UInt64_eq_mask(x, y);
  return ((uint128_t)mask) << 64 | mask;
}

static inline   uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y) {
  uint64_t mask =
      (FStar_UInt64_gte_mask(x >> 64, y >> 64) &
       ~(FStar_UInt64_eq_mask(x >> 64, y >> 64))) |
      (FStar_UInt64_eq_mask(x >> 64, y >> 64) & FStar_UInt64_gte_mask(x, y));
  return ((uint128_t)mask) << 64 | mask;
}

static inline    uint128_t FStar_UInt128_split51(uint128_t* src) {
  uint128_t res = (*src) >> 51;
  *src = (*src) & two51_1;
  return res;
}

static inline   uint128_t FStar_UInt128_mul32(uint64_t x, uint32_t y) {
  return ((uint128_t)x * y);
}

#else

//Not using this anymore because the intrinsics below are better
#define CONSTANT_TIME_CARRY(a, b) \
  ((a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1))
//  (a < b) is faster but may not be constant time
//  better to use intrinsics/assembly

typedef struct {
  uint64_t high;
  uint64_t low;
} FStar_UInt128_t, FStar_UInt128_t_, uint128_t;

static inline void print128(unsigned char* where, uint128_t n) {
  printf("%s: [%llu,%llu]\n",where,n.high,n.low);
}

static inline  uint128_t load128_le(uint8_t* b){
  uint128_t r;
  r.low  = load64_le(b);
  r.high = load64_le(b+8);
  return r;
}

static inline  void store128_le(uint8_t* b, uint128_t n){
  store64_le(b,n.low);
  store64_le(b+8,n.high);
}

static inline  uint128_t load128_be(uint8_t* b){
  uint128_t r;
  r.high  = load64_be(b);
  r.low = load64_be(b+8);
  return r;
}

static inline  void store128_be(uint8_t* b, uint128_t n){
  store64_le(b,n.high);
  store64_le(b+8,n.low);
}


static inline    uint128_t FStar_UInt128_add(uint128_t x, uint128_t y) {
  uint128_t r;
  r.low = x.low + y.low; 
  r.high = x.high + y.high + CONSTANT_TIME_CARRY(r.low, y.low); 
/*    __asm__ __volatile__ (			\ */
/*   "addq %2, %0 \n"				\ */
/*   "adcq %3, %1 \n" : */
/*   "=r"(r.low), "=r"(r.high) :  */
/*   "emr" (y.low), "emr"(y.high),  */
/*   "0" (x.low), "1" (x.high)); */
  return r;
}

static inline    uint128_t FStar_UInt128_add_mod(uint128_t x, uint128_t y) {
  return FStar_UInt128_add(x, y);
}

static inline    uint128_t FStar_UInt128_split51(uint128_t* src) {
  uint128_t x;
  uint128_t y;
  x.low = src->low & two51_1;
  x.high = 0;
  y.low = (uint64_t) (src->low >> 51) & (src->high << 51);
  y.high = src->high >> 51;
  src->low = x.low;
  src->high= x.high;
  return y;
}

static inline    uint128_t FStar_UInt128_sub(uint128_t x, uint128_t y) {
  uint128_t r;
  r.low = x.low - y.low; 
  r.high = x.high - y.high - CONSTANT_TIME_CARRY(x.low, r.low); 
  /*
   __asm__("subq %2, %0; sbbq %3, %1" :
  	  "=r"(r.low), "=r"(r.high) : 
  	  "emr" (y.low), "emr"(y.high), 
  	  "0" (x.low), "1" (x.high));
  */
  return r;
}

static inline    uint128_t FStar_UInt128_sub_mod(uint128_t x, uint128_t y) {
  return FStar_UInt128_sub(x, y);
}

static inline    uint128_t FStar_UInt128_logand(uint128_t x, uint128_t y) {
  uint128_t r;
  r.high = x.high & y.high;
  r.low = x.low & y.low;
  return r;
}

static inline    uint128_t FStar_UInt128_logor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.high = x.high | y.high;
  r.low = x.low | y.low;
  return r;
}

static inline    uint128_t FStar_UInt128_logxor(uint128_t x, uint128_t y) {
  uint128_t r;
  r.high = x.high ^ y.high;
  r.low = x.low ^ y.low;
  return r;
}

static inline    uint128_t FStar_UInt128_lognot(uint128_t x) {
  uint128_t r;
  r.high = ~x.high;
  r.low = ~x.low;
  return r;
}

/* y should not be a secret; y >= 128 should never happen */
static inline   uint128_t FStar_UInt128_shift_left(uint128_t x, FStar_UInt32_t y) {
  uint128_t r;
  if (y < 64) {
    r.high = (x.high << y) | (x.low >> (64-y));
    r.low = x.low << y;
  } else {
    r.high = x.low << (y-64);
    r.low = 0;
  }
  return r;
}
/* y should not be a secret; y >= 128 should never happen */
static inline   uint128_t FStar_UInt128_shift_right(uint128_t x, FStar_UInt32_t y) {
  uint128_t r;
  if (y < 64) {
    r.high = (x.high >> y);
    r.low =  (x.low >> y) | (x.high << (64-y));
  } else {
    r.high = 0;
    r.low = x.high >> (y-64);
  }
  return r;
}

/* Conversions */
static inline   uint128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x) {
  return (uint128_t){.high = UINT64_C(0), .low = x};
}

static inline   uint64_t FStar_Int_Cast_uint128_to_uint64(uint128_t x) { return x.low; }

static inline   uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y) {
  return (uint128_t){.low = FStar_UInt64_eq_mask(x.low, y.low),
      .high = FStar_UInt64_eq_mask(x.high, y.high)};
}

static inline   uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y) {
  uint64_t mask = (FStar_UInt64_gte_mask(x.high, y.high) &
                   ~(FStar_UInt64_eq_mask(x.high, y.high))) |
                  (FStar_UInt64_eq_mask(x.high, y.high) &
                   FStar_UInt64_gte_mask(x.low, y.low));
  return (uint128_t){.high = mask, .low = mask};
}


static inline   uint128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y) {
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
  return (uint128_t){.high = (x * y) + w1 + k, .low = (t << 32) + w3};
}


static inline   uint128_t FStar_UInt128_mul_karatsuba(uint64_t x, uint64_t y) {
  uint64_t x0 = x & 0xffffffff;
  uint64_t x1 = x >> 32;
  uint64_t y0 = y & 0xffffffff;
  uint64_t y1 = y >> 32;
  uint64_t x1y1 = x1 * y1;
  uint64_t x0y0 = x0 * y0;
  uint64_t z1 = ((x1 + x0) * (y1 + y0)) - x0y0 - x1y1;
  uint64_t z1l = z1 << 32;
  uint64_t z1h = z1 >> 32;
  uint64_t rl = z1l + x0y0;
  uint64_t rh = z1h + x1y1 + CONSTANT_TIME_CARRY(rl,z1l);
  return (uint128_t){.high = rh, .low = rl};
}

static inline   uint128_t FStar_UInt128_square_wide(uint64_t x) {
  uint64_t x0 = x & 0xffffffff;
  uint64_t x1 = x >> 32;
  uint64_t x00 = x0 * x0;
  uint64_t x01 = x0 * x1;
  uint64_t x11 = x1 * x1;
  uint64_t x00l = x00 & 0xffffffff;
  uint64_t x00h = x00 >> 32;
  uint64_t x01l = x01 & 0xffffffff;
  uint64_t x01h = x01 >> 31;
  uint64_t lh = (x01l << 1) + x00h;
  uint64_t resl = x00l + (lh << 32);
  uint64_t resh = (lh >> 32) + x11 + x01h;
  return (uint128_t){.high = resh, .low = resl};
}

static inline   uint128_t FStar_UInt128_mul32(uint64_t x, uint32_t y) {
  uint64_t x0 = x & 0xffffffff;
  uint64_t x1 = x >> 32;
  uint64_t x0y = x0 * y;
  uint64_t x0yl = x0y & 0xffffffff;
  uint64_t x0yh = x0y >> 32;
  uint64_t x1y = (x1 * y) + x0yh;
  uint64_t r0 = x0yl + (x1y << 32);
  uint64_t r1 = x1y >> 32;
  return (uint128_t){.high = r1, .low = r0};
}

/* static inline   uint128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y) { */
/*   uint128_t r; */

/*   uint64_t x1 = (uint32_t)x; */
/*   uint64_t y1 = (uint32_t)y; */
/*   uint64_t x2 = x >> 32; */
/*   uint64_t y2 = y >> 32; */

/*   uint64_t x1y1 = x1 * y1; */
/*   uint64_t x1y2 = x1 * y2; */
/*   uint64_t x2y1 = x2 * y1; */
/*   uint64_t x2y2 = x2 * y2; */

/*   uint64_t x1y1_low = (uint32_t) x1y1; */
/*   uint64_t x2y1_low = (uint32_t) x2y1; */
/*   uint64_t x1y2_low = (uint32_t) x1y2; */

/*   uint64_t x1y1_high = x1y1 >> 32; */
/*   uint64_t x2y1_high = x2y1 >> 32; */
/*   uint64_t x1y2_high = x1y2 >> 32; */

/*   uint64_t mid = x1y1_high + x2y1_low + x1y2_low; */
/*   uint64_t mid_low = mid << 32; */
/*   uint64_t mid_high = mid >> 32; */

/*   r.low = mid_low + x1y1_low;  */
/*   r.high = mid_high + x2y1_high + x1y2_high + x2y2; */
/*   return r; */
/* } */

#endif

// 128-bit arithmetic
//uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y);
//uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y);

// Buffers (FIXME remove eqb!)
#define FStar_Buffer_eqb(b1, b2, n) \
  (memcmp((b1), (b2), (n)*sizeof((b1)[0])) == 0)
void FStar_Buffer_recall(void *x);

// Some types that KreMLin has no special knowledge of; many of them appear in
// signatures of ghost functions, meaning that it suffices to give them (any)
// definition.
typedef void *Prims_pos, *Prims_nat, *Prims_nonzero, *FStar_Seq_seq, *Prims_int,
  *Prims_prop, *FStar_HyperStack_mem, *FStar_Set_set, *Prims_st_pre_h, *FStar_Heap_heap,
        *Prims_all_pre_h, *FStar_TSet_set, *Prims_string, *Prims_list,
        *FStar_Map_t,
        *FStar_UInt63_t_, *FStar_Int63_t_,
        *FStar_UInt63_t, *FStar_Int63_t,
        *FStar_UInt_uint_t, *FStar_Int_int_t,
        *FStar_HyperStack_stackref, *FStar_Bytes_bytes,
        *FStar_HyperHeap_rid, *FStar_Heap_aref;

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
#define KRML_EXIT \
  do { \
    printf("Unimplemented function at %s:%d\n", __FILE__, __LINE__); \
    exit(254); \
  } while (0)

#define KRML_EABORT \
  (exit(252), 0)

// Stubs to make ST happy
bool FStar_HyperStack_is_eternal_color(Prims_int x0);
#define FStar_ST_op_Colon_Equals(x, v) KRML_EXIT
#define FStar_ST_op_Bang(x) 0
#define FStar_ST_salloc(x) 0
#define FStar_ST_ralloc(x,y) 0
#define FStar_ST_new_region(x) 0
#define FStar_ST_recall(x) do {} while (0)
#define FStar_ST_recall_region(x) do {} while (0)

#define FStar_Monotonic_RRef_m_recall(...) do {} while (0)
#define FStar_Monotonic_RRef_m_write(...) do {} while (0)
#define FStar_Monotonic_RRef_m_alloc(...) { 0 }

#define FStar_HyperHeap_root 0

// Misc; many of these are polymorphic, hence not extracted (yet) by Kremlin,
// which means that a macro is the "right" way to make they don't generate a
// compilation error.
Prims_int FStar_UInt32_v(uint32_t x);
#define Prims_fst(x) (x).fst
#define Prims_snd(x) (x).snd
#define FStar_Seq_createEmpty(x) 0
#define FStar_Seq_create(len, init) 0
#define FStar_Seq_upd(s, i, e) 0
#define FStar_Seq_eq(l1, l2) 0
FStar_Seq_seq FStar_Seq_append(FStar_Seq_seq x, FStar_Seq_seq y);
FStar_Seq_seq FStar_Seq_slice(FStar_Seq_seq x, FStar_Seq_seq y, Prims_nat z);
#define FStar_SeqProperties_snoc(x, y) 0
#define FStar_SeqProperties_cons(x, y) 0
#define FStar_Seq_index(x, y) 0
FStar_UInt32_t FStar_UInt32_uint_to_t(Prims_nat x);



#define FStar_Buffer_to_seq_full(x) 0

static inline uint32_t rotate32_left (uint32_t x, uint32_t n)
{
  //  assert (n<32);
  return (x<<n) | (x>>(-n&31));
}
static inline uint32_t rotate32_right (uint32_t x, uint32_t n)
{
  //  assert (n<32);
  return (x>>n) | (x<<(-n&31));
}

#endif
