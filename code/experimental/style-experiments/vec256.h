#ifndef __Vec_256_H
#define __Vec_256_H

#include <sys/types.h>
#include <wmmintrin.h>
#include <smmintrin.h>
#include <immintrin.h>

typedef __m256i Lib_Vec256_vec256;


#define Lib_Vec256_vec256_eq64(x0, x1) \
  (_mm256_cmpeq_epi64(x0, x1))

#define Lib_Vec256_vec256_xor(x0, x1) \
  (_mm256_xor_si256(x0, x1))

#define Lib_Vec256_vec256_or(x0, x1) \
  (_mm256_or_si256(x0, x1))

#define Lib_Vec256_vec256_and(x0, x1) \
  (_mm256_and_si256(x0, x1))

#define Lib_Vec256_vec256_lognot(x0) \
  (_mm256_xor_si256(x0, _mm256_set1_epi32(-1)))

#define Lib_Vec256_vec256_shift_left(x0, x1) \
  (_mm256_slli_si256(x0, (x1)/8))

#define Lib_Vec256_vec256_shift_right(x0, x1) \
  (_mm256_srli_si256(x0, (x1)/8))

#define Lib_Vec256_vec256_shift_left64(x0, x1) \
  (_mm256_slli_epi64(x0, x1))

#define Lib_Vec256_vec256_shift_right64(x0, x1) \
  (_mm256_srli_epi64(x0, x1))


#define Lib_Vec256_vec256_shuffle64(x0, x1)	\
  (_mm256_shuffle_epi32(x0, x1))

#define Lib_Vec256_vec256_shuffle64_spec(x0, x1, x2, x3) \
  (_MM_SHUFFLE(x0, x1, x2, x3))

#define Lib_Vec256_vec256_load_le(x0) \
  (_mm256_loadu_si256((__m256i*)(x0)))

#define Lib_Vec256_vec256_store_le(x0, x1) \
  (_mm256_storeu_si256((__m256i*)(x0), x1))

#define Lib_Vec256_vec256_insert32(x0, x1, x2)	\
  (_mm256_insert_epi32(x0, x1, x2))

#define Lib_Vec256_vec256_zero  \
  (_mm256_set1_epi16((uint16_t)0))

#define Lib_Vec256_vec256_add64(x0, x1) \
  (_mm256_add_epi64(x0, x1))

#define Lib_Vec256_vec256_sub64(x0, x1)		\
  (_mm256_sub_epi64(x0, x1))

#define Lib_Vec256_vec256_mul64(x0, x1) \
  (_mm256_mul_epu32(x0, x1))

#define Lib_Vec256_vec256_smul64(x0, x1) \
  (_mm256_mul_epu32(x0, _mm256_set1_epi64x(x1)))

#define Lib_Vec256_vec256_load64(x1) \
  (_mm256_set1_epi64x(x1)) // hi lo

#define Lib_Vec256_vec256_load64s(x1, x2, x3, x4) \
  (_mm256_set_epi64x(x1,x2,x3,x4)) // hi lo

#define Lib_Vec256_vec256_interleave_low64(x1, x2) \
  (_mm256_unpacklo_epi64(x1, x2)) 

#define Lib_Vec256_vec256_interleave_high64(x1, x2) \
  (_mm256_unpackhi_epi64(x1, x2)) 

#define Lib_Vec256_vec256_interleave_low128(x1, x2) \
  (_mm256_permute2x128_si256(x1, x2, 0x20)) 

#define Lib_Vec256_vec256_interleave_high128(x1, x2) \
  (_mm256_permute2x128_si256(x1, x2, 0x31)) 

#define Lib_Vec256_bit_mask64(x) -((x) & 1)


#endif
