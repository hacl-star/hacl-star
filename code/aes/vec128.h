#ifndef __Vec_H
#define __Vec_H

#include <sys/types.h>
#include <wmmintrin.h>
#include <smmintrin.h>

typedef __m128i Lib_Vec128_vec128;

#define Lib_Vec128_ni_aes_enc(x0, x1) \
  (_mm_aesenc_si128(x0, x1))

#define Lib_Vec128_ni_aes_enc_last(x0, x1) \
  (_mm_aesenclast_si128(x0, x1))

#define Lib_Vec128_ni_aes_keygen_assist(x0, x1) \
  (_mm_aeskeygenassist_si128(x0, x1))

#define Lib_Vec128_ni_clmul(x0, x1, x2)		\
  (_mm_clmulepi64_si128(x0, x1, x2))


#define Lib_Vec128_vec128_xor(x0, x1) \
  (_mm_xor_si128(x0, x1))

#define Lib_Vec128_vec128_eq64(x0, x1) \
  (_mm_cmpeq_epi64(x0, x1))

#define Lib_Vec128_vec128_or(x0, x1) \
  (_mm_or_si128(x0, x1))

#define Lib_Vec128_vec128_and(x0, x1) \
  (_mm_and_si128(x0, x1))

#define Lib_Vec128_vec128_lognot(x0) \
  (_mm_xor_si128(x0, _mm_set1_epi32(-1)))

#define Lib_Vec128_vec128_shift_left(x0, x1) \
  (_mm_slli_si128(x0, (x1)/8))

#define Lib_Vec128_vec128_shift_right(x0, x1) \
  (_mm_srli_si128(x0, (x1)/8))

#define Lib_Vec128_vec128_shift_left64(x0, x1) \
  (_mm_slli_epi64(x0, x1))

#define Lib_Vec128_vec128_shift_right64(x0, x1) \
  (_mm_srli_epi64(x0, x1))


#define Lib_Vec128_vec128_shuffle32(x0, x1)	\
  (_mm_shuffle_epi32(x0, x1))

#define Lib_Vec128_vec128_shuffle32_spec(x0, x1, x2, x3) \
  (_MM_SHUFFLE(x0, x1, x2, x3))

#define Lib_Vec128_vec128_load_le(x0) \
  (_mm_loadu_si128((__m128i*)(x0)))

#define Lib_Vec128_vec128_store_le(x0, x1) \
  (_mm_storeu_si128((__m128i*)(x0), x1))

#define Lib_Vec128_vec128_load_be(x0)		\
  (_mm_shuffle_epi8(_mm_loadu_si128((__m128i*)(x0)), _mm_set_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)))

#define Lib_Vec128_vec128_store_be(x0, x1)	\
  (_mm_storeu_si128((__m128i*)(x0), _mm_shuffle_epi8(x1, _mm_set_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15))))

#define Lib_Vec128_vec128_insert32(x0, x1, x2)	\
  (_mm_insert_epi32(x0, x1, x2))

#define Lib_Vec128_vec128_zero  \
  (_mm_set1_epi16((uint16_t)0))

#define Lib_Vec128_bit_mask64(x) -((x) & 1)

#define Lib_Vec128_vec128_add64(x0, x1) \
  (_mm_add_epi64(x0, x1))

#define Lib_Vec128_vec128_sub64(x0, x1)		\
  (_mm_sub_epi64(x0, x1))

#define Lib_Vec128_vec128_mul64(x0, x1) \
  (_mm_mul_epu32(x0, x1))

#define Lib_Vec128_vec128_smul64(x0, x1) \
  (_mm_mul_epu32(x0, _mm_set1_epi64x(x1)))

#define Lib_Vec128_vec128_load64s(x1, x2) \
  (_mm_set_epi64x(x1, x2)) // hi lo

#define Lib_Vec128_vec128_load64(x) \
  (_mm_set1_epi64x(x)) // hi lo


#define Lib_Vec128_vec128_interleave_low64(x1, x2) \
  (_mm_unpacklo_epi64(x1, x2)) 

#define Lib_Vec128_vec128_interleave_high64(x1, x2) \
  (_mm_unpackhi_epi64(x1, x2)) 

#endif
