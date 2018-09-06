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

#define Lib_Vec128_vec128_xor(x0, x1) \
  (_mm_xor_si128(x0, x1))

#define Lib_Vec128_vec128_shift_left(x0, x1) \
  (_mm_slli_si128(x0, x1/8))

#define Lib_Vec128_vec128_shuffle32(x0, x1) \
  (_mm_shuffle_epi32(x0, x1))

#define Lib_Vec128_vec128_shuffle32_spec(x0, x1, x2, x3) \
  (_MM_SHUFFLE(x0, x1, x2, x3))

#define Lib_Vec128_vec128_load_le(x0) \
  (_mm_loadu_si128((__m128i*)(x0)))

#define Lib_Vec128_vec128_store_le(x0, x1) \
  (_mm_storeu_si128((__m128i*)(x0), x1))

#define Lib_Vec128_vec128_insert32(x0, x1, x2) \
  (_mm_insert_epi32(x0, x1, x2))

#define Lib_Vec128_vec128_zero  \
  (_mm_set1_epi16((uint16_t)0))

#endif
