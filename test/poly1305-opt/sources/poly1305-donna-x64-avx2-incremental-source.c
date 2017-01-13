#include <stdint.h>
#include <x86intrin.h>

typedef __m128i xmmi;
typedef __m256i ymmi;

typedef unsigned int uint128_t __attribute__((mode(TI)));

enum poly1305_state_flags_t {
	poly1305_started = 1,
	poly1305_final_shift8 = 4,
	poly1305_final_shift16 = 8,
	poly1305_final_shift24 = 16,
	poly1305_final_shift32 = 32,
	poly1305_finalize = 64,

	poly1305_final_r4_r4_r4_r3 = 128, /* use [r^4,r^4,r^4,r^3]  */
	poly1305_final_r4_r4_r3_r2 = 256, /* use [r^4,r^4,r^3,r^2]  */
	poly1305_final_r4_r3_r2_r = 512, /* use [r^4,r^3,r^2,r]  */
	poly1305_final_r3_r2_r_1 = 1024, /* use [r^3,r^2,r,1]  */
	poly1305_final_r2_r_1_1 = 2048, /* use [r^2,r,1,1]  */
	poly1305_final_r_1_1_1 = 4096 /* use [r,1,1,1] */
};

#define poly1305_shift_flags (poly1305_final_shift8|poly1305_final_shift16|poly1305_final_shift24|poly1305_final_shift32)
#define poly1305_mult_flags (poly1305_final_r4_r4_r4_r3|poly1305_final_r4_r4_r3_r2|poly1305_final_r4_r3_r2_r|poly1305_final_r3_r2_r_1|poly1305_final_r2_r_1_1|poly1305_final_r_1_1_1)

typedef struct poly1305_state_internal_t {
	union {
		uint64_t h[3];
		uint32_t hh[20];
	};                       /*  80 bytes  */
	uint32_t R[5];           /*  20 bytes  */
	uint32_t R2[5];          /*  20 bytes  */
	uint32_t R3[5];          /*  20 bytes  */
	uint32_t R4[5];          /*  20 bytes  */
	uint64_t pad[2];         /*  16 bytes  */
	uint64_t flags;          /*   8 bytes  */
} poly1305_state_internal;   /* 184 bytes total */

typedef uint8_t poly1305_state[192];

#if defined(__AVX2__)
#define FN(name) name##_avx2
#else
#endif


/* copy 0-63 bytes */
inline __attribute__((always_inline)) 
poly1305_block_copy63(uint8_t *dst, const uint8_t *src, size_t bytes) {
	size_t offset = src - dst;
	if (bytes & 32) { _mm256_store_si256((ymmi *)dst, _mm256_loadu_si256((ymmi *)(dst + offset))); dst += 32; }
	if (bytes & 16) { _mm_store_si128((xmmi *)dst, _mm_loadu_si128((xmmi *)(dst + offset))); dst += 16; }
	if (bytes &  8) { *(uint64_t *)dst = *(uint64_t *)(dst + offset); dst += 8; }
	if (bytes &  4) { *(uint32_t *)dst = *(uint32_t *)(dst + offset); dst += 4; }
	if (bytes &  2) { *(uint16_t *)dst = *(uint16_t *)(dst + offset); dst += 2; }
	if (bytes &  1) { *( uint8_t *)dst = *( uint8_t *)(dst + offset);           }
}


size_t
FN(poly1305_block_size)(void) {
	return 64;
}


__attribute__((noinline)) void
FN(poly1305_init_ext)(poly1305_state_internal *st, const unsigned char key[32], size_t bytes) {
	uint32_t *R;
	uint128_t d[3];
	uint64_t r0,r1,r2,c;
	uint64_t r20,r21,r22,s21,s22;
	uint64_t t0,t1;
	size_t i;

	if (!bytes) bytes = ~(size_t)0;

	/* H = 0 */
	_mm256_storeu_si256((ymmi *)&st->hh[0], _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)&st->hh[8], _mm256_setzero_si256());
	_mm_storeu_si128((xmmi *)&st->hh[16], _mm_setzero_si128());


	/* clamp key */
	t0 = *(uint64_t *)(key + 0);
	t1 = *(uint64_t *)(key + 8);
	r0 = t0 & 0xffc0fffffff; t0 >>= 44; t0 |= t1 << 20;
	r1 = t0 & 0xfffffc0ffff; t1 >>= 24;
	r2 = t1 & 0x00ffffffc0f;

	st->pad[0] = *(uint64_t *)(key + 16);
	st->pad[1] = *(uint64_t *)(key + 24);

	R = st->R;
	R[0] = (uint32_t)( r0                    ) & 0x3ffffff;
	R[1] = (uint32_t)((r0 >> 26) | (r1 << 18)) & 0x3ffffff;
	R[2] = (uint32_t)((r1 >> 8)              ) & 0x3ffffff;
	R[3] = (uint32_t)((r1 >> 34) | (r2 << 10)) & 0x3ffffff;
	R[4] = (uint32_t)((r2 >> 16)             );

	if (bytes > 16) {
		r20 = r0;
		r21 = r1;
		r22 = r2;
		s22 = r22 * (5 << 2);
		d[0] = ((uint128_t)r20 * r20) + ((uint128_t)(r21 * 2) * s22);
		d[1] = ((uint128_t)r22 * s22) + ((uint128_t)(r20 * 2) * r21);
		d[2] = ((uint128_t)r21 * r21) + ((uint128_t)(r22 * 2) * r20);
		              r20 = (uint64_t)d[0] & 0xfffffffffff; c = (uint64_t)(d[0] >> 44);
		d[1] += c   ; r21 = (uint64_t)d[1] & 0xfffffffffff; c = (uint64_t)(d[1] >> 44);
		d[2] += c   ; r22 = (uint64_t)d[2] & 0x3ffffffffff; c = (uint64_t)(d[2] >> 42);
		r20 += c * 5; c = (r20 >> 44); r20 = r20 & 0xfffffffffff;
		r21 += c    ; c = (r21 >> 44); r21 = r21 & 0xfffffffffff;
		r22 += c    ; /* even if r22 overflows, it will still fit in r4 safely, and is safe to multiply with */

		R = st->R2;
		R[0] = (uint32_t)( r20                     ) & 0x3ffffff;
		R[1] = (uint32_t)((r20 >> 26) | (r21 << 18)) & 0x3ffffff;
		R[2] = (uint32_t)((r21 >> 8)               ) & 0x3ffffff;
		R[3] = (uint32_t)((r21 >> 34) | (r22 << 10)) & 0x3ffffff;
		R[4] = (uint32_t)((r22 >> 16)              );
	}

	if (bytes > 48) {
		uint64_t r40,r41,r42,s42;
		r40 = r20;
		r41 = r21;
		r42 = r22;
		s42 = r42 * (5 << 2);
		d[0] = ((uint128_t)r40 * r40) + ((uint128_t)(r41 * 2) * s42);
		d[1] = ((uint128_t)r42 * s42) + ((uint128_t)(r40 * 2) * r41);
		d[2] = ((uint128_t)r41 * r41) + ((uint128_t)(r42 * 2) * r40);
		              r40 = (uint64_t)d[0] & 0xfffffffffff; c = (uint64_t)(d[0] >> 44);
		d[1] += c   ; r41 = (uint64_t)d[1] & 0xfffffffffff; c = (uint64_t)(d[1] >> 44);
		d[2] += c   ; r42 = (uint64_t)d[2] & 0x3ffffffffff; c = (uint64_t)(d[2] >> 42);
		r40 += c * 5; c = (r40 >> 44); r40 = r40 & 0xfffffffffff;
		r41 += c    ; c = (r41 >> 44); r41 = r41 & 0xfffffffffff;
		r42 += c    ; /* even if r42 overflows, it will still fit in r4 safely, and is safe to multiply with */

		R = st->R4;
		R[0] = (uint32_t)( r40                     ) & 0x3ffffff;
		R[1] = (uint32_t)((r40 >> 26) | (r41 << 18)) & 0x3ffffff;
		R[2] = (uint32_t)((r41 >> 8)               ) & 0x3ffffff;
		R[3] = (uint32_t)((r41 >> 34) | (r42 << 10)) & 0x3ffffff;
		R[4] = (uint32_t)((r42 >> 16)              );
	}

	/* r^3 */
	if (bytes > 32) {
		s21 = r21 * (5 << 2);
		s22 = r22 * (5 << 2);
		d[0] = ((uint128_t)r0 * r20) + ((uint128_t)r1 * s22) + ((uint128_t)r2 * s21);
		d[1] = ((uint128_t)r0 * r21) + ((uint128_t)r1 * r20) + ((uint128_t)r2 * s22);
		d[2] = ((uint128_t)r0 * r22) + ((uint128_t)r1 * r21) + ((uint128_t)r2 * r20);
		              r0 = (uint64_t)d[0] & 0xfffffffffff; c = (uint64_t)(d[0] >> 44);
		d[1] += c   ; r1 = (uint64_t)d[1] & 0xfffffffffff; c = (uint64_t)(d[1] >> 44);
		d[2] += c   ; r2 = (uint64_t)d[2] & 0x3ffffffffff; c = (uint64_t)(d[2] >> 42);
		r0 += c * 5; c = (r0 >> 44); r0 = r0 & 0xfffffffffff;
		r1 += c    ; c = (r1 >> 44); r1 = r1 & 0xfffffffffff;
		r2 += c    ; /* even if r2 overflows, it will still fit in r4 safely, and is safe to multiply with */

		R = st->R3;
		R[0] = (uint32_t)( r0                    ) & 0x3ffffff;
		R[1] = (uint32_t)((r0 >> 26) | (r1 << 18)) & 0x3ffffff;
		R[2] = (uint32_t)((r1 >> 8)              ) & 0x3ffffff;
		R[3] = (uint32_t)((r1 >> 34) | (r2 << 10)) & 0x3ffffff;
		R[4] = (uint32_t)((r2 >> 16)             );
	}

	st->flags = 0;
}


__attribute__((noinline))  void
FN(poly1305_blocks)(poly1305_state_internal *st, const uint8_t *m, size_t bytes) {
	__attribute__((aligned(64))) ymmi HIBIT = _mm256_broadcastq_epi64(_mm_cvtsi32_si128(1 << 24));
	const ymmi MMASK = _mm256_broadcastq_epi64(_mm_cvtsi32_si128((1 << 26) - 1));
	//const ymmi FIVE = _mm256_broadcastq_epi64(_mm_cvtsi32_si128(5));

	ymmi H0,H1,H2,H3,H4;
	ymmi T0,T1,T2,T3,T4,T5,T6,T7,T8,T9;
	ymmi M0,M1,M2,M3,M4;
	ymmi M5,M6,M7,M8,M9;
	ymmi C1,C2;
	ymmi R40,R41,R42,R43,R44,S41,S42,S43,S44;

	if (st->flags & poly1305_shift_flags) {
		T0 = _mm256_srli_si256(HIBIT, 8);
		if (st->flags & poly1305_final_shift8)  T0 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(3,0,0,0));
		if (st->flags & poly1305_final_shift16) T0 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(3,3,0,0));
		if (st->flags & poly1305_final_shift24) T0 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(3,3,3,0));
		if (st->flags & poly1305_final_shift32) T0 = _mm256_setzero_si256();
		HIBIT = T0;
	}

	if (!(st->flags & poly1305_started)) {
		/* H = [Mx,My] */
		T7 = _mm256_loadu_si256((ymmi *)(m + 0));
		T8 = _mm256_loadu_si256((ymmi *)(m + 32));
		T5 = _mm256_unpacklo_epi64(T7, T8);
		T6 = _mm256_unpackhi_epi64(T7, T8);
		T5 = _mm256_permute4x64_epi64(T5, _MM_SHUFFLE(3,1,2,0));
		T6 = _mm256_permute4x64_epi64(T6, _MM_SHUFFLE(3,1,2,0));
		H0 = _mm256_and_si256(MMASK, T5);
		H1 = _mm256_and_si256(MMASK, _mm256_srli_epi64(T5, 26));
		T5 = _mm256_or_si256(_mm256_srli_epi64(T5, 52), _mm256_slli_epi64(T6, 12));
		H2 = _mm256_and_si256(MMASK, T5);
		H3 = _mm256_and_si256(MMASK, _mm256_srli_epi64(T5, 26));
		H4 = _mm256_srli_epi64(T6, 40); 
		H4 = _mm256_or_si256(H4, HIBIT);
		m += 64;
		bytes -= 64;
		st->flags |= poly1305_started;
	} else {
		T0 = _mm256_loadu_si256((ymmi *)&st->hh[0]);
		T1 = _mm256_loadu_si256((ymmi *)&st->hh[8]);
		T2 = _mm256_loadu_si256((ymmi *)&st->hh[16]);
		T0 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(3,1,2,0));
		T1 = _mm256_permute4x64_epi64(T1, _MM_SHUFFLE(3,1,2,0));
		T2 = _mm256_permute4x64_epi64(T2, _MM_SHUFFLE(3,1,2,0));
		H0 = _mm256_unpacklo_epi32(T0, _mm256_setzero_si256());
		H1 = _mm256_unpackhi_epi32(T0, _mm256_setzero_si256());
		H2 = _mm256_unpacklo_epi32(T1, _mm256_setzero_si256());
		H3 = _mm256_unpackhi_epi32(T1, _mm256_setzero_si256());
		H4 = _mm256_unpacklo_epi32(T2, _mm256_setzero_si256());
	}

	if (bytes >= 64) {
		if (st->flags & (poly1305_final_r4_r4_r4_r3|poly1305_final_r4_r4_r3_r2|poly1305_final_r4_r3_r2_r|poly1305_final_r3_r2_r_1|poly1305_final_r2_r_1_1|poly1305_final_r_1_1_1)) {
			ymmi R0 = _mm256_castsi128_si256(_mm_cvtsi32_si128(1));
			ymmi R1 = _mm256_loadu_si256((ymmi *)&st->R[0]);
			ymmi R2 = _mm256_loadu_si256((ymmi *)&st->R2[0]);
			ymmi R3 = _mm256_loadu_si256((ymmi *)&st->R3[0]);
			ymmi R4 = _mm256_loadu_si256((ymmi *)&st->R4[0]);

			R1 = _mm256_permute4x64_epi64(R1, _MM_SHUFFLE(3,1,2,0));
			R2 = _mm256_permute4x64_epi64(R2, _MM_SHUFFLE(3,1,2,0));
			R3 = _mm256_permute4x64_epi64(R3, _MM_SHUFFLE(3,1,2,0));
			R4 = _mm256_permute4x64_epi64(R4, _MM_SHUFFLE(3,1,2,0));

			if (st->flags & poly1305_final_r4_r4_r4_r3) {
				T0 = R4;
				T1 = R4;
				T2 = R4;
				T3 = R3;
			} else if (st->flags & poly1305_final_r4_r4_r3_r2) {
				T0 = R4;
				T1 = R4;
				T2 = R3;
				T3 = R2;
			} else if (st->flags & poly1305_final_r4_r3_r2_r) {
				T0 = R4;
				T1 = R3;
				T2 = R2;
				T3 = R1;
			} else if (st->flags & poly1305_final_r3_r2_r_1) {
				T0 = R3;
				T1 = R2;
				T2 = R1;
				T3 = R0;
			} else if (st->flags & poly1305_final_r2_r_1_1) {
				T0 = R2;
				T1 = R1;
				T2 = R0;
				T3 = R0;
			} else if (st->flags & poly1305_final_r_1_1_1) {
				T0 = R1;
				T1 = R0;
				T2 = R0;
				T3 = R0;
			}

			T5 = _mm256_unpacklo_epi64(T0, T1);
			T6 = _mm256_unpackhi_epi64(T0, T1);
			T7 = _mm256_unpacklo_epi64(T2, T3);
			T8 = _mm256_unpackhi_epi64(T2, T3);
			T0 = _mm256_permute2x128_si256(T5, T7, 0x20);
			T1 = _mm256_permute2x128_si256(T5, T7, 0x31);
			T2 = _mm256_permute2x128_si256(T6, T8, 0x20);
			R40 = T0;
			R41 = _mm256_srli_epi64(T0, 32);
			R42 = T1;
			R43 = _mm256_srli_epi64(T1, 32);
			R44 = T2;
		} else {
			T0 = _mm256_loadu_si256((ymmi *)&st->R4[0]);
			T1 = _mm256_srli_epi64(T0, 32);
			R40 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(0,0,0,0));
			R41 = _mm256_permute4x64_epi64(T1, _MM_SHUFFLE(0,0,0,0));
			R42 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(1,1,1,1));
			R43 = _mm256_permute4x64_epi64(T1, _MM_SHUFFLE(1,1,1,1));
			R44 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(2,2,2,2));
		}
		S41 = _mm256_add_epi32(R41, _mm256_slli_epi32(R41, 2));
		S42 = _mm256_add_epi32(R42, _mm256_slli_epi32(R42, 2));
		S43 = _mm256_add_epi32(R43, _mm256_slli_epi32(R43, 2));
		S44 = _mm256_add_epi32(R44, _mm256_slli_epi32(R44, 2));

		do {
			ymmi v01,v02,v03,v04;
			ymmi v11,v12,v13,v14;
			ymmi v21,v22,v23,v24;
			ymmi v31,v32,v33,v34;
			ymmi v41,v42,v43,v44;
			ymmi T14,T15;

			/* H *= [r^4,r^4,r^4,r^4] */
			T15 = S42;
			T0  = H4; T0  = _mm256_mul_epu32(T0, S41);
			v01 = H3; v01 = _mm256_mul_epu32(v01, T15);
			T14 = S43;
			T1  = H4; T1  = _mm256_mul_epu32(T1 , T15);
			v11 = H3; v11 = _mm256_mul_epu32(v11, T14);
			T2  = H4; T2  = _mm256_mul_epu32(T2 , T14); T0 = _mm256_add_epi64(T0, v01);
			T15 = S44;
			v02 = H2; v02 = _mm256_mul_epu32(v02, T14);
			T3  = H4; T3  = _mm256_mul_epu32(T3 , T15); T1 = _mm256_add_epi64(T1, v11);
			v03 = H1; v03 = _mm256_mul_epu32(v03, T15);
			v12 = H2; v12 = _mm256_mul_epu32(v12, T15); T0 = _mm256_add_epi64(T0, v02);
			T14 = R40;
			v21 = H3; v21 = _mm256_mul_epu32(v21, T15);
			v31 = H3; v31 = _mm256_mul_epu32(v31, T14); T0 = _mm256_add_epi64(T0, v03);
			T4  = H4; T4  = _mm256_mul_epu32(T4 , T14); T1 = _mm256_add_epi64(T1, v12);
			v04 = H0; v04 = _mm256_mul_epu32(v04, T14); T2 = _mm256_add_epi64(T2, v21);
			v13 = H1; v13 = _mm256_mul_epu32(v13, T14); T3 = _mm256_add_epi64(T3, v31);
			T15 = R41;
			v22 = H2; v22 = _mm256_mul_epu32(v22, T14);
			v32 = H2; v32 = _mm256_mul_epu32(v32, T15); T0 = _mm256_add_epi64(T0, v04);
			v41 = H3; v41 = _mm256_mul_epu32(v41, T15); T1 = _mm256_add_epi64(T1, v13);
			v14 = H0; v14 = _mm256_mul_epu32(v14, T15); T2 = _mm256_add_epi64(T2, v22);
			T14 = R42;
			v23 = H1; v23 = _mm256_mul_epu32(v23, T15); T3 = _mm256_add_epi64(T3, v32);
			v33 = H1; v33 = _mm256_mul_epu32(v33, T14); T4 = _mm256_add_epi64(T4, v41);
			v42 = H2; v42 = _mm256_mul_epu32(v42, T14); T1 = _mm256_add_epi64(T1, v14);
			T15 = R43;
			v24 = H0; v24 = _mm256_mul_epu32(v24, T14); T2 = _mm256_add_epi64(T2, v23);
			v34 = H0; v34 = _mm256_mul_epu32(v34, T15); T3 = _mm256_add_epi64(T3, v33);
			v43 = H1; v43 = _mm256_mul_epu32(v43, T15); T4 = _mm256_add_epi64(T4, v42);
			v44 = H0; v44 = _mm256_mul_epu32(v44, R44); T2 = _mm256_add_epi64(T2, v24);
			                                            T3 = _mm256_add_epi64(T3, v34);
			                                            T4 = _mm256_add_epi64(T4, v43);
			                                            T4 = _mm256_add_epi64(T4, v44);

			/* H += [Mx,My] */
			T5 = _mm256_loadu_si256((ymmi *)(m + 0));
			T6 = _mm256_loadu_si256((ymmi *)(m + 32));
			T7 = _mm256_permute2x128_si256(T5, T6, 0x20);
			T8 = _mm256_permute2x128_si256(T5, T6, 0x31);
			T5 = _mm256_unpacklo_epi32(T7, T8);
			T6 = _mm256_unpackhi_epi32(T7, T8);
			M0 = _mm256_unpacklo_epi32(T5, _mm256_setzero_si256());
			M1 = _mm256_unpackhi_epi32(T5, _mm256_setzero_si256());
			M2 = _mm256_unpacklo_epi32(T6, _mm256_setzero_si256());
			M3 = _mm256_unpackhi_epi32(T6, _mm256_setzero_si256());
			M1 = _mm256_slli_epi64(M1, 6);
			M2 = _mm256_slli_epi64(M2, 12);
			M3 = _mm256_slli_epi64(M3, 18);
			T0 = _mm256_add_epi64(T0, M0);
			T1 = _mm256_add_epi64(T1, M1);
			T2 = _mm256_add_epi64(T2, M2);
			T3 = _mm256_add_epi64(T3, M3);
			T4 = _mm256_add_epi64(T4, HIBIT);

			/* reduce */
			C1 = _mm256_srli_epi64(T0, 26); C2 = _mm256_srli_epi64(T3, 26); T0 = _mm256_and_si256(T0, MMASK); T3 = _mm256_and_si256(T3, MMASK); T1 = _mm256_add_epi64(T1, C1); T4 = _mm256_add_epi64(T4, C2); 
			C1 = _mm256_srli_epi64(T1, 26); C2 = _mm256_srli_epi64(T4, 26); T1 = _mm256_and_si256(T1, MMASK); T4 = _mm256_and_si256(T4, MMASK); T2 = _mm256_add_epi64(T2, C1); T0 = _mm256_add_epi64(T0, _mm256_add_epi32(C2, _mm256_slli_epi32(C2, 2))); 
			C1 = _mm256_srli_epi64(T2, 26); C2 = _mm256_srli_epi64(T0, 26); T2 = _mm256_and_si256(T2, MMASK); T0 = _mm256_and_si256(T0, MMASK); T3 = _mm256_add_epi64(T3, C1); T1 = _mm256_add_epi64(T1, C2);
			C1 = _mm256_srli_epi64(T3, 26);                                 T3 = _mm256_and_si256(T3, MMASK);                                   T4 = _mm256_add_epi64(T4, C1);
			
			/* H = (H*[r^4,r^4,r^4,r^4] + [Mx,My]) */
			H0 = T0;
			H1 = T1;
			H2 = T2;
			H3 = T3;
			H4 = T4;

			bytes -= 64;
			m += 64;
		} while (bytes >= 64);
	}

	if (!(st->flags & poly1305_finalize)) {
		T0 = _mm256_shuffle_epi32(H0, _MM_SHUFFLE(0,0,2,0));
		T1 = _mm256_shuffle_epi32(H1, _MM_SHUFFLE(0,0,2,0));
		T2 = _mm256_shuffle_epi32(H2, _MM_SHUFFLE(0,0,2,0));
		T3 = _mm256_shuffle_epi32(H3, _MM_SHUFFLE(0,0,2,0));
		T4 = _mm256_shuffle_epi32(H4, _MM_SHUFFLE(0,0,2,0));
		T0 = _mm256_permute4x64_epi64(T0, _MM_SHUFFLE(0,0,2,0));
		T1 = _mm256_permute4x64_epi64(T1, _MM_SHUFFLE(0,0,2,0));
		T2 = _mm256_permute4x64_epi64(T2, _MM_SHUFFLE(0,0,2,0));
		T3 = _mm256_permute4x64_epi64(T3, _MM_SHUFFLE(0,0,2,0));
		T4 = _mm256_permute4x64_epi64(T4, _MM_SHUFFLE(0,0,2,0));
		T0 = _mm256_permute2x128_si256(T0, T1, 0x20);
		T2 = _mm256_permute2x128_si256(T2, T3, 0x20);
		_mm256_storeu_si256((ymmi *)&st->hh[0], T0);
		_mm256_storeu_si256((ymmi *)&st->hh[8], T2);
		_mm_storeu_si128((xmmi *)&st->hh[16], _mm256_castsi256_si128(T4));
	} else {
		uint32_t t0,t1,t2,t3,t4,b;
		uint64_t h0,h1,h2,g0,g1,g2,c,nc;

		/* H = H[0]+H[1] */
		T0 = H0;
		T1 = H1;
		T2 = H2;
		T3 = H3;
		T4 = H4;
		T0 = _mm256_add_epi64(T0, _mm256_permute4x64_epi64(T0, 0xf5));
		T1 = _mm256_add_epi64(T1, _mm256_permute4x64_epi64(T1, 0xf5));
		T2 = _mm256_add_epi64(T2, _mm256_permute4x64_epi64(T2, 0xf5));
		T3 = _mm256_add_epi64(T3, _mm256_permute4x64_epi64(T3, 0xf5));
		T4 = _mm256_add_epi64(T4, _mm256_permute4x64_epi64(T4, 0xf5));
		T0 = _mm256_add_epi64(T0, _mm256_permute4x64_epi64(T0, 0xaa));
		T1 = _mm256_add_epi64(T1, _mm256_permute4x64_epi64(T1, 0xaa));
		T2 = _mm256_add_epi64(T2, _mm256_permute4x64_epi64(T2, 0xaa));
		T3 = _mm256_add_epi64(T3, _mm256_permute4x64_epi64(T3, 0xaa));
		T4 = _mm256_add_epi64(T4, _mm256_permute4x64_epi64(T4, 0xaa));
		t0 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T0))    ; b = (t0 >> 26); t0 &= 0x3ffffff;
		t1 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T1)) + b; b = (t1 >> 26); t1 &= 0x3ffffff;
		t2 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T2)) + b; b = (t2 >> 26); t2 &= 0x3ffffff;
		t3 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T3)) + b; b = (t3 >> 26); t3 &= 0x3ffffff;
		t4 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T4)) + b; 

		/* everything except t4 is in range, so this is all safe */
		h0 =  (((uint64_t)t0      ) | ((uint64_t)t1 << 26)                       ) & 0xfffffffffffull;
		h1 =  (((uint64_t)t1 >> 18) | ((uint64_t)t2 <<  8) | ((uint64_t)t3 << 34)) & 0xfffffffffffull;
		h2 =  (((uint64_t)t3 >> 10) | ((uint64_t)t4 << 16)                       );

		             c = (h2 >> 42); h2 &= 0x3ffffffffff;
		h0 += c * 5; c = (h0 >> 44); h0 &= 0xfffffffffff;
		h1 += c;	 c = (h1 >> 44); h1 &= 0xfffffffffff;
		h2 += c;     c = (h2 >> 42); h2 &= 0x3ffffffffff;
		h0 += c * 5; c = (h0 >> 44); h0 &= 0xfffffffffff;
		h1 += c;

		g0 = h0 + 5; c = (g0 >> 44); g0 &= 0xfffffffffff;
		g1 = h1 + c; c = (g1 >> 44); g1 &= 0xfffffffffff;
		g2 = h2 + c - ((uint64_t)1 << 42);

		c = (g2 >> 63) - 1;
		nc = ~c;
		h0 = (h0 & nc) | (g0 & c);
		h1 = (h1 & nc) | (g1 & c);
		h2 = (h2 & nc) | (g2 & c);

		st->h[0] = h0;
		st->h[1] = h1;
		st->h[2] = h2;
	}
}

__attribute__((noinline)) void
FN(poly1305_finish_ext)(poly1305_state_internal *st, const uint8_t *m, size_t leftover, unsigned char mac[16]) {
	uint64_t h0,h1,h2;
	__attribute__((aligned(64))) unsigned char final[64];

	if (leftover) {
		_mm256_store_si256((ymmi *)(final + 0), _mm256_setzero_si256());
		_mm256_store_si256((ymmi *)(final + 32), _mm256_setzero_si256());
		poly1305_block_copy63(final, m, leftover);
		if ((leftover % 16) != 0) final[leftover] = 1;
		st->flags &= ~(poly1305_shift_flags | poly1305_mult_flags);
		if (leftover >= 48) st->flags |= poly1305_final_shift8;
		else if (leftover >= 32) st->flags |= poly1305_final_shift16;
		else if (leftover >= 16) st->flags |= poly1305_final_shift24;
		else st->flags |= poly1305_final_shift32;
		if (st->flags & poly1305_started) {
			if (leftover <= 16)
				st->flags |= poly1305_final_r4_r4_r3_r2;
			else if (leftover <= 32)
				st->flags |= poly1305_final_r4_r4_r4_r3;
		}
		FN(poly1305_blocks)(st, final, 64);
	}

	if (st->flags & poly1305_started) {
		st->flags &= ~(poly1305_shift_flags | poly1305_mult_flags);
		if (!leftover || (leftover > 48))
			st->flags |= poly1305_final_r4_r3_r2_r;
		else if (leftover > 32)
			st->flags |= poly1305_final_r3_r2_r_1;
		else if (leftover > 16)
			st->flags |= poly1305_final_r2_r_1_1;
		else
			st->flags |= poly1305_final_r_1_1_1;
		st->flags |= (poly1305_finalize|poly1305_final_shift32);
		_mm256_store_si256((ymmi *)(final + 0), _mm256_setzero_si256());
		_mm256_store_si256((ymmi *)(final + 32), _mm256_setzero_si256());
		FN(poly1305_blocks)(st, final, 64);
	}

	h0 = st->h[0];
	h1 = st->h[1];
	h2 = st->h[2];

	/* pad */
	h0 = ((h0      ) | (h1 << 44));
	h1 = ((h1 >> 20) | (h2 << 24));

	__asm__ __volatile__(
		"addq %2, %0 ;\n"
		"adcq %3, %1 ;\n"
		: "+r"(h0), "+r"(h1)
		: "r"(st->pad[0]), "r"(st->pad[1])
		: "flags", "cc"
	);

	_mm256_storeu_si256((ymmi *)st + 0, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 1, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 2, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 3, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 4, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 5, _mm256_setzero_si256());

	*(uint64_t *)(mac + 0) = h0;
	*(uint64_t *)(mac + 8) = h1;
}

void
FN(poly1305_auth)(unsigned char out[16], const unsigned char *m, size_t inlen, const unsigned char key[32]) {
	__attribute__((aligned(64))) poly1305_state S;
	poly1305_state_internal *st = (poly1305_state_internal *)S;
	size_t blocks;
	FN(poly1305_init_ext)(st, key, inlen);
	blocks = inlen & ~63;
	if (blocks) {
		FN(poly1305_blocks)(st, m, blocks);
		m += blocks;
		inlen -= blocks;
	}
	FN(poly1305_finish_ext)(st, m, inlen, out);
}


