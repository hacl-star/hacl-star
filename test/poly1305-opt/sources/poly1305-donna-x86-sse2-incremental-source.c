#include <stdint.h>
#include <x86intrin.h>

typedef __m128i xmmi;

enum poly1305_state_flags_t {
	poly1305_started = 1,
	poly1305_final_shift8 = 4,
	poly1305_final_shift16 = 8,
	poly1305_final_r2_r = 16, /* use [r^2,r] for the final block */
	poly1305_final_r_1 = 32, /* use [r,1] for the final block */
};

typedef struct poly1305_state_internal_t {
	union {
		uint32_t h[5];
		uint32_t hh[10];
	};                       /*  40 bytes  */
	uint32_t R[5];           /*  20 bytes  */
	uint32_t R2[5];          /*  20 bytes  */
	uint32_t R4[5];          /*  20 bytes  */
	uint32_t pad[4];         /*  16 bytes  */
	uint32_t flags;          /*   4 bytes  */
} poly1305_state_internal;   /* 124 bytes total */

typedef uint8_t poly1305_state[128];

#if defined(__AVX__)
#define FN(name) name##_avx
#else
#define FN(name) name##_sse2
#endif

size_t
FN(poly1305_block_size)(void) {
	return 32;
}

/* copy 0-31 bytes */
inline __attribute__((always_inline)) static void
poly1305_block_copy31(uint8_t *dst, const uint8_t *src, size_t bytes) {
	size_t offset = src - dst;
	if (bytes & 16) { _mm_store_si128((xmmi *)dst, _mm_loadu_si128((xmmi *)(dst + offset))); dst += 16; }
	if (bytes &  8) { *(uint64_t *)dst = *(uint64_t *)(dst + offset); dst += 8; }
	if (bytes &  4) { *(uint32_t *)dst = *(uint32_t *)(dst + offset); dst += 4; }
	if (bytes &  2) { *(uint16_t *)dst = *(uint16_t *)(dst + offset); dst += 2; }
	if (bytes &  1) { *( uint8_t *)dst = *( uint8_t *)(dst + offset);           }
}

__attribute__((noinline)) void
FN(poly1305_init_ext)(poly1305_state_internal *st, const unsigned char key[32], size_t bytes) {
	uint32_t *R;
	uint32_t t0,t1,t2,t3;
	uint32_t r0,r1,r2,r3,r4;
	uint32_t s1,s2,s3,s4;
	uint32_t b;
	uint64_t t[5];
	size_t i;

	if (!bytes) bytes = ~(size_t)0;

	/* H = 0 */
	_mm_storeu_si128((xmmi *)&st->hh[0], _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)&st->hh[4], _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)&st->hh[8], _mm_setzero_si128());

	/* clamp key */
	t0 = *(uint32_t *)(key + 0);
	t1 = *(uint32_t *)(key + 4);
	t2 = *(uint32_t *)(key + 8);
	t3 = *(uint32_t *)(key + 12);
	r0 = t0 & 0x3ffffff; t0 >>= 26; t0 |= t1 << 6;
	r1 = t0 & 0x3ffff03; t1 >>= 20; t1 |= t2 << 12;
	r2 = t1 & 0x3ffc0ff; t2 >>= 14; t2 |= t3 << 18;
	r3 = t2 & 0x3f03fff; t3 >>= 8;
	r4 = t3 & 0x00fffff;

	/* r^1 */
	R = st->R;
	R[0] = r0;
	R[1] = r1;
	R[2] = r2;
	R[3] = r3;
	R[4] = r4;

	/* save pad */
	st->pad[0] = *(uint32_t *)(key + 16);
	st->pad[1] = *(uint32_t *)(key + 20);
	st->pad[2] = *(uint32_t *)(key + 24);
	st->pad[3] = *(uint32_t *)(key + 28);

	/* r^2, r^4 */
	for (i = 0; i < 2; i++) {
		if (i == 0) {
			R = st->R2;
			if (bytes <= 16)
				break;
		} else if (i == 1) {
			R = st->R4;
			if (bytes < 96)
				break;
		}

		s1 = r1 * 5;
		s2 = r2 * 5;
		s3 = r3 * 5;
		s4 = r4 * 5;

		t[0]  = ((uint64_t)(r0) * (r0  )) + ((uint64_t)(r2*2) * (s3)) + ((uint64_t)(r4*2) * (s1));
		t[1]  = ((uint64_t)(r0) * (r1*2)) + ((uint64_t)(r4*2) * (s2)) + ((uint64_t)(r3  ) * (s3));
		t[2]  = ((uint64_t)(r1) * (r1  )) + ((uint64_t)(r0*2) * (r2)) + ((uint64_t)(r4*2) * (s3));
		t[3]  = ((uint64_t)(r0) * (r3*2)) + ((uint64_t)(r1*2) * (r2)) + ((uint64_t)(r4  ) * (s4));
		t[4]  = ((uint64_t)(r2) * (r2  )) + ((uint64_t)(r0*2) * (r4)) + ((uint64_t)(r3*2) * (r1));

						r0 = (uint32_t)t[0] & 0x3ffffff; b = (uint32_t)(t[0] >> 26);
		t[1] += b;      r1 = (uint32_t)t[1] & 0x3ffffff; b = (uint32_t)(t[1] >> 26);
		t[2] += b;      r2 = (uint32_t)t[2] & 0x3ffffff; b = (uint32_t)(t[2] >> 26);
		t[3] += b;      r3 = (uint32_t)t[3] & 0x3ffffff; b = (uint32_t)(t[3] >> 26);
		t[4] += b;      r4 = (uint32_t)t[4] & 0x3ffffff; b = (uint32_t)(t[4] >> 26);
		r0 += b * 5;   b = (r0 >> 26); r0 &= 0x3ffffff;
		r1 += b;

		R[0] = r0;
		R[1] = r1;
		R[2] = r2;
		R[3] = r3;
		R[4] = r4;
	}

	st->flags = 0;
}

__attribute__((noinline)) void
FN(poly1305_blocks)(poly1305_state_internal *st, const uint8_t *m, size_t bytes) {
	__attribute__((aligned(64))) xmmi HIBIT = _mm_shuffle_epi32(_mm_cvtsi32_si128(1 << 24), _MM_SHUFFLE(1,0,1,0));
	const xmmi MMASK = _mm_shuffle_epi32(_mm_cvtsi32_si128((1 << 26) - 1), _MM_SHUFFLE(1,0,1,0));
	const xmmi FIVE = _mm_shuffle_epi32(_mm_cvtsi32_si128(5), _MM_SHUFFLE(1,0,1,0));

	xmmi H0,H1,H2,H3,H4;
	xmmi T0,T1,T2,T3,T4,T5,T6,T7,T8;
	xmmi M0,M1,M2,M3,M4;
	xmmi M5,M6,M7,M8,M9;
	xmmi C1,C2;
	xmmi R20,R21,R22,R23,R24,S21,S22,S23,S24;
	xmmi R40,R41,R42,R43,R44,S41,S42,S43,S44;

	if (st->flags & poly1305_final_shift8) HIBIT = _mm_srli_si128(HIBIT, 8);
	if (st->flags & poly1305_final_shift16) HIBIT = _mm_setzero_si128();

	if (!(st->flags & poly1305_started)) {
		/* H = [Mx,My] */
		T5 = _mm_unpacklo_epi64(_mm_loadl_epi64((xmmi *)(m + 0)), _mm_loadl_epi64((xmmi *)(m + 16)));
		T6 = _mm_unpacklo_epi64(_mm_loadl_epi64((xmmi *)(m + 8)), _mm_loadl_epi64((xmmi *)(m + 24)));
		H0 = _mm_and_si128(MMASK, T5);
		H1 = _mm_and_si128(MMASK, _mm_srli_epi64(T5, 26));
		T5 = _mm_or_si128(_mm_srli_epi64(T5, 52), _mm_slli_epi64(T6, 12));
		H2 = _mm_and_si128(MMASK, T5);
		H3 = _mm_and_si128(MMASK, _mm_srli_epi64(T5, 26));
		H4 = _mm_srli_epi64(T6, 40); 
		H4 = _mm_or_si128(H4, HIBIT);
		m += 32;
		bytes -= 32;
		st->flags |= poly1305_started;
	} else {
		T0 = _mm_loadu_si128((xmmi *)&st->hh[0]);
		T1 = _mm_loadu_si128((xmmi *)&st->hh[4]);
		T2 = _mm_loadu_si128((xmmi *)&st->hh[8]);
		H0 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(1,1,0,0));
		H1 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(3,3,2,2));
		H2 = _mm_shuffle_epi32(T1, _MM_SHUFFLE(1,1,0,0));
		H3 = _mm_shuffle_epi32(T1, _MM_SHUFFLE(3,3,2,2));
		H4 = _mm_shuffle_epi32(T2, _MM_SHUFFLE(1,1,0,0));
	}

	if (st->flags & (poly1305_final_r2_r|poly1305_final_r_1)) {
		if (st->flags & poly1305_final_r2_r) {
			/* use [r^2, r] */
			T2 = _mm_loadu_si128((xmmi *)&st->R[0]);
			T3 = _mm_cvtsi32_si128(st->R[4]);
			T0 = _mm_loadu_si128((xmmi *)&st->R2[0]);
			T1 = _mm_cvtsi32_si128(st->R2[4]);
			T4 = _mm_unpacklo_epi32(T0, T2);
			T5 = _mm_unpackhi_epi32(T0, T2);
			R24 = _mm_unpacklo_epi64(T1, T3);
		} else {
			/* use [r, 1] */
			T0 = _mm_loadu_si128((xmmi *)&st->R[0]);
			T1 = _mm_cvtsi32_si128(st->R[4]);
			T2 = _mm_cvtsi32_si128(1);
			T4 = _mm_unpacklo_epi32(T0, T2);
			T5 = _mm_unpackhi_epi32(T0, T2);
			R24 = T1;
		}

		R20 = _mm_shuffle_epi32(T4, _MM_SHUFFLE(1,1,0,0));
		R21 = _mm_shuffle_epi32(T4, _MM_SHUFFLE(3,3,2,2));
		R22 = _mm_shuffle_epi32(T5, _MM_SHUFFLE(1,1,0,0));
		R23 = _mm_shuffle_epi32(T5, _MM_SHUFFLE(3,3,2,2));
	} else {
		/* use [r^2, r^2] */
		T0 = _mm_loadu_si128((xmmi *)&st->R2[0]);
		T1 = _mm_cvtsi32_si128(st->R2[4]);
		R20 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(0,0,0,0));
		R21 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(1,1,1,1));
		R22 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(2,2,2,2));
		R23 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(3,3,3,3));
		R24 = _mm_shuffle_epi32(T1, _MM_SHUFFLE(0,0,0,0));
	}
	S21 = _mm_mul_epu32(R21, FIVE);
	S22 = _mm_mul_epu32(R22, FIVE);
	S23 = _mm_mul_epu32(R23, FIVE);
	S24 = _mm_mul_epu32(R24, FIVE);

	if (bytes >= 64) {
		T0 = _mm_loadu_si128((xmmi *)&st->R4[0]);
		T1 = _mm_cvtsi32_si128(st->R4[4]);
		R40 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(0,0,0,0));
		R41 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(1,1,1,1));
		R42 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(2,2,2,2));
		R43 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(3,3,3,3));
		R44 = _mm_shuffle_epi32(T1, _MM_SHUFFLE(0,0,0,0));
		S41 = _mm_mul_epu32(R41, FIVE);
		S42 = _mm_mul_epu32(R42, FIVE);
		S43 = _mm_mul_epu32(R43, FIVE);
		S44 = _mm_mul_epu32(R44, FIVE);

		while (bytes >= 64) {
			xmmi v00,v01,v02,v03,v04;
			xmmi v10,v11,v12,v13,v14;
			xmmi v20,v21,v22,v23,v24;
			xmmi v30,v31,v32,v33,v34;
			xmmi v40,v41,v42,v43,v44;
			xmmi T14,T15;

			/* H *= [r^4,r^4], preload [Mx,My] */
			T15 = S42;
			T0  = H4; T0  = _mm_mul_epu32(T0, S41);
			v01 = H3; v01 = _mm_mul_epu32(v01, T15);
			T14 = S43;
			T1  = H4; T1  = _mm_mul_epu32(T1 , T15);
			v11 = H3; v11 = _mm_mul_epu32(v11, T14);
			T2  = H4; T2  = _mm_mul_epu32(T2 , T14); T0 = _mm_add_epi64(T0, v01);
			T15 = S44;
			v02 = H2; v02 = _mm_mul_epu32(v02, T14);
			T3  = H4; T3  = _mm_mul_epu32(T3 , T15); T1 = _mm_add_epi64(T1, v11);
			v03 = H1; v03 = _mm_mul_epu32(v03, T15);
			v12 = H2; v12 = _mm_mul_epu32(v12, T15); T0 = _mm_add_epi64(T0, v02);
			T14 = R40;
			v21 = H3; v21 = _mm_mul_epu32(v21, T15);
			v31 = H3; v31 = _mm_mul_epu32(v31, T14); T0 = _mm_add_epi64(T0, v03);
			T4  = H4; T4  = _mm_mul_epu32(T4 , T14); T1 = _mm_add_epi64(T1, v12);
			v04 = H0; v04 = _mm_mul_epu32(v04, T14); T2 = _mm_add_epi64(T2, v21);
			v13 = H1; v13 = _mm_mul_epu32(v13, T14); T3 = _mm_add_epi64(T3, v31);
			T15 = R41;
			v22 = H2; v22 = _mm_mul_epu32(v22, T14);
			v32 = H2; v32 = _mm_mul_epu32(v32, T15); T0 = _mm_add_epi64(T0, v04);
			v41 = H3; v41 = _mm_mul_epu32(v41, T15); T1 = _mm_add_epi64(T1, v13);
			v14 = H0; v14 = _mm_mul_epu32(v14, T15); T2 = _mm_add_epi64(T2, v22);
			T14 = R42;
			v23 = H1; v23 = _mm_mul_epu32(v23, T15); T3 = _mm_add_epi64(T3, v32);
			v33 = H1; v33 = _mm_mul_epu32(v33, T14); T4 = _mm_add_epi64(T4, v41);
			v42 = H2; v42 = _mm_mul_epu32(v42, T14); T1 = _mm_add_epi64(T1, v14);
			T15 = R43;
			v24 = H0; v24 = _mm_mul_epu32(v24, T14); T2 = _mm_add_epi64(T2, v23);
			v34 = H0; v34 = _mm_mul_epu32(v34, T15); T3 = _mm_add_epi64(T3, v33);
			v43 = H1; v43 = _mm_mul_epu32(v43, T15); T4 = _mm_add_epi64(T4, v42);
			v44 = H0; v44 = _mm_mul_epu32(v44, R44); T2 = _mm_add_epi64(T2, v24);
													 T3 = _mm_add_epi64(T3, v34);
													 T4 = _mm_add_epi64(T4, v43);
													 T4 = _mm_add_epi64(T4, v44);

			T5 = _mm_unpacklo_epi64(_mm_loadl_epi64((xmmi *)(m + 0)), _mm_loadl_epi64((xmmi *)(m + 16)));
			T6 = _mm_unpacklo_epi64(_mm_loadl_epi64((xmmi *)(m + 8)), _mm_loadl_epi64((xmmi *)(m + 24)));
			M0 = _mm_and_si128(MMASK, T5);
			M1 = _mm_and_si128(MMASK, _mm_srli_epi64(T5, 26));
			T5 = _mm_or_si128(_mm_srli_epi64(T5, 52), _mm_slli_epi64(T6, 12));
			M3 = _mm_and_si128(MMASK, _mm_srli_epi64(T6, 14));
			M2 = _mm_and_si128(MMASK, T5);
			M4 = _mm_or_si128(_mm_srli_epi64(T6, 40), HIBIT);

			/* H += [Mx,My]*[r^2,r^2] */
			T15 = S22;
			v00 = M4; v00 = _mm_mul_epu32(v00, S21);
			v01 = M3; v01 = _mm_mul_epu32(v01, T15);
			T14 = S23;
			v10 = M4; v10 = _mm_mul_epu32(v10, T15);
			v11 = M3; v11 = _mm_mul_epu32(v11, T14); T0 = _mm_add_epi64(T0, v00);
			v20 = M4; v20 = _mm_mul_epu32(v20, T14); T0 = _mm_add_epi64(T0, v01);
			T15 = S24;
			v02 = M2; v02 = _mm_mul_epu32(v02, T14); T1 = _mm_add_epi64(T1, v10);
			v30 = M4; v30 = _mm_mul_epu32(v30, T15); T1 = _mm_add_epi64(T1, v11);
			v03 = M1; v03 = _mm_mul_epu32(v03, T15); T2 = _mm_add_epi64(T2, v20);
			v12 = M2; v12 = _mm_mul_epu32(v12, T15); T0 = _mm_add_epi64(T0, v02);
			T14 = R20;
			v21 = M3; v21 = _mm_mul_epu32(v21, T15); T3 = _mm_add_epi64(T3, v30);
			v31 = M3; v31 = _mm_mul_epu32(v31, T14); T0 = _mm_add_epi64(T0, v03);
			v40 = M4; v40 = _mm_mul_epu32(v40, T14); T1 = _mm_add_epi64(T1, v12);
			v04 = M0; v04 = _mm_mul_epu32(v04, T14); T2 = _mm_add_epi64(T2, v21);
			v13 = M1; v13 = _mm_mul_epu32(v13, T14); T3 = _mm_add_epi64(T3, v31);
			T15 = R21;
			v22 = M2; v22 = _mm_mul_epu32(v22, T14); T4 = _mm_add_epi64(T4, v40);
			v32 = M2; v32 = _mm_mul_epu32(v32, T15); T0 = _mm_add_epi64(T0, v04);
			v41 = M3; v41 = _mm_mul_epu32(v41, T15); T1 = _mm_add_epi64(T1, v13);
			v14 = M0; v14 = _mm_mul_epu32(v14, T15); T2 = _mm_add_epi64(T2, v22);
			T14 = R22;
			v23 = M1; v23 = _mm_mul_epu32(v23, T15); T3 = _mm_add_epi64(T3, v32);
			v33 = M1; v33 = _mm_mul_epu32(v33, T14); T4 = _mm_add_epi64(T4, v41);
			v42 = M2; v42 = _mm_mul_epu32(v42, T14); T1 = _mm_add_epi64(T1, v14);
			T15 = R23;
			v24 = M0; v24 = _mm_mul_epu32(v24, T14); T2 = _mm_add_epi64(T2, v23);
			v34 = M0; v34 = _mm_mul_epu32(v34, T15); T3 = _mm_add_epi64(T3, v33);
			v43 = M1; v43 = _mm_mul_epu32(v43, T15); T4 = _mm_add_epi64(T4, v42);
			v44 = M0; v44 = _mm_mul_epu32(v44, R24); T2 = _mm_add_epi64(T2, v24);
													 T3 = _mm_add_epi64(T3, v34);
													 T4 = _mm_add_epi64(T4, v43);
													 T4 = _mm_add_epi64(T4, v44);

			/* H += [Mx',My'] */
			T5 = _mm_loadu_si128((xmmi *)(m + 32));
			T6 = _mm_loadu_si128((xmmi *)(m + 48));
			T7 = _mm_unpacklo_epi32(T5, T6);
			T8 = _mm_unpackhi_epi32(T5, T6);
			M5 = _mm_unpacklo_epi32(T7, _mm_setzero_si128());
			M6 = _mm_unpackhi_epi32(T7, _mm_setzero_si128());
			M7 = _mm_unpacklo_epi32(T8, _mm_setzero_si128());
			M8 = _mm_unpackhi_epi32(T8, _mm_setzero_si128());
			M6 = _mm_slli_epi64(M6, 6);
			M7 = _mm_slli_epi64(M7, 12);
			M8 = _mm_slli_epi64(M8, 18);
			T0 = _mm_add_epi64(T0, M5);
			T1 = _mm_add_epi64(T1, M6);
			T2 = _mm_add_epi64(T2, M7);
			T3 = _mm_add_epi64(T3, M8);
			T4 = _mm_add_epi64(T4, HIBIT);

			/* reduce */
			C1 = _mm_srli_epi64(T0, 26); C2 = _mm_srli_epi64(T3, 26); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_and_si128(T3, MMASK); T1 = _mm_add_epi64(T1, C1); T4 = _mm_add_epi64(T4, C2); 
			C1 = _mm_srli_epi64(T1, 26); C2 = _mm_srli_epi64(T4, 26); T1 = _mm_and_si128(T1, MMASK); T4 = _mm_and_si128(T4, MMASK); T2 = _mm_add_epi64(T2, C1); T0 = _mm_add_epi64(T0, _mm_mul_epu32(C2, FIVE)); 
			C1 = _mm_srli_epi64(T2, 26); C2 = _mm_srli_epi64(T0, 26); T2 = _mm_and_si128(T2, MMASK); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_add_epi64(T3, C1); T1 = _mm_add_epi64(T1, C2);
			C1 = _mm_srli_epi64(T3, 26);                              T3 = _mm_and_si128(T3, MMASK);                                T4 = _mm_add_epi64(T4, C1);
		
			/* Final: H = (H*[r^4,r^4] + [Mx,My]*[r^2,r^2] + [Mx',My']) */
			H0 = T0;
			H1 = T1;
			H2 = T2;
			H3 = T3;
			H4 = T4;

			m += 64;
			bytes -= 64;
		}
	}


	if (bytes >= 32) {
		xmmi v01,v02,v03,v04;
		xmmi v11,v12,v13,v14;
		xmmi v21,v22,v23,v24;
		xmmi v31,v32,v33,v34;
		xmmi v41,v42,v43,v44;
		xmmi T14,T15;

		/* H *= [r^2,r^2] */
		T15 = S22;
		T0  = H4; T0  = _mm_mul_epu32(T0, S21);
		v01 = H3; v01 = _mm_mul_epu32(v01, T15);
		T14 = S23;
		T1  = H4; T1  = _mm_mul_epu32(T1 , T15);
		v11 = H3; v11 = _mm_mul_epu32(v11, T14);
		T2  = H4; T2  = _mm_mul_epu32(T2 , T14); T0 = _mm_add_epi64(T0, v01);
		T15 = S24;
		v02 = H2; v02 = _mm_mul_epu32(v02, T14);
		T3  = H4; T3  = _mm_mul_epu32(T3 , T15); T1 = _mm_add_epi64(T1, v11);
		v03 = H1; v03 = _mm_mul_epu32(v03, T15);
		v12 = H2; v12 = _mm_mul_epu32(v12, T15); T0 = _mm_add_epi64(T0, v02);
		T14 = R20;
		v21 = H3; v21 = _mm_mul_epu32(v21, T15);
		v31 = H3; v31 = _mm_mul_epu32(v31, T14); T0 = _mm_add_epi64(T0, v03);
		T4  = H4; T4  = _mm_mul_epu32(T4 , T14); T1 = _mm_add_epi64(T1, v12);
		v04 = H0; v04 = _mm_mul_epu32(v04, T14); T2 = _mm_add_epi64(T2, v21);
		v13 = H1; v13 = _mm_mul_epu32(v13, T14); T3 = _mm_add_epi64(T3, v31);
		T15 = R21;
		v22 = H2; v22 = _mm_mul_epu32(v22, T14);
		v32 = H2; v32 = _mm_mul_epu32(v32, T15); T0 = _mm_add_epi64(T0, v04);
		v41 = H3; v41 = _mm_mul_epu32(v41, T15); T1 = _mm_add_epi64(T1, v13);
		v14 = H0; v14 = _mm_mul_epu32(v14, T15); T2 = _mm_add_epi64(T2, v22);
		T14 = R22;
		v23 = H1; v23 = _mm_mul_epu32(v23, T15); T3 = _mm_add_epi64(T3, v32);
		v33 = H1; v33 = _mm_mul_epu32(v33, T14); T4 = _mm_add_epi64(T4, v41);
		v42 = H2; v42 = _mm_mul_epu32(v42, T14); T1 = _mm_add_epi64(T1, v14);
		T15 = R23;
		v24 = H0; v24 = _mm_mul_epu32(v24, T14); T2 = _mm_add_epi64(T2, v23);
		v34 = H0; v34 = _mm_mul_epu32(v34, T15); T3 = _mm_add_epi64(T3, v33);
		v43 = H1; v43 = _mm_mul_epu32(v43, T15); T4 = _mm_add_epi64(T4, v42);
		v44 = H0; v44 = _mm_mul_epu32(v44, R24); T2 = _mm_add_epi64(T2, v24);
		                                         T3 = _mm_add_epi64(T3, v34);
		                                         T4 = _mm_add_epi64(T4, v43);
		                                         T4 = _mm_add_epi64(T4, v44);
		
		/* H += [Mx,My] */
		if (m) {
			T5 = _mm_loadu_si128((xmmi *)(m + 0));
			T6 = _mm_loadu_si128((xmmi *)(m + 16));
			T7 = _mm_unpacklo_epi32(T5, T6);
			T8 = _mm_unpackhi_epi32(T5, T6);
			M0 = _mm_unpacklo_epi32(T7, _mm_setzero_si128());
			M1 = _mm_unpackhi_epi32(T7, _mm_setzero_si128());
			M2 = _mm_unpacklo_epi32(T8, _mm_setzero_si128());
			M3 = _mm_unpackhi_epi32(T8, _mm_setzero_si128());
			M1 = _mm_slli_epi64(M1, 6);
			M2 = _mm_slli_epi64(M2, 12);
			M3 = _mm_slli_epi64(M3, 18);
			T0 = _mm_add_epi64(T0, M0);
			T1 = _mm_add_epi64(T1, M1);
			T2 = _mm_add_epi64(T2, M2);
			T3 = _mm_add_epi64(T3, M3);
			T4 = _mm_add_epi64(T4, HIBIT);
		}

		/* reduce */
		C1 = _mm_srli_epi64(T0, 26); C2 = _mm_srli_epi64(T3, 26); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_and_si128(T3, MMASK); T1 = _mm_add_epi64(T1, C1); T4 = _mm_add_epi64(T4, C2); 
		C1 = _mm_srli_epi64(T1, 26); C2 = _mm_srli_epi64(T4, 26); T1 = _mm_and_si128(T1, MMASK); T4 = _mm_and_si128(T4, MMASK); T2 = _mm_add_epi64(T2, C1); T0 = _mm_add_epi64(T0, _mm_mul_epu32(C2, FIVE)); 
		C1 = _mm_srli_epi64(T2, 26); C2 = _mm_srli_epi64(T0, 26); T2 = _mm_and_si128(T2, MMASK); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_add_epi64(T3, C1); T1 = _mm_add_epi64(T1, C2);
		C1 = _mm_srli_epi64(T3, 26);                              T3 = _mm_and_si128(T3, MMASK);                                T4 = _mm_add_epi64(T4, C1);
		
		/* H = (H*[r^2,r^2] + [Mx,My]) */
		H0 = T0;
		H1 = T1;
		H2 = T2;
		H3 = T3;
		H4 = T4;
	}

	if (m) {
		T0 = _mm_shuffle_epi32(H0, _MM_SHUFFLE(0,0,2,0));
		T1 = _mm_shuffle_epi32(H1, _MM_SHUFFLE(0,0,2,0));
		T2 = _mm_shuffle_epi32(H2, _MM_SHUFFLE(0,0,2,0));
		T3 = _mm_shuffle_epi32(H3, _MM_SHUFFLE(0,0,2,0));
		T4 = _mm_shuffle_epi32(H4, _MM_SHUFFLE(0,0,2,0));
		T0 = _mm_unpacklo_epi64(T0, T1);
		T1 = _mm_unpacklo_epi64(T2, T3);
		_mm_storeu_si128((xmmi *)&st->hh[0], T0);
		_mm_storeu_si128((xmmi *)&st->hh[4], T1);
		_mm_storel_epi64((xmmi *)&st->hh[8], T4);
	} else {
		uint32_t t0,t1,t2,t3,t4;
		uint32_t g0,g1,g2,g3,g4,c,nc;
		uint32_t f0,f1,f2,f3;

		/* H = H[0]+H[1] */
		T0 = H0;
		T1 = H1;
		T2 = H2;
		T3 = H3;
		T4 = H4;

		T0 = _mm_add_epi64(T0, _mm_srli_si128(T0, 8));
		T1 = _mm_add_epi64(T1, _mm_srli_si128(T1, 8));
		T2 = _mm_add_epi64(T2, _mm_srli_si128(T2, 8));
		T3 = _mm_add_epi64(T3, _mm_srli_si128(T3, 8));
		T4 = _mm_add_epi64(T4, _mm_srli_si128(T4, 8));

		t0 = _mm_cvtsi128_si32(T0)    ; c = (t0 >> 26); t0 &= 0x3ffffff;
		t1 = _mm_cvtsi128_si32(T1) + c; c = (t1 >> 26); t1 &= 0x3ffffff;
		t2 = _mm_cvtsi128_si32(T2) + c; c = (t2 >> 26); t2 &= 0x3ffffff;
		t3 = _mm_cvtsi128_si32(T3) + c; c = (t3 >> 26); t3 &= 0x3ffffff;
		t4 = _mm_cvtsi128_si32(T4) + c; c = (t4 >> 26); t4 &= 0x3ffffff;
		t0 = t0 + (c * 5)             ; c = (t0 >> 26); t0 &= 0x3ffffff;
		t1 = t1 + c                   ; c = (t1 >> 26); t1 &= 0x3ffffff;
		t2 = t2 + c                   ; c = (t2 >> 26); t2 &= 0x3ffffff;
		t3 = t3 + c                   ; c = (t3 >> 26); t3 &= 0x3ffffff;
		t4 = t4 + c                   ; c = (t4 >> 26); t4 &= 0x3ffffff;
		t0 = t0 + (c * 5)             ; c = (t0 >> 26); t0 &= 0x3ffffff;
		t1 = t1 + c                   ;

		g0 = t0 + 5; c = g0 >> 26; g0 &= 0x3ffffff;
		g1 = t1 + c; c = g1 >> 26; g1 &= 0x3ffffff;
		g2 = t2 + c; c = g2 >> 26; g2 &= 0x3ffffff;
		g3 = t3 + c; c = g3 >> 26; g3 &= 0x3ffffff;
		g4 = t4 + c - (1 << 26);

		c = (g4 >> 31) - 1;
		nc = ~c;
		t0 = (t0 & nc) | (g0 & c);
		t1 = (t1 & nc) | (g1 & c);
		t2 = (t2 & nc) | (g2 & c);
		t3 = (t3 & nc) | (g3 & c);
		t4 = (t4 & nc) | (g4 & c);

		st->h[0] = t0;
		st->h[1] = t1;
		st->h[2] = t2;
		st->h[3] = t3;
		st->h[4] = t4;
	}
}

__attribute__((noinline)) void
FN(poly1305_finish_ext)(poly1305_state_internal *st, const uint8_t *m, size_t leftover, unsigned char mac[16]) {
	uint32_t h0,h1,h2,h3,h4;
	uint32_t t0,t1;

	if (leftover) {
		__attribute__((aligned(16))) unsigned char final[32] = {0};
		poly1305_block_copy31(final, m, leftover);
		if (leftover != 16) final[leftover] = 1;
		st->flags |= (leftover >= 16) ? poly1305_final_shift8 : poly1305_final_shift16;
		FN(poly1305_blocks)(st, final, 32);
	}

	if (st->flags & poly1305_started) {
		/* finalize, H *= [r^2,r], or H *= [r,1] */
		if (!leftover || (leftover > 16))
			st->flags |= poly1305_final_r2_r;
		else
			st->flags |= poly1305_final_r_1;
		FN(poly1305_blocks)(st, NULL, 32);
	}

	h0 = st->h[0];
	h1 = st->h[1];
	h2 = st->h[2];
	h3 = st->h[3];
	h4 = st->h[4];

	h0 = ((h0      ) | (h1 << 26));
	h1 = ((h1 >>  6) | (h2 << 20));
	h2 = ((h2 >> 12) | (h3 << 14));
	h3 = ((h3 >> 18) | (h4 <<  8));

	__asm__ __volatile__(
		"addl %4, %0;\n"
		"adcl %5, %1;\n"
		"adcl %6, %2;\n"
		"adcl %7, %3;\n"
		: "+r"(h0), "+r"(h1), "+r"(h2), "+r"(h3)
		: "rm"(st->pad[0]), "rm"(st->pad[1]), "rm"(st->pad[2]), "rm"(st->pad[3])
		: "flags", "cc"
	);

	_mm_storeu_si128((xmmi *)st + 0, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 1, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 2, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 3, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 4, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 5, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 6, _mm_setzero_si128());
	_mm_storeu_si128((xmmi *)st + 7, _mm_setzero_si128());

	*(uint32_t *)(mac + 0) = h0;
	*(uint32_t *)(mac + 4) = h1;
	*(uint32_t *)(mac + 8) = h2;
	*(uint32_t *)(mac + 12) = h3;
}

void
FN(poly1305_auth)(unsigned char out[16], const unsigned char *m, size_t inlen, const unsigned char key[32]) {
	__attribute__((aligned(64))) poly1305_state S;
	poly1305_state_internal *st = (poly1305_state_internal *)S;
	size_t blocks;
	FN(poly1305_init_ext)(st, key, inlen);
	blocks = inlen & ~31;
	if (blocks) {
		FN(poly1305_blocks)(st, m, blocks);
		m += blocks;
		inlen -= blocks;
	}
	FN(poly1305_finish_ext)(st, m, inlen, out);
}

