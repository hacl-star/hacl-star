/* icc -O3 */

#include <stdint.h>
#include <x86intrin.h>

typedef __m128i xmmi;
typedef __m256i ymmi;

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
		uint32_t h[5];
		uint32_t hh[20];
	};                       /*  80 bytes  */
	uint32_t R[5];           /*  20 bytes  */
	uint32_t R2[5];          /*  20 bytes  */
	uint32_t R3[5];          /*  20 bytes  */
	uint32_t R4[5];          /*  20 bytes  */
	uint32_t pad[4];         /*  16 bytes  */
	uint32_t flags;          /*   4 bytes  */
} poly1305_state_internal;   /* 180 bytes total */

typedef uint8_t poly1305_state[192];

#if defined(__AVX2__)
#define FN(name) name##_avx2
#else
#endif

size_t
FN(poly1305_block_size)(void) {
	return 64;
}

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

__attribute__((noinline)) void
FN(poly1305_init_ext)(poly1305_state_internal *st, const unsigned char key[32], size_t bytes) {
	uint32_t *R;
	uint32_t t0,t1,t2,t3;
	uint32_t r0,r1,r2,r3,r4;
	uint32_t s1,s2,s3,s4;
	uint32_t r20,r21,r22,r23,r24;
	uint32_t s21,s22,s23,s24;
	uint32_t b;
	uint64_t t[5];
	size_t i;

	if (!bytes) bytes = ~(size_t)0;

	/* H = 0 */
	_mm256_storeu_si256((ymmi *)&st->hh[0], _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)&st->hh[8], _mm256_setzero_si256());
	_mm_storeu_si128((xmmi *)&st->hh[16], _mm_setzero_si128());

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

	if (bytes > 16) {
		const xmmi FIVE = _mm_shuffle_epi32(_mm_cvtsi32_si128(5), _MM_SHUFFLE(1,0,1,0));
		const xmmi MMASK = _mm_shuffle_epi32(_mm_cvtsi32_si128((1 << 26) - 1), _MM_SHUFFLE(1,0,1,0));

		xmmi R40,R41,R42,R43,R44;
		xmmi R20,R21,R22,R23,R24;
		xmmi S21,S22,S23,S24;
		xmmi S41,S42,S43,S44;
		xmmi T0,T1,T2,T3,T4;
		xmmi F0,F1,F2,F3,F4,F5;

		xmmi v01,v02,v03,v04;
		xmmi v11,v12,v13,v14;
		xmmi v21,v22,v23,v24;
		xmmi v31,v32,v33,v34;
		xmmi v41,v42,v43,v44;
		xmmi T14,T15;
		xmmi C1,C2;

		T0 = _mm_loadu_si128((xmmi *)&st->R[0]); /*  R3  R2  R1  R0 */
		T1 = _mm_cvtsi32_si128(st->R[4]);        /*  xx  xx  xx  R4 */
		T2 = _mm_setzero_si128();
		T3 = _mm_setzero_si128();

		R20 = _mm_unpacklo_epi64(T0, T2);        /* R21 R20  R1  R0 */
		R22 = _mm_unpackhi_epi64(T0, T2);        /* R23 R22  R3  R2 */
		R24 = _mm_unpacklo_epi64(T1, T3);        /*  xx  xx R24  R4 */
		R21 = _mm_srli_epi64(R20, 32);
		R23 = _mm_srli_epi64(R22, 32);

		S21 = _mm_mul_epu32(R21, FIVE);
		S22 = _mm_mul_epu32(R22, FIVE);
		S23 = _mm_mul_epu32(R23, FIVE);
		S24 = _mm_mul_epu32(R24, FIVE);

		v02 = _mm_mul_epu32(_mm_add_epi32(R22, R22), S23);
		v13 = _mm_mul_epu32(R23, S23);
		v23 = _mm_mul_epu32(_mm_add_epi32(R24, R24), S23);
		v33 = _mm_mul_epu32(R24, S24);
		v43 = _mm_mul_epu32(_mm_add_epi32(R23, R23), R21);
		T0 = v02;
		T1 = v13;
		T2 = v23;
		T3 = v33;
		T4 = v43;

		v03 = _mm_mul_epu32(_mm_add_epi32(R24, R24), S21);
		v12 = _mm_mul_epu32(_mm_add_epi32(R24, R24), S22);
		v22 = _mm_mul_epu32(_mm_add_epi32(R20, R20), R22);
		v31 = _mm_mul_epu32(_mm_add_epi32(R23, R23), R20);  T0 = _mm_add_epi64(T0, v03);
		v42 = _mm_mul_epu32(_mm_add_epi32(R20, R20), R24);  T1 = _mm_add_epi64(T1, v12);
		v01 = _mm_mul_epu32(R20, R20);                      T2 = _mm_add_epi64(T2, v22);
		v11 = _mm_mul_epu32(_mm_add_epi32(R21, R21), R20);  T3 = _mm_add_epi64(T3, v31);
		v21 = _mm_mul_epu32(R21, R21);                      T4 = _mm_add_epi64(T4, v42);
		v32 = _mm_mul_epu32(_mm_add_epi32(R21, R21), R22);  T0 = _mm_add_epi64(T0, v01);
		v41 = _mm_mul_epu32(R22, R22);                      T1 = _mm_add_epi64(T1, v11);
		                                                    T2 = _mm_add_epi64(T2, v21);
		                                                    T3 = _mm_add_epi64(T3, v32);
		                                                    T4 = _mm_add_epi64(T4, v41);

		/* reduce */
		C1 = _mm_srli_epi64(T0, 26); C2 = _mm_srli_epi64(T3, 26); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_and_si128(T3, MMASK); T1 = _mm_add_epi64(T1, C1); T4 = _mm_add_epi64(T4, C2); 
		C1 = _mm_srli_epi64(T1, 26); C2 = _mm_srli_epi64(T4, 26); T1 = _mm_and_si128(T1, MMASK); T4 = _mm_and_si128(T4, MMASK); T2 = _mm_add_epi64(T2, C1); T0 = _mm_add_epi64(T0, _mm_mul_epu32(C2, FIVE)); 
		C1 = _mm_srli_epi64(T2, 26); C2 = _mm_srli_epi64(T0, 26); T2 = _mm_and_si128(T2, MMASK); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_add_epi64(T3, C1); T1 = _mm_add_epi64(T1, C2);
		C1 = _mm_srli_epi64(T3, 26);                              T3 = _mm_and_si128(T3, MMASK);                                T4 = _mm_add_epi64(T4, C1);

		T0 = _mm_unpacklo_epi32(T0, T1);
		T2 = _mm_unpacklo_epi32(T2, T3);
		T2 = _mm_unpacklo_epi64(T0, T2);
		T3 = T4;

		/* r^2 */
		R = st->R2;
		_mm_storeu_si128((xmmi *)&R[0], T2);
		R[4] = _mm_cvtsi128_si32(T3);

		if (bytes > 32) {
			T0 = _mm_loadu_si128((xmmi *)&st->R[0]); /*  R3  R2  R1  R0 */
			T1 = _mm_cvtsi32_si128(st->R[4]);        /*  xx  xx  xx  R4 */
			R20 = _mm_unpacklo_epi64(T0, T2);        /* R21 R20  R1  R0 */
			R22 = _mm_unpackhi_epi64(T0, T2);        /* R23 R22  R3  R2 */
			R24 = _mm_unpacklo_epi64(T1, T3);        /*  xx  xx R24  R4 */
			R21 = _mm_srli_epi64(R20, 32);
			R23 = _mm_srli_epi64(R22, 32);

			R40 = _mm_shuffle_epi32(R20, _MM_SHUFFLE(3,2,3,2));
			R41 = _mm_shuffle_epi32(R21, _MM_SHUFFLE(3,2,3,2));
			R42 = _mm_shuffle_epi32(R22, _MM_SHUFFLE(3,2,3,2));
			R43 = _mm_shuffle_epi32(R23, _MM_SHUFFLE(3,2,3,2));
			R44 = _mm_shuffle_epi32(R24, _MM_SHUFFLE(3,2,3,2));
			S41 = _mm_mul_epu32(R41, FIVE);
			S42 = _mm_mul_epu32(R42, FIVE);
			S43 = _mm_mul_epu32(R43, FIVE);
			S44 = _mm_mul_epu32(R44, FIVE);

			/* [r^1,r^2] *= [r^2,r^2] = [r^3,r^4] */
			T15 = S42;
			T0  = R24; T0  = _mm_mul_epu32(T0, S41);
			v01 = R23; v01 = _mm_mul_epu32(v01, T15);
			T14 = S43;
			T1  = R24; T1  = _mm_mul_epu32(T1 , T15);
			v11 = R23; v11 = _mm_mul_epu32(v11, T14);
			T2  = R24; T2  = _mm_mul_epu32(T2 , T14); T0 = _mm_add_epi64(T0, v01);
			T15 = S44;
			v02 = R22; v02 = _mm_mul_epu32(v02, T14);
			T3  = R24; T3  = _mm_mul_epu32(T3 , T15); T1 = _mm_add_epi64(T1, v11);
			v03 = R21; v03 = _mm_mul_epu32(v03, T15);
			v12 = R22; v12 = _mm_mul_epu32(v12, T15); T0 = _mm_add_epi64(T0, v02);
			T14 = R40;
			v21 = R23; v21 = _mm_mul_epu32(v21, T15);
			v31 = R23; v31 = _mm_mul_epu32(v31, T14); T0 = _mm_add_epi64(T0, v03);
			T4  = R24; T4  = _mm_mul_epu32(T4 , T14); T1 = _mm_add_epi64(T1, v12);
			v04 = R20; v04 = _mm_mul_epu32(v04, T14); T2 = _mm_add_epi64(T2, v21);
			v13 = R21; v13 = _mm_mul_epu32(v13, T14); T3 = _mm_add_epi64(T3, v31);
			T15 = R41;
			v22 = R22; v22 = _mm_mul_epu32(v22, T14);
			v32 = R22; v32 = _mm_mul_epu32(v32, T15); T0 = _mm_add_epi64(T0, v04);
			v41 = R23; v41 = _mm_mul_epu32(v41, T15); T1 = _mm_add_epi64(T1, v13);
			v14 = R20; v14 = _mm_mul_epu32(v14, T15); T2 = _mm_add_epi64(T2, v22);
			T14 = R42;
			v23 = R21; v23 = _mm_mul_epu32(v23, T15); T3 = _mm_add_epi64(T3, v32);
			v33 = R21; v33 = _mm_mul_epu32(v33, T14); T4 = _mm_add_epi64(T4, v41);
			v42 = R22; v42 = _mm_mul_epu32(v42, T14); T1 = _mm_add_epi64(T1, v14);
			T15 = R43;
			v24 = R20; v24 = _mm_mul_epu32(v24, T14); T2 = _mm_add_epi64(T2, v23);
			v34 = R20; v34 = _mm_mul_epu32(v34, T15); T3 = _mm_add_epi64(T3, v33);
			v43 = R21; v43 = _mm_mul_epu32(v43, T15); T4 = _mm_add_epi64(T4, v42);
			v44 = R20; v44 = _mm_mul_epu32(v44, R44); T2 = _mm_add_epi64(T2, v24);
													 T3 = _mm_add_epi64(T3, v34);
													 T4 = _mm_add_epi64(T4, v43);
													 T4 = _mm_add_epi64(T4, v44);

			/* reduce */
			C1 = _mm_srli_epi64(T0, 26); C2 = _mm_srli_epi64(T3, 26); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_and_si128(T3, MMASK); T1 = _mm_add_epi64(T1, C1); T4 = _mm_add_epi64(T4, C2); 
			C1 = _mm_srli_epi64(T1, 26); C2 = _mm_srli_epi64(T4, 26); T1 = _mm_and_si128(T1, MMASK); T4 = _mm_and_si128(T4, MMASK); T2 = _mm_add_epi64(T2, C1); T0 = _mm_add_epi64(T0, _mm_mul_epu32(C2, FIVE)); 
			C1 = _mm_srli_epi64(T2, 26); C2 = _mm_srli_epi64(T0, 26); T2 = _mm_and_si128(T2, MMASK); T0 = _mm_and_si128(T0, MMASK); T3 = _mm_add_epi64(T3, C1); T1 = _mm_add_epi64(T1, C2);
			C1 = _mm_srli_epi64(T3, 26);                              T3 = _mm_and_si128(T3, MMASK);                                T4 = _mm_add_epi64(T4, C1);

			F0 = _mm_shuffle_epi32(T0, _MM_SHUFFLE(0,0,2,0)); // x x 40 30
			F1 = _mm_shuffle_epi32(T1, _MM_SHUFFLE(0,0,2,0)); // x x 41 31
			F2 = _mm_shuffle_epi32(T2, _MM_SHUFFLE(0,0,2,0)); // x x 42 32
			F3 = _mm_shuffle_epi32(T3, _MM_SHUFFLE(0,0,2,0)); // x x 43 33
			F4 = _mm_shuffle_epi32(T4, _MM_SHUFFLE(0,0,2,0)); // x x xx 34
			F5 = _mm_shuffle_epi32(T4, _MM_SHUFFLE(0,0,0,2)); // x x xx 44
			T0 = _mm_unpacklo_epi32(F0, F1); // 41 40 31 30
			T1 = _mm_unpacklo_epi32(F2, F3); // 43 42 33 32
			F0 = _mm_unpacklo_epi64(T0, T1); // 33 32 31 30
			F1 = _mm_unpackhi_epi64(T0, T1); // 43 42 41 40
			_mm_storeu_si128((xmmi *)&st->R3[0], F0);
			st->R3[4] = _mm_cvtsi128_si32(F4);
			_mm_storeu_si128((xmmi *)&st->R4[0], F1);
			st->R4[4] = _mm_cvtsi128_si32(F5);
		}
	}

	st->flags = 0;
}

__attribute__((noinline))  void
FN(poly1305_blocks)(poly1305_state_internal *st, const uint8_t *m, size_t bytes) {
	__attribute__((aligned(64))) ymmi HIBIT = _mm256_broadcastq_epi64(_mm_cvtsi32_si128(1 << 24));
	const ymmi MMASK = _mm256_broadcastq_epi64(_mm_cvtsi32_si128((1 << 26) - 1));
	const ymmi FIVE = _mm256_broadcastq_epi64(_mm_cvtsi32_si128(5));

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
		S41 = _mm256_mul_epu32(R41, FIVE);
		S42 = _mm256_mul_epu32(R42, FIVE);
		S43 = _mm256_mul_epu32(R43, FIVE);
		S44 = _mm256_mul_epu32(R44, FIVE);

		do {
			ymmi v01,v02,v03,v04;
			ymmi v11,v12,v13,v14;
			ymmi v21,v22,v23,v24;
			ymmi v31,v32,v33,v34;
			ymmi v41,v42,v43,v44;
			ymmi T14,T15;

			/* H *= [r^4,r^4] */
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
			m += 64;

			/* reduce */
			C1 = _mm256_srli_epi64(T0, 26); C2 = _mm256_srli_epi64(T3, 26); T0 = _mm256_and_si256(T0, MMASK); T3 = _mm256_and_si256(T3, MMASK); T1 = _mm256_add_epi64(T1, C1); T4 = _mm256_add_epi64(T4, C2); 
			C1 = _mm256_srli_epi64(T1, 26); C2 = _mm256_srli_epi64(T4, 26); T1 = _mm256_and_si256(T1, MMASK); T4 = _mm256_and_si256(T4, MMASK); T2 = _mm256_add_epi64(T2, C1); T0 = _mm256_add_epi64(T0, _mm256_mul_epu32(C2, FIVE)); 
			C1 = _mm256_srli_epi64(T2, 26); C2 = _mm256_srli_epi64(T0, 26); T2 = _mm256_and_si256(T2, MMASK); T0 = _mm256_and_si256(T0, MMASK); T3 = _mm256_add_epi64(T3, C1); T1 = _mm256_add_epi64(T1, C2);
			C1 = _mm256_srli_epi64(T3, 26);                                 T3 = _mm256_and_si256(T3, MMASK);                                   T4 = _mm256_add_epi64(T4, C1);
			
			/* H = (H*[r^4,r^4] + [Mx,My]) */
			H0 = T0;
			H1 = T1;
			H2 = T2;
			H3 = T3;
			H4 = T4;

			bytes -= 64;
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
		uint32_t t0,t1,t2,t3,t4;
		uint32_t g0,g1,g2,g3,g4,c,nc;
		uint32_t f0,f1,f2,f3;

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
		t0 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T0))    ; c = (t0 >> 26); t0 &= 0x3ffffff;
		t1 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T1)) + c; c = (t1 >> 26); t1 &= 0x3ffffff;
		t2 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T2)) + c; c = (t2 >> 26); t2 &= 0x3ffffff;
		t3 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T3)) + c; c = (t3 >> 26); t3 &= 0x3ffffff;
		t4 = _mm_cvtsi128_si32(_mm256_castsi256_si128(T4)) + c; c = (t4 >> 26); t4 &= 0x3ffffff;
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

	_mm256_storeu_si256((ymmi *)st + 0, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 1, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 2, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 3, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 4, _mm256_setzero_si256());
	_mm256_storeu_si256((ymmi *)st + 5, _mm256_setzero_si256());

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
	blocks = inlen & ~63;
	if (blocks) {
		FN(poly1305_blocks)(st, m, blocks);
		m += blocks;
		inlen -= blocks;
	}
	FN(poly1305_finish_ext)(st, m, inlen, out);
}
